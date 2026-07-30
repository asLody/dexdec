//! Platform symbol metadata build/inspect commands.

use std::path::{Path, PathBuf};

use crate::{
    PlatformFamily, PlatformSymbolBuilder, PlatformSymbolDatabase, PlatformTarget, SymbolArchive,
};

use super::error::{cli_err, CliResult};
use super::model::{SymbolsBuildRequest, SymbolsInspectRequest, SymbolsRequest};
use super::output::CliHost;

/// Executes platform-symbol subcommands.
pub struct SymbolsCommand;

impl SymbolsCommand {
    pub fn run(host: &mut impl CliHost, request: &SymbolsRequest) -> CliResult<()> {
        match request {
            SymbolsRequest::Build(request) => SymbolsBuild::run(host, request),
            SymbolsRequest::Inspect(request) => SymbolsInspect::run(host, request),
        }
    }
}

struct SymbolsBuild;

impl SymbolsBuild {
    fn run(host: &mut impl CliHost, request: &SymbolsBuildRequest) -> CliResult<()> {
        let base = request
            .base_database
            .as_deref()
            .map(PlatformSymbolDatabase::read)
            .transpose()?;
        let jdk_home = request.jdk_home.clone().or_else(|| {
            request
                .base_database
                .is_none()
                .then(|| std::env::var_os("JAVA_HOME").map(PathBuf::from))
                .flatten()
        });
        let java_release = match (request.java_release, jdk_home.as_deref()) {
            (Some(release), _) => Some(release),
            (None, Some(home)) => JavaRelease::from_home(host, home)?,
            (None, None) => None,
        };
        let android_sdk = request.android_sdk.clone().or_else(|| {
            if request.base_database.is_some() {
                return None;
            }
            std::env::var_os("ANDROID_HOME")
                .or_else(|| std::env::var_os("ANDROID_SDK_ROOT"))
                .map(PathBuf::from)
        });
        let android_apis = match android_sdk.as_deref() {
            Some(sdk) if request.android_apis.is_empty() => AndroidPlatforms::installed(sdk)?,
            _ => request.android_apis.clone(),
        };
        let default_target = android_apis
            .iter()
            .max()
            .copied()
            .map(PlatformTarget::android)
            .or_else(|| java_release.map(PlatformTarget::java))
            .or_else(|| base.as_ref().map(PlatformSymbolDatabase::default_target))
            .ok_or_else(|| cli_err("no JDK or Android platform inputs were configured"))?;
        let mut builder = match base {
            Some(database) => PlatformSymbolBuilder::from_database(database),
            None => PlatformSymbolBuilder::new(default_target),
        };

        if let (Some(home), Some(release)) = (jdk_home.as_deref(), java_release) {
            for module in JdkModules::selected(home, &request.jdk_modules)? {
                builder.add_archive(
                    SymbolArchive::new(
                        module,
                        format!("openjdk-{release}"),
                        PlatformFamily::Java,
                        release,
                    )
                    .with_priority(50),
                )?;
            }
        }
        for archive in &request.library_archives {
            let name = archive
                .file_stem()
                .and_then(|name| name.to_str())
                .unwrap_or("library");
            builder.add_archive(
                SymbolArchive::new(archive, name, PlatformFamily::Library, 1).with_priority(20),
            )?;
        }
        let mut external_annotations = 0usize;
        let mut constant_domains = 0usize;
        if let Some(sdk) = android_sdk.as_deref() {
            for api in android_apis {
                let platform = sdk.join("platforms").join(format!("android-{api}"));
                let jar = platform.join("android.jar");
                if !jar.is_file() {
                    return Err(cli_err(format!(
                        "Android API {api} is missing {}",
                        jar.display()
                    )));
                }
                builder.add_archive(
                    SymbolArchive::new(jar, "android-sdk", PlatformFamily::Android, api)
                        .with_priority(100),
                )?;
                let annotations = platform.join("data").join("annotations.zip");
                if annotations.is_file() {
                    let imported = builder.add_android_metadata(annotations, api)?;
                    external_annotations += imported.annotations;
                    constant_domains += imported.constant_domains;
                }
            }
        }
        let build = builder.stats();
        let database = builder.finish();
        let stats = database.stats();
        host.write(&request.output, database.to_bytes()?)?;
        host.emit(&format!(
            "wrote {}: {} archives, {} variants, {} selected classes, {} fields, {} methods, {} external annotations, {} constant domains\n",
            request.output.display(),
            build.archives,
            stats.class_variants,
            stats.selected_classes,
            stats.fields,
            stats.methods,
            external_annotations,
            constant_domains
        ))?;
        Ok(())
    }
}

struct SymbolsInspect;

impl SymbolsInspect {
    fn run(host: &mut impl CliHost, request: &SymbolsInspectRequest) -> CliResult<()> {
        let database = PlatformSymbolDatabase::read(&request.database)?;
        let stats = database.stats();
        host.emit(&format!(
            "target={:?}-{} sources={} variants={} classes={} fields={} methods={}\n",
            database.default_target().family,
            database.default_target().version,
            stats.sources,
            stats.class_variants,
            stats.selected_classes,
            stats.fields,
            stats.methods
        ))?;
        for source in database.sources() {
            host.emit(&format!(
                "source={} family={:?} priority={}\n",
                source.name, source.family, source.priority
            ))?;
        }
        Ok(())
    }
}

struct JavaRelease;

impl JavaRelease {
    fn from_home(host: &mut impl CliHost, home: &Path) -> CliResult<Option<u16>> {
        let release = home.join("release");
        if !release.is_file() {
            return Ok(None);
        }
        let contents = host.read_to_string(&release)?;
        let version = contents
            .lines()
            .find_map(|line| line.strip_prefix("JAVA_VERSION="))
            .map(|value| value.trim_matches('"'))
            .and_then(|value| value.split(['.', '-']).next())
            .and_then(|value| value.parse::<u16>().ok());
        Ok(version)
    }
}

struct JdkModules;

impl JdkModules {
    fn selected(home: &Path, selected: &[String]) -> CliResult<Vec<PathBuf>> {
        let modules = home.join("jmods");
        let mut paths = std::fs::read_dir(&modules)?
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "jmod")
            })
            .filter(|path| {
                let name = path
                    .file_stem()
                    .and_then(|name| name.to_str())
                    .unwrap_or("");
                if selected.is_empty() {
                    name.starts_with("java.")
                } else {
                    selected.iter().any(|selected| selected == name)
                }
            })
            .collect::<Vec<_>>();
        paths.sort();
        if paths.is_empty() {
            return Err(cli_err(format!(
                "no matching JDK modules found in {}",
                modules.display()
            )));
        }
        Ok(paths)
    }
}

struct AndroidPlatforms;

impl AndroidPlatforms {
    fn installed(sdk: &Path) -> CliResult<Vec<u16>> {
        let platforms = sdk.join("platforms");
        let mut apis = std::fs::read_dir(&platforms)?
            .filter_map(Result::ok)
            .filter_map(|entry| {
                entry
                    .file_name()
                    .to_str()
                    .and_then(|name| name.strip_prefix("android-"))
                    .and_then(|api| api.parse::<u16>().ok())
                    .filter(|_| entry.path().join("android.jar").is_file())
            })
            .collect::<Vec<_>>();
        apis.sort_unstable();
        apis.dedup();
        if apis.is_empty() {
            return Err(cli_err(format!(
                "no Android platforms found in {}",
                platforms.display()
            )));
        }
        Ok(apis)
    }
}
