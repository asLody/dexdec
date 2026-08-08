//! Source generation for one method, selected classes, or a complete archive.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use serde::Serialize;

use crate::{ClassSelector, DecompileOptions, Decompiler, MethodRequest, SourceLanguage};

use super::error::{CliError, CliResult};
use super::model::{DecompileRequest, ExitStatus, LanguageSelection, OutputFormat};
use super::output::{prepare_file_path, CliHost, CommandContext};
use super::resolve::ClassResolver;

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct GeneratedSource {
    class: String,
    method: Option<String>,
    descriptor: Option<String>,
    language: &'static str,
    output_path: Option<String>,
    method_count: usize,
    source: Option<String>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct GenerationFailure {
    class: String,
    error: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct DecompileReport {
    selection: &'static str,
    input: String,
    requested: usize,
    succeeded: usize,
    failed: usize,
    output_directory: Option<String>,
    results: Vec<GeneratedSource>,
    failures: Vec<GenerationFailure>,
}

pub struct DecompileCommand;

impl DecompileCommand {
    pub fn run<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &DecompileRequest,
    ) -> CliResult<ExitStatus> {
        let mut decompiler = Decompiler::open(&request.input)?;
        let catalog = decompiler.catalog();
        let classes =
            SelectionResolver::new(&catalog).resolve(context, &mut decompiler, request)?;
        Self::validate_destination(request, classes.len())?;

        let options = DecompileOptions::default().with_nested(request.include_nested);
        decompiler.set_options(options.clone());
        if let Some(method) = request.method.as_deref() {
            return Self::method(
                context,
                request,
                &mut decompiler,
                &classes[0],
                method,
                options,
            );
        }

        if let Some(directory) = request.output_dir.as_deref() {
            context.host_mut().create_dir_all(directory)?;
        }
        let requested = classes.len();
        let mut results = Vec::with_capacity(requested);
        let mut failures = Vec::new();
        let mut output_paths = SourceOutputPaths::default();
        for (index, class) in classes.iter().enumerate() {
            context.progress(&format!(
                "[{}/{}] decompile {}",
                index + 1,
                requested,
                class
            ))?;
            decompiler.clear_analysis_scope();
            let language = match Self::language_for(&mut decompiler, class, request.language) {
                Ok(language) => language,
                Err(error) if !request.fail_fast => {
                    failures.push(GenerationFailure {
                        class: class.clone(),
                        error: error.to_string(),
                    });
                    continue;
                }
                Err(error) => return Err(error),
            };
            decompiler.set_options(options.clone().with_language(language));
            let unit = match decompiler.class(class.clone()) {
                Ok(unit) => unit,
                Err(error) if !request.fail_fast => {
                    failures.push(GenerationFailure {
                        class: class.clone(),
                        error: error.to_string(),
                    });
                    continue;
                }
                Err(error) => return Err(error.into()),
            };
            let output_path = if let Some(directory) = request.output_dir.as_deref() {
                let path = prepare_file_path(&directory.join(output_paths.claim(&unit.path)));
                match context.host_mut().write(&path, unit.source.as_bytes()) {
                    Ok(()) => Some(path),
                    Err(error) if !request.fail_fast => {
                        // Match JADX `SaveCode.save`: log and continue instead of
                        // aborting the remaining classes in the shard.
                        let _ = context
                            .host_mut()
                            .note(&format!("Save file error: {error}"));
                        failures.push(GenerationFailure {
                            class: class.clone(),
                            error: error.to_string(),
                        });
                        continue;
                    }
                    Err(error) => return Err(error),
                }
            } else if let Some(path) = request.output_file.as_deref() {
                let path = prepare_file_path(path);
                context.host_mut().write(&path, unit.source.as_bytes())?;
                Some(path)
            } else {
                None
            };
            results.push(GeneratedSource {
                class: unit.class,
                method: None,
                descriptor: None,
                language: Self::language_name(unit.language),
                output_path: output_path.map(|path| path.display().to_string()),
                method_count: unit.method_count,
                source: (request.output_dir.is_none() && request.output_file.is_none())
                    .then_some(unit.source),
            });
        }

        let report = DecompileReport {
            selection: "classes",
            input: request.input.display().to_string(),
            requested,
            succeeded: results.len(),
            failed: failures.len(),
            output_directory: request
                .output_dir
                .as_ref()
                .map(|path| path.display().to_string()),
            results,
            failures,
        };
        let text = Self::format_report(&report, context.format());
        context.respond("decompile", &report, &text)?;
        Ok(if report.failed == 0 {
            ExitStatus::Success
        } else {
            ExitStatus::PartialFailure
        })
    }

    fn method<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &DecompileRequest,
        decompiler: &mut Decompiler,
        class: &str,
        method: &str,
        options: DecompileOptions,
    ) -> CliResult<ExitStatus> {
        let language = Self::language_for(decompiler, class, request.language)?;
        decompiler.set_options(options.with_language(language));
        let mut method_request = MethodRequest::new(class, method);
        if let Some(descriptor) = request.descriptor.as_deref() {
            method_request = method_request.with_descriptor(descriptor);
        }
        let output = decompiler.method(method_request)?;
        let source = output.source.unwrap_or_else(|| {
            "// Method is abstract or native and has no bytecode body.\n".to_string()
        });
        if let Some(path) = request.output_file.as_deref() {
            context.host_mut().write(path, source.as_bytes())?;
        }
        let result = GeneratedSource {
            class: output.request.class,
            method: Some(output.request.method),
            descriptor: output.request.descriptor,
            language: Self::language_name(output.language),
            output_path: request
                .output_file
                .as_ref()
                .map(|path| path.display().to_string()),
            method_count: 1,
            source: request.output_file.is_none().then_some(source.clone()),
        };
        let report = DecompileReport {
            selection: "method",
            input: request.input.display().to_string(),
            requested: 1,
            succeeded: 1,
            failed: 0,
            output_directory: None,
            results: vec![result],
            failures: Vec::new(),
        };
        let text = Self::format_report(&report, context.format());
        context.respond("decompile", &report, &text)?;
        Ok(ExitStatus::Success)
    }

    fn validate_destination(request: &DecompileRequest, class_count: usize) -> CliResult<()> {
        if class_count == 0 {
            return Err(CliError::not_found("no classes matched the request"));
        }
        if request.method.is_some() && class_count != 1 {
            return Err(CliError::usage(
                "method decompilation requires exactly one --class selector",
            ));
        }
        if request.method.is_some() && request.output_dir.is_some() {
            return Err(CliError::usage(
                "method decompilation accepts --output-file, not --output-dir",
            ));
        }
        if class_count > 1 && request.output_dir.is_none() {
            return Err(CliError::usage(format!(
                "{class_count} classes were selected but no --output-dir was provided"
            ))
            .with_hint("Add `--output-dir decompiled` or select one class with --class."));
        }
        if class_count > 1 && request.output_file.is_some() {
            return Err(CliError::usage(
                "--output-file can only be used with one selected class or method",
            ));
        }
        Ok(())
    }

    fn language_for(
        decompiler: &mut Decompiler,
        class: &str,
        selection: LanguageSelection,
    ) -> CliResult<SourceLanguage> {
        match selection {
            LanguageSelection::Auto => Ok(decompiler.source_language(class.to_string())?),
            LanguageSelection::Fixed(language) => Ok(language),
        }
    }

    fn language_name(language: SourceLanguage) -> &'static str {
        match language {
            SourceLanguage::Java => "java",
            SourceLanguage::Kotlin => "kotlin",
        }
    }

    fn format_report(report: &DecompileReport, format: OutputFormat) -> String {
        if report.requested == 1
            && report.failed == 0
            && report.results[0].source.is_some()
            && format == OutputFormat::Text
        {
            return report.results[0].source.clone().unwrap_or_default();
        }
        let mut text = format!(
            "requested={} succeeded={} failed={}\n",
            report.requested, report.succeeded, report.failed
        );
        for result in &report.results {
            if let Some(path) = result.output_path.as_deref() {
                text.push_str(&format!("ok\t{}\t{path}\n", result.class));
            }
        }
        for failure in &report.failures {
            text.push_str(&format!("failed\t{}\t{}\n", failure.class, failure.error));
        }
        text
    }
}

#[derive(Default)]
struct SourceOutputPaths {
    exact: BTreeMap<PathBuf, PathBuf>,
    portable: BTreeSet<String>,
}

impl SourceOutputPaths {
    fn claim(&mut self, requested: &Path) -> PathBuf {
        if let Some(path) = self.exact.get(requested) {
            return path.clone();
        }
        let portable = Self::portable_key(requested);
        if self.portable.insert(portable) {
            let path = requested.to_path_buf();
            self.exact.insert(path.clone(), path.clone());
            return path;
        }
        let Some(file_name) = requested.file_name() else {
            return requested.to_path_buf();
        };
        let parent = requested.parent().unwrap_or_else(|| Path::new(""));
        for discriminator in 2usize.. {
            let candidate = parent
                .join(format!("__dexdec_case_conflict_{discriminator}"))
                .join(file_name);
            if self.portable.insert(Self::portable_key(&candidate)) {
                self.exact
                    .insert(requested.to_path_buf(), candidate.clone());
                return candidate;
            }
        }
        unreachable!("unbounded output path discriminator");
    }

    fn portable_key(path: &Path) -> String {
        path.components()
            .map(|component| component.as_os_str().to_string_lossy().to_lowercase())
            .collect::<Vec<_>>()
            .join("/")
    }
}

struct SelectionResolver<'a> {
    catalog: &'a crate::ArchiveCatalog,
}

impl<'a> SelectionResolver<'a> {
    fn new(catalog: &'a crate::ArchiveCatalog) -> Self {
        Self { catalog }
    }

    fn resolve<H: CliHost>(
        &self,
        context: &mut CommandContext<'_, H>,
        decompiler: &mut Decompiler,
        request: &DecompileRequest,
    ) -> CliResult<Vec<String>> {
        let mut selectors = request.classes.clone();
        if let Some(path) = request.class_file.as_deref() {
            selectors.extend(ClassFile::load(context, path)?);
        }
        if selectors.is_empty() {
            decompiler.set_options(DecompileOptions::default().with_nested(request.include_nested));
            return Ok(decompiler.select(&ClassSelector::All)?);
        }
        let resolver = ClassResolver::new(self.catalog);
        selectors
            .into_iter()
            .map(|selector| {
                resolver
                    .resolve(&selector)
                    .map(|class| class.descriptor.clone())
            })
            .collect::<CliResult<BTreeSet<_>>>()
            .map(BTreeSet::into_iter)
            .map(Iterator::collect)
    }
}

struct ClassFile;

impl ClassFile {
    fn load<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        path: &Path,
    ) -> CliResult<Vec<String>> {
        let selectors = context
            .host_mut()
            .read_to_string(path)?
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .map(str::to_string)
            .collect::<Vec<_>>();
        if selectors.is_empty() {
            return Err(CliError::input(format!(
                "class selector file is empty: {}",
                path.display()
            )));
        }
        Ok(selectors)
    }
}

#[cfg(test)]
mod tests {
    use super::SourceOutputPaths;
    use std::path::{Path, PathBuf};

    #[test]
    fn case_insensitive_source_paths_do_not_overwrite_each_other() {
        let mut paths = SourceOutputPaths::default();
        let upper = paths.claim(Path::new("example/C.java"));
        let duplicate = paths.claim(Path::new("example/C.java"));
        let lower = paths.claim(Path::new("example/c.java"));

        assert_eq!(upper, PathBuf::from("example/C.java"));
        assert_eq!(duplicate, upper);
        assert_eq!(lower.file_name().unwrap(), "c.java");
        assert_eq!(
            lower,
            PathBuf::from("example/__dexdec_case_conflict_2/c.java")
        );
        assert_ne!(
            SourceOutputPaths::portable_key(&upper),
            SourceOutputPaths::portable_key(&lower)
        );
    }
}
