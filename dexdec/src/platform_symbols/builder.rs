use std::collections::BTreeMap;
use std::io::{self, Cursor, Read};
use std::path::{Path, PathBuf};

use super::classfile::ClassFileDecoder;
use super::{
    android::AndroidMetadataImporter, AndroidMetadataStats, PlatformFamily, PlatformSymbolDatabase,
    PlatformTarget, SymbolAvailability, SymbolSource,
};

const MAX_CLASS_FILE_SIZE: u64 = 32 * 1024 * 1024;

/// One JAR, JMOD, or signature archive and the platform snapshot it represents.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolArchive {
    pub path: PathBuf,
    pub source: SymbolSource,
    pub version: u16,
}

impl SymbolArchive {
    pub fn new(
        path: impl Into<PathBuf>,
        name: impl Into<String>,
        family: PlatformFamily,
        version: u16,
    ) -> Self {
        Self {
            path: path.into(),
            source: SymbolSource {
                name: name.into(),
                family,
                priority: match family {
                    PlatformFamily::Android => 100,
                    PlatformFamily::Java => 50,
                    PlatformFamily::Library => 10,
                },
            },
            version,
        }
    }

    pub fn with_priority(mut self, priority: i16) -> Self {
        self.source.priority = priority;
        self
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SymbolBuildStats {
    pub archives: usize,
    pub classes: usize,
    pub fields: usize,
    pub methods: usize,
}

impl std::ops::AddAssign for SymbolBuildStats {
    fn add_assign(&mut self, other: Self) {
        self.archives += other.archives;
        self.classes += other.classes;
        self.fields += other.fields;
        self.methods += other.methods;
    }
}

/// Builds a deterministic versioned database directly from JVM class files.
pub struct PlatformSymbolBuilder {
    database: PlatformSymbolDatabase,
    stats: SymbolBuildStats,
}

impl PlatformSymbolBuilder {
    pub fn new(default_target: PlatformTarget) -> Self {
        Self {
            database: PlatformSymbolDatabase::new(default_target),
            stats: SymbolBuildStats::default(),
        }
    }

    /// Extends an existing deterministic database with additional archives.
    pub fn from_database(database: PlatformSymbolDatabase) -> Self {
        Self {
            database,
            stats: SymbolBuildStats::default(),
        }
    }

    pub fn add_archive(&mut self, archive: SymbolArchive) -> io::Result<SymbolBuildStats> {
        if archive.version == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "platform archive version must be non-zero",
            ));
        }
        let source = self.database.add_source(archive.source);
        let classes = ArchiveClassFiles::read(&archive.path, archive.version)?;
        let mut stats = SymbolBuildStats {
            archives: 1,
            ..SymbolBuildStats::default()
        };
        for mut class in classes {
            class.source = source;
            class.availability = SymbolAvailability::exact(archive.version);
            stats.classes += 1;
            stats.fields += class.fields.len();
            stats.methods += class.methods.len();
            self.database.add_class(class);
        }
        self.stats += stats;
        Ok(stats)
    }

    pub fn stats(&self) -> SymbolBuildStats {
        self.stats
    }

    pub fn add_android_metadata(
        &mut self,
        annotations: impl AsRef<Path>,
        api: u16,
    ) -> io::Result<AndroidMetadataStats> {
        AndroidMetadataImporter::apply(&mut self.database, annotations.as_ref(), api)
    }

    pub fn finish(mut self) -> PlatformSymbolDatabase {
        self.database.normalize();
        self.database
    }
}

struct ArchiveClassFiles;

impl ArchiveClassFiles {
    fn read(path: &Path, target_release: u16) -> io::Result<Vec<super::PlatformClass>> {
        let bytes = std::fs::read(path)?;
        let zip_bytes = if bytes.starts_with(b"JM\x01\0") {
            &bytes[4..]
        } else {
            bytes.as_slice()
        };
        let mut archive = zip::ZipArchive::new(Cursor::new(zip_bytes))
            .map_err(|source| archive_error(path, source))?;
        let mut classes = BTreeMap::<String, (u16, super::PlatformClass)>::new();
        for index in 0..archive.len() {
            let mut entry = archive
                .by_index(index)
                .map_err(|source| archive_error(path, source))?;
            if entry.is_dir() {
                continue;
            }
            let entry_name = entry.name().to_string();
            let Some(release) = Self::class_release(&entry_name, target_release) else {
                continue;
            };
            if entry.size() > MAX_CLASS_FILE_SIZE {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{entry_name}: class file exceeds safety limit"),
                ));
            }
            let mut bytes = Vec::with_capacity(entry.size() as usize);
            entry
                .by_ref()
                .take(MAX_CLASS_FILE_SIZE + 1)
                .read_to_end(&mut bytes)?;
            if bytes.len() as u64 > MAX_CLASS_FILE_SIZE {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{entry_name}: class file exceeds safety limit"),
                ));
            }
            let class = ClassFileDecoder::decode(&bytes).map_err(|source| {
                io::Error::new(
                    source.kind(),
                    format!("{}:{entry_name}: {source}", path.display()),
                )
            })?;
            if class.descriptor == "Lmodule-info;" {
                continue;
            }
            let replace = classes
                .get(&class.descriptor)
                .is_none_or(|(current, _)| release >= *current);
            if replace {
                classes.insert(class.descriptor.clone(), (release, class));
            }
        }
        Ok(classes.into_values().map(|(_, class)| class).collect())
    }

    fn class_release(name: &str, target_release: u16) -> Option<u16> {
        let name = name.strip_prefix("classes/").unwrap_or(name);
        if let Some(rest) = name.strip_prefix("META-INF/versions/") {
            let (release, logical) = rest.split_once('/')?;
            let release = release.parse::<u16>().ok()?;
            return (release <= target_release
                && (logical.ends_with(".class") || logical.ends_with(".sig")))
            .then_some(release);
        }
        (name.ends_with(".class") || name.ends_with(".sig")).then_some(0)
    }
}

fn archive_error(path: &Path, source: zip::result::ZipError) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("{}: {source}", path.display()),
    )
}
