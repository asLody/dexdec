//! Stable, high-level decompilation interface.

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::analysis::{JavaDecompilerConfig, KotlinDecompilerConfig};
use crate::frontend::kotlin_metadata::KotlinMetadata;
use crate::frontend::DexFileReader;
use crate::ir::{AnalysisObserver, NullAnalysisObserver};
use crate::language::java::JavaIdentifier;
use crate::language::kotlin::KotlinIdentifier;

use super::{
    ArchiveCatalog, ArchiveMemberCatalog, ClassOutline, ReferenceLocation, ReferenceResults,
    ReferenceTarget,
};
use super::{DecompileError, DecompilerContext};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SourceLanguage {
    Java,
    #[default]
    Kotlin,
}

/// Source-generation settings shared by method and class requests.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct DecompileOptions {
    pub language: SourceLanguage,
    pub java: JavaDecompilerConfig,
    pub kotlin: KotlinDecompilerConfig,
    pub include_nested: bool,
}

impl DecompileOptions {
    pub fn with_language(mut self, language: SourceLanguage) -> Self {
        self.language = language;
        self
    }

    pub fn with_java(mut self, java: JavaDecompilerConfig) -> Self {
        self.java = java;
        self
    }

    pub fn with_kotlin(mut self, kotlin: KotlinDecompilerConfig) -> Self {
        self.kotlin = kotlin;
        self
    }

    pub fn with_nested(mut self, include_nested: bool) -> Self {
        self.include_nested = include_nested;
        self
    }
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            language: SourceLanguage::default(),
            java: JavaDecompilerConfig::default(),
            kotlin: KotlinDecompilerConfig::default(),
            include_nested: true,
        }
    }
}

/// A deterministic class selection for batch decompilation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ClassSelector {
    All,
    Exact(String),
    Matching(String),
    Listed(BTreeSet<String>),
}

impl ClassSelector {
    pub fn exact(descriptor: impl Into<String>) -> Self {
        Self::Exact(descriptor.into())
    }

    pub fn matching(query: impl Into<String>) -> Self {
        Self::Matching(query.into())
    }

    pub fn listed(classes: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self::Listed(classes.into_iter().map(Into::into).collect())
    }

    fn explicitly_names_classes(&self) -> bool {
        matches!(self, Self::Exact(_) | Self::Listed(_))
    }
}

/// An exact or name-only method request.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct MethodRequest {
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
}

impl MethodRequest {
    pub fn new(class: impl Into<String>, method: impl Into<String>) -> Self {
        Self {
            class: class.into(),
            method: method.into(),
            descriptor: None,
        }
    }

    pub fn with_descriptor(mut self, descriptor: impl Into<String>) -> Self {
        self.descriptor = Some(descriptor.into());
        self
    }
}

/// Output for one source compilation unit.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SourceUnit {
    pub class: String,
    pub language: SourceLanguage,
    pub path: PathBuf,
    pub method_count: usize,
    pub source: String,
}

/// Source output for a method. `source` is absent for abstract and native methods.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct MethodOutput {
    pub request: MethodRequest,
    pub language: SourceLanguage,
    pub source: Option<String>,
}

/// A class-local generation failure returned by [`ClassBatch`].
#[derive(Debug)]
#[non_exhaustive]
pub struct ClassFailure {
    pub class: String,
    pub method_count: usize,
    pub error: DecompileError,
}

impl std::fmt::Display for ClassFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}: {}", self.class, self.error)
    }
}

impl std::error::Error for ClassFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

/// Aggregate counters collected without retaining generated source text.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct BatchSummary {
    pub classes: usize,
    pub methods: usize,
    pub failures: usize,
    pub failed_methods: usize,
}

/// Reusable decompiler service. It owns caches and is silent unless an observer is installed.
pub struct Decompiler {
    context: DecompilerContext,
    options: DecompileOptions,
    observer: Arc<dyn AnalysisObserver>,
    reference_cache: HashMap<ReferenceTarget, Vec<ReferenceLocation>>,
}

impl Decompiler {
    pub fn open(path: impl AsRef<Path>) -> Result<Self, DecompileError> {
        Ok(Self {
            context: DecompilerContext::from_file(path)?,
            options: DecompileOptions::default(),
            observer: Arc::new(NullAnalysisObserver),
            reference_cache: HashMap::new(),
        })
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecompileError> {
        Ok(Self::from_reader(DexFileReader::from_bytes(bytes)?))
    }

    pub fn from_reader(reader: DexFileReader) -> Self {
        Self {
            context: DecompilerContext::from_reader(reader),
            options: DecompileOptions::default(),
            observer: Arc::new(NullAnalysisObserver),
            reference_cache: HashMap::new(),
        }
    }

    pub fn with_options(mut self, options: DecompileOptions) -> Self {
        self.options = options;
        self
    }

    pub fn with_observer(mut self, observer: Arc<dyn AnalysisObserver>) -> Self {
        self.observer = observer;
        self
    }

    pub fn set_observer(&mut self, observer: Arc<dyn AnalysisObserver>) {
        self.observer = observer;
    }

    pub fn options(&self) -> &DecompileOptions {
        &self.options
    }

    pub fn set_options(&mut self, options: DecompileOptions) {
        self.options = options;
    }

    /// Discard request-local class and semantic caches while retaining the
    /// parsed archive catalog and DEX metadata.
    pub fn clear_analysis_scope(&mut self) {
        self.context.clear_analysis_scope();
    }

    pub fn reader(&self) -> &DexFileReader {
        self.context.reader()
    }

    pub fn reader_mut(&mut self) -> &mut DexFileReader {
        self.context.reader_mut()
    }

    /// Build the lightweight class catalog used by interactive clients.
    ///
    /// This only reads class definition names. It does not load class bodies,
    /// decode methods, or generate source.
    pub fn catalog(&self) -> ArchiveCatalog {
        ArchiveCatalog::from_reader(self.context.reader())
    }

    /// Build the member directory used by interactive symbol search.
    ///
    /// This parses field and method declarations but does not decode bytecode,
    /// construct IR, or generate source.
    pub fn member_catalog(&self) -> Result<ArchiveMemberCatalog, DecompileError> {
        ArchiveMemberCatalog::from_reader(self.context.reader()).map_err(Into::into)
    }

    /// Stream member declarations to a client-owned index or analysis.
    pub fn visit_members(
        &self,
        visitor: &mut dyn super::MemberVisitor,
    ) -> Result<(), DecompileError> {
        self.context
            .reader()
            .visit_member_declarations(|member| visitor.visit(member.into()))
            .map_err(Into::into)
    }

    /// The language a class was written in, as far as the class itself says.
    ///
    /// The Kotlin compiler stamps everything it emits with `@kotlin.Metadata`,
    /// down to the synthetic classes it makes for lambdas. R8 often strips that
    /// annotation but leaves the DEX `SourceFile` (`.kt`), which is the same
    /// attribute JADX uses to recover Kotlin file names. A class with neither
    /// signal is read back as Java.
    ///
    /// Only the class declaration is read; no method body is decoded.
    pub fn source_language(
        &mut self,
        class: impl Into<String>,
    ) -> Result<SourceLanguage, DecompileError> {
        let class = class.into();
        let Some(node) = self.context.load_class_deferred(&class)? else {
            return Err(DecompileError::ClassNotFound(class));
        };
        Ok(inferred_source_language(
            &node.annotations,
            node.source_file.as_deref(),
        ))
    }

    /// Inspect one class declaration without decoding any method body.
    pub fn class_outline(
        &mut self,
        class: impl Into<String>,
    ) -> Result<ClassOutline, DecompileError> {
        let class = class.into();
        if self.context.load_class_deferred(&class)?.is_none() {
            return Err(DecompileError::ClassNotFound(class));
        }
        Ok(ClassOutline::from_node(
            self.context
                .get_class(&class)
                .expect("class was loaded immediately above"),
        ))
    }

    /// Locate bytecode sites matching a class or member query.
    ///
    /// Each distinct target is scanned once per decompiler instance. The scan
    /// reads encoded methods directly and does not load classes or generate IR.
    pub fn references(
        &mut self,
        target: ReferenceTarget,
    ) -> Result<ReferenceResults, DecompileError> {
        if let Some(locations) = self.reference_cache.get(&target) {
            return Ok(ReferenceResults {
                target,
                locations: locations.clone(),
            });
        }
        let locations = self
            .context
            .reader()
            .find_references(&target.dex_target())?
            .into_iter()
            .map(|location| ReferenceLocation {
                class: location.class,
                method: location.method,
                descriptor: location.descriptor,
                offset: location.offset,
            })
            .collect::<Vec<_>>();
        self.reference_cache
            .insert(target.clone(), locations.clone());
        Ok(ReferenceResults { target, locations })
    }

    pub fn select(&mut self, selector: &ClassSelector) -> Result<Vec<String>, DecompileError> {
        let explicit = selector.explicitly_names_classes();
        let mut classes = match selector {
            ClassSelector::All => {
                self.context.load_all_classes()?;
                self.context.class_names()
            }
            ClassSelector::Exact(class) => {
                if self.context.load_class_deferred(class)?.is_none() {
                    return Err(DecompileError::ClassNotFound(class.clone()));
                }
                vec![class.clone()]
            }
            ClassSelector::Matching(query) => {
                self.context.load_all_classes()?;
                self.context
                    .class_names()
                    .into_iter()
                    .filter(|class| class.contains(query))
                    .collect()
            }
            ClassSelector::Listed(classes) => {
                self.context
                    .load_classes_deferred(classes.iter().map(String::as_str))?;
                for class in classes {
                    if self.context.get_class(class).is_none() {
                        return Err(DecompileError::ClassNotFound(class.clone()));
                    }
                }
                classes.iter().cloned().collect()
            }
        };
        if self.options.include_nested && !explicit {
            classes.retain(|class| self.context.class_is_compilation_unit(class));
        }
        classes.sort_unstable();
        classes.dedup();
        Ok(classes)
    }

    pub fn class(&mut self, class: impl Into<String>) -> Result<SourceUnit, DecompileError> {
        let class = class.into();
        if self.context.load_class_deferred(&class)?.is_none() {
            return Err(DecompileError::ClassNotFound(class));
        }
        self.generate_class(class)
    }

    pub fn method(&mut self, mut request: MethodRequest) -> Result<MethodOutput, DecompileError> {
        if self.context.load_class(&request.class)?.is_none() {
            return Err(DecompileError::ClassNotFound(request.class));
        }
        let class = self
            .context
            .get_class(&request.class)
            .expect("loaded class");
        let candidates = class
            .methods()
            .iter()
            .filter(|method| method.info.name == request.method)
            .map(|method| method.info.descriptor())
            .filter(|descriptor| {
                request
                    .descriptor
                    .as_ref()
                    .is_none_or(|wanted| super::normalize_descriptor(wanted) == *descriptor)
            })
            .collect::<Vec<_>>();
        let descriptor = match candidates.as_slice() {
            [] => {
                return Err(DecompileError::MethodNotFound {
                    class: request.class,
                    method: request.method,
                    descriptor: request.descriptor,
                });
            }
            [descriptor] => descriptor.clone(),
            descriptors => {
                return Err(DecompileError::AmbiguousMethod {
                    class: request.class,
                    method: request.method,
                    descriptors: descriptors.to_vec(),
                });
            }
        };
        request.descriptor = Some(descriptor.clone());
        let source = match self.options.language {
            SourceLanguage::Java => self
                .context
                .decompile_java_method_with_config_and_observer(
                    &request.class,
                    &request.method,
                    Some(&descriptor),
                    &self.options.java,
                    Arc::clone(&self.observer),
                )?,
            SourceLanguage::Kotlin => self.context.decompile_method_with_config_and_observer(
                &request.class,
                &request.method,
                Some(&descriptor),
                &self.options.kotlin,
                Arc::clone(&self.observer),
            )?,
        };
        Ok(MethodOutput {
            request,
            language: self.options.language,
            source,
        })
    }

    pub fn classes(&mut self, selector: ClassSelector) -> Result<ClassBatch<'_>, DecompileError> {
        let classes = self.select(&selector)?;
        Ok(ClassBatch {
            decompiler: self,
            classes: classes.into_iter(),
            summary: BatchSummary::default(),
        })
    }

    fn generate_class(&mut self, class: String) -> Result<SourceUnit, DecompileError> {
        let method_count = self
            .context
            .get_class(&class)
            .ok_or_else(|| DecompileError::ClassNotFound(class.clone()))?
            .methods()
            .len();
        let generated = match self.options.language {
            SourceLanguage::Java => self.context.decompile_java_class_observed(
                &class,
                &self.options.java,
                self.options.include_nested,
                Arc::clone(&self.observer),
            ),
            SourceLanguage::Kotlin => self.context.decompile_class_observed(
                &class,
                &self.options.kotlin,
                self.options.include_nested,
                Arc::clone(&self.observer),
            ),
        };
        self.context.clear_method_cache();
        let source = generated?.ok_or_else(|| DecompileError::ClassNotFound(class.clone()))?;
        Ok(SourceUnit {
            path: source_path(&class, self.options.language),
            class,
            language: self.options.language,
            method_count,
            source,
        })
    }
}

/// Streaming batch iterator. Each source is released before the next class is generated.
pub struct ClassBatch<'a> {
    decompiler: &'a mut Decompiler,
    classes: std::vec::IntoIter<String>,
    summary: BatchSummary,
}

impl ClassBatch<'_> {
    pub fn len(&self) -> usize {
        self.classes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.classes.len() == 0
    }

    pub fn summary(&self) -> BatchSummary {
        self.summary
    }
}

impl Iterator for ClassBatch<'_> {
    type Item = Result<SourceUnit, ClassFailure>;

    fn next(&mut self) -> Option<Self::Item> {
        let class = self.classes.next()?;
        let method_count = self
            .decompiler
            .context
            .get_class(&class)
            .map_or(0, |node| node.methods().len());
        self.summary.classes += 1;
        self.summary.methods += method_count;
        Some(match self.decompiler.generate_class(class.clone()) {
            Ok(source) => Ok(source),
            Err(error) => {
                self.decompiler.context.clear_method_cache();
                self.summary.failures += 1;
                self.summary.failed_methods += method_count;
                Err(ClassFailure {
                    class,
                    method_count,
                    error,
                })
            }
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.classes.size_hint()
    }
}

impl ExactSizeIterator for ClassBatch<'_> {}

pub fn source_path(descriptor: &str, language: SourceLanguage) -> PathBuf {
    let binary_name = descriptor
        .strip_prefix('L')
        .and_then(|name| name.strip_suffix(';'))
        .unwrap_or(descriptor);
    let (package, binary_simple_name) = binary_name
        .rsplit_once('/')
        .map_or(("", binary_name), |(package, name)| (package, name));
    let mut path = PathBuf::new();
    for segment in package.split('/').filter(|segment| !segment.is_empty()) {
        path.push(match language {
            SourceLanguage::Java => JavaIdentifier::from_dex(segment).to_string(),
            SourceLanguage::Kotlin => KotlinIdentifier::from_dex(segment).to_string(),
        });
    }
    let (name, extension) = match language {
        SourceLanguage::Java => (
            JavaIdentifier::from_dex(binary_simple_name).to_string(),
            "java",
        ),
        SourceLanguage::Kotlin => (
            KotlinIdentifier::from_dex(binary_simple_name).to_string(),
            "kt",
        ),
    };
    path.push(format!("{name}.{extension}"));
    path
}

/// Relative Java source path derived from a DEX class descriptor.
pub fn java_source_path(descriptor: &str) -> PathBuf {
    source_path(descriptor, SourceLanguage::Java)
}

/// Relative Kotlin source path derived from a DEX class descriptor.
pub fn kotlin_source_path(descriptor: &str) -> PathBuf {
    source_path(descriptor, SourceLanguage::Kotlin)
}

fn inferred_source_language(
    annotations: &[crate::frontend::AnnotationNode],
    source_file: Option<&str>,
) -> SourceLanguage {
    if annotations.iter().any(KotlinMetadata::is_metadata) || is_kotlin_source_file(source_file) {
        SourceLanguage::Kotlin
    } else {
        SourceLanguage::Java
    }
}

fn is_kotlin_source_file(source_file: Option<&str>) -> bool {
    source_file.is_some_and(|name| {
        name.ends_with(".kt") || name.ends_with(".kts") || name.ends_with(".ktm")
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_path_uses_kotlin_identifiers() {
        assert_eq!(
            kotlin_source_path("Lexample/bad-name/Test$class;"),
            PathBuf::from("example/`bad-name`/`Test$class`.kt")
        );
    }

    #[test]
    fn listed_selection_is_sorted_and_unique() {
        assert_eq!(
            ClassSelector::listed(["LB;", "LA;", "LB;"]),
            ClassSelector::Listed(BTreeSet::from(["LA;".to_string(), "LB;".to_string()]))
        );
    }

    #[test]
    fn source_file_kt_selects_kotlin_without_metadata() {
        assert_eq!(
            inferred_source_language(&[], Some("PipHintTracker.kt")),
            SourceLanguage::Kotlin
        );
        assert_eq!(
            inferred_source_language(&[], Some("Script.kts")),
            SourceLanguage::Kotlin
        );
        assert_eq!(
            inferred_source_language(&[], Some("Main.java")),
            SourceLanguage::Java
        );
        assert_eq!(inferred_source_language(&[], None), SourceLanguage::Java);
    }
}
