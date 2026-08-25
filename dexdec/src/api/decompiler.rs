//! Stable, high-level decompilation interface.

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use rayon::prelude::*;

use super::ClassRenderInput;
use crate::analysis::java_backend::JavaSourceAbi;
use crate::analysis::kotlin_backend::KotlinSourceAbi;
use crate::analysis::{
    JavaDecompiler, JavaDecompilerConfig, KotlinDecompiler, KotlinDecompilerConfig,
};
use crate::frontend::kotlin_metadata::KotlinMetadata;
use crate::frontend::DexFileReader;
use crate::ir::analysis::ClassHierarchyIndex;
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
    /// When true (default), each class request discards the loaded class graph
    /// so one interactive lookup cannot leak into the next. Full-archive
    /// decompilation should set this to false and keep shared analysis.
    pub isolate_requests: bool,
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

    pub fn with_isolated_requests(mut self, isolate_requests: bool) -> Self {
        self.isolate_requests = isolate_requests;
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
            isolate_requests: true,
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

    /// Generate many classes while reusing the loaded archive graph.
    ///
    /// Shared hierarchy/ABI, one decode pass, one termination solve, then
    /// class generation in parallel. This loads the requested classes (and
    /// nested types when `include_nested`) itself; callers need not
    /// `load_all_classes()`. After collect, leftover frontend/IR buffers are
    /// dropped. Later requests on the same `Decompiler` must load classes
    /// again.
    pub fn generate_classes(
        &mut self,
        classes: Vec<(String, SourceLanguage)>,
    ) -> Result<Vec<Result<SourceUnit, ClassFailure>>, DecompileError> {
        if classes.is_empty() {
            return Ok(Vec::new());
        }
        if self.options.isolate_requests || classes.len() == 1 {
            return Ok(classes
                .into_iter()
                .map(|(class, language)| {
                    self.set_options(self.options.clone().with_language(language));
                    let class_name = class.clone();
                    let method_count = self
                        .context
                        .get_class(&class)
                        .map_or(0, |node| node.methods().len());
                    self.class(class).map_err(|error| ClassFailure {
                        class: class_name,
                        method_count,
                        error,
                    })
                })
                .collect());
        }

        let needs_java = classes
            .iter()
            .any(|(_, language)| *language == SourceLanguage::Java);
        let needs_kotlin = classes
            .iter()
            .any(|(_, language)| *language == SourceLanguage::Kotlin);
        let include_nested = self.options.include_nested;
        self.context.load_archive_selection(
            classes.iter().map(|(class, _)| class.as_str()),
            include_nested,
        )?;
        self.context.set_retain_decoded_methods(true);
        let generated = self.generate_archive_classes(classes, needs_java, needs_kotlin);
        self.context.set_retain_decoded_methods(false);
        generated
    }

    fn generate_archive_classes(
        &mut self,
        classes: Vec<(String, SourceLanguage)>,
        needs_java: bool,
        needs_kotlin: bool,
    ) -> Result<Vec<Result<SourceUnit, ClassFailure>>, DecompileError> {
        let stats = batch_stats_enabled();
        let t0 = Instant::now();
        self.context.prepare_archive_overrides()?;
        let overrides_ms = t0.elapsed();
        let t1 = Instant::now();
        self.context.prefetch_decoded_methods()?;
        let prefetch_ms = t1.elapsed();
        let t2 = Instant::now();
        self.context
            .prepare_archive_source_abi_before_termination(needs_java, needs_kotlin)?;
        let abi_prefix_ms = t2.elapsed();
        let t3 = Instant::now();
        self.context.apply_archive_termination()?;
        let termination_ms = t3.elapsed();
        let t4 = Instant::now();
        self.context
            .prepare_archive_source_abi_after_termination(needs_kotlin)?;
        let abi_ms = abi_prefix_ms + t4.elapsed();

        let include_nested = self.options.include_nested;
        let observer = Arc::clone(&self.observer);
        let t4 = Instant::now();
        let mut ready = Vec::new();
        let mut finished: Vec<Option<Result<SourceUnit, ClassFailure>>> =
            (0..classes.len()).map(|_| None).collect();
        for (index, (class, language)) in classes.into_iter().enumerate() {
            let method_count = self
                .context
                .get_class(&class)
                .map_or(0, |node| node.methods().len());
            match self.context.collect_class_render_input(
                &class,
                include_nested,
                Arc::clone(&observer),
                false,
            ) {
                Ok(Some(input)) => ready.push((
                    index,
                    ArchiveClassJob {
                        class,
                        language,
                        method_count,
                        input,
                    },
                )),
                Ok(None) => {
                    finished[index] = Some(Err(ClassFailure {
                        class: class.clone(),
                        method_count,
                        error: DecompileError::ClassNotFound(class),
                    }));
                }
                Err(error) => {
                    finished[index] = Some(Err(ClassFailure {
                        class,
                        method_count,
                        error,
                    }));
                }
            }
        }

        let collect_ms = t4.elapsed();
        let hierarchy = self.context.type_hierarchy()?;
        if needs_java {
            self.context.prepare_java_source_abi()?;
        }
        let java_abi = if needs_java {
            self.context.java_source_abi()
        } else {
            Arc::new(JavaSourceAbi::default())
        };
        let kotlin_abi = if needs_kotlin {
            self.context.kotlin_source_abi()?
        } else {
            Arc::new(KotlinSourceAbi::default())
        };
        self.context.abandon_archive_buffers();
        let java = self.options.java.clone();
        let kotlin = self.options.kotlin.clone();
        let observer = Arc::clone(&self.observer);

        let t5 = Instant::now();
        let rendered = ready
            .into_par_iter()
            .with_min_len(1)
            .map(|(index, job)| {
                let started = Instant::now();
                let class = job.class.clone();
                let result = render_archive_job(
                    job,
                    &java,
                    &kotlin,
                    &hierarchy,
                    &java_abi,
                    &kotlin_abi,
                    &observer,
                );
                (index, class, started.elapsed(), result)
            })
            .collect::<Vec<_>>();
        let generate_ms = t5.elapsed();
        if stats {
            let mut slow = rendered
                .iter()
                .map(|(_, class, elapsed, _)| (elapsed.as_secs_f64() * 1000.0, class.as_str()))
                .collect::<Vec<_>>();
            slow.sort_by(|left, right| right.0.total_cmp(&left.0));
            let top = slow
                .into_iter()
                .take(8)
                .map(|(ms, class)| format!("{class}={ms:.0}ms"))
                .collect::<Vec<_>>()
                .join(" ");
            eprintln!(
                "dexdec batch: overrides={:.0}ms prefetch={:.0}ms abi={:.0}ms termination={:.0}ms collect={:.0}ms generate={:.0}ms classes={} slowest[{}]",
                overrides_ms.as_secs_f64() * 1000.0,
                prefetch_ms.as_secs_f64() * 1000.0,
                abi_ms.as_secs_f64() * 1000.0,
                termination_ms.as_secs_f64() * 1000.0,
                collect_ms.as_secs_f64() * 1000.0,
                generate_ms.as_secs_f64() * 1000.0,
                finished.len(),
                top,
            );
        }
        for (index, _, _, result) in rendered {
            finished[index] = Some(result);
        }
        Ok(finished
            .into_iter()
            .map(|result| result.expect("every archive class slot is filled"))
            .collect())
    }

    fn generate_class(&mut self, class: String) -> Result<SourceUnit, DecompileError> {
        if self.options.isolate_requests {
            self.clear_analysis_scope();
        }
        if self.context.get_class(&class).is_none()
            && self.context.load_class_deferred(&class)?.is_none()
        {
            return Err(DecompileError::ClassNotFound(class));
        }
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
        let source = generated?.ok_or_else(|| DecompileError::ClassNotFound(class.clone()))?;
        if self.options.isolate_requests {
            self.clear_analysis_scope();
        }
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
        self.summary.classes += 1;
        Some(match self.decompiler.generate_class(class.clone()) {
            Ok(source) => {
                self.summary.methods += source.method_count;
                Ok(source)
            }
            Err(error) => {
                let method_count = self
                    .decompiler
                    .context
                    .get_class(&class)
                    .map_or(0, |node| node.methods().len());
                if self.decompiler.options().isolate_requests {
                    self.decompiler.clear_analysis_scope();
                } else {
                    self.decompiler.context.clear_method_cache();
                }
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

fn batch_stats_enabled() -> bool {
    std::env::var_os("DEXDEC_BATCH_STATS").is_some()
}

struct ArchiveClassJob {
    class: String,
    language: SourceLanguage,
    method_count: usize,
    input: ClassRenderInput,
}

fn archive_java_parallel_methods() -> bool {
    archive_java_parallel_methods_from(std::env::var_os("DEXDEC_ARCHIVE_METHOD_PARALLEL"))
}

fn archive_java_parallel_methods_from(value: Option<std::ffi::OsString>) -> bool {
    // Nested rayon inside class-level archive jobs oversubscribed the pool
    // (study wall 85s -> 88s). Exact "1" remains the A/B override.
    value.as_deref() == Some(std::ffi::OsStr::new("1"))
}

fn archive_kotlin_parallel_methods() -> bool {
    archive_java_parallel_methods_from(std::env::var_os("DEXDEC_ARCHIVE_METHOD_PARALLEL"))
}

fn render_archive_job(
    mut job: ArchiveClassJob,
    java: &JavaDecompilerConfig,
    kotlin: &KotlinDecompilerConfig,
    hierarchy: &Arc<ClassHierarchyIndex>,
    java_abi: &Arc<JavaSourceAbi>,
    kotlin_abi: &Arc<KotlinSourceAbi>,
    observer: &Arc<dyn AnalysisObserver>,
) -> Result<SourceUnit, ClassFailure> {
    let generated = match job.language {
        SourceLanguage::Java => {
            let mut decompiler = JavaDecompiler::new(java.clone())
                .with_shared_type_hierarchy(Arc::clone(hierarchy))
                .with_source_abi(Arc::clone(java_abi))
                .with_analysis_observer(Arc::clone(observer))
                .with_parallel_methods(archive_java_parallel_methods());
            debug_assert!(
                !decompiler.parallel_methods() || archive_java_parallel_methods(),
                "archive Java jobs set parallel_methods=false unless DEXDEC_ARCHIVE_METHOD_PARALLEL=1"
            );
            decompiler
                .generate_class_with_nested(
                    &job.input.class_node,
                    &mut job.input.methods,
                    job.input.nested,
                )
                .map_err(DecompileError::from)
        }
        SourceLanguage::Kotlin => KotlinDecompiler::new(kotlin.clone())
            .with_shared_type_hierarchy(Arc::clone(hierarchy))
            .with_source_abi(Arc::clone(kotlin_abi))
            .with_analysis_observer(Arc::clone(observer))
            .with_parallel_methods(archive_kotlin_parallel_methods())
            .generate_class_with_nested(
                &job.input.class_node,
                &mut job.input.methods,
                job.input.nested,
            )
            .map_err(DecompileError::from),
    };
    match generated {
        Ok(source) => Ok(SourceUnit {
            path: source_path(&job.class, job.language),
            class: job.class,
            language: job.language,
            method_count: job.method_count,
            source,
        }),
        Err(error) => Err(ClassFailure {
            class: job.class,
            method_count: job.method_count,
            error,
        }),
    }
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
    fn archive_java_jobs_disable_method_parallelism() {
        assert!(!archive_java_parallel_methods_from(None));
        assert!(!archive_java_parallel_methods_from(Some("0".into())));
        assert!(archive_java_parallel_methods_from(Some("1".into())));
        let decompiler =
            JavaDecompiler::new(JavaDecompilerConfig::default()).with_parallel_methods(false);
        assert!(!decompiler.parallel_methods());
    }

    #[test]
    fn archive_kotlin_jobs_disable_method_parallelism() {
        assert!(!archive_kotlin_parallel_methods());
        let decompiler =
            KotlinDecompiler::new(KotlinDecompilerConfig::default()).with_parallel_methods(false);
        assert!(!decompiler.parallel_methods());
        let parallel = KotlinDecompiler::new(KotlinDecompilerConfig::default());
        assert!(parallel.parallel_methods());
    }

    #[test]
    fn generate_classes_loads_requested_classes_without_full_archive() {
        let dex = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/testcases/classes.dex");
        let mut decompiler = Decompiler::open(dex).expect("open test DEX");
        decompiler.set_options(
            DecompileOptions::default()
                .with_language(SourceLanguage::Java)
                .with_isolated_requests(false),
        );
        let results = decompiler
            .generate_classes(vec![
                ("LHelloWorld;".into(), SourceLanguage::Java),
                ("LSimpleIf;".into(), SourceLanguage::Java),
            ])
            .expect("generate requested classes");
        assert_eq!(results.len(), 2);
        for result in results {
            result.expect("requested class should decompile without load_all_classes");
        }
        let again = decompiler
            .generate_classes(vec![
                ("LHelloWorld;".into(), SourceLanguage::Java),
                ("LSimpleIf;".into(), SourceLanguage::Java),
            ])
            .expect("second archive pass after abandon");
        assert_eq!(again.len(), 2);
        for result in again {
            result.expect("abandoned buffers must not poison a later archive pass");
        }
    }

    #[test]
    fn isolate_class_requests_discard_loaded_graph() {
        let dex = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/testcases/classes.dex");
        let mut decompiler = Decompiler::open(dex).expect("open test DEX");
        decompiler.set_options(DecompileOptions::default().with_language(SourceLanguage::Java));
        decompiler
            .class("LHelloWorld;")
            .expect("first isolate class");
        assert!(
            decompiler.reader().get_class("LHelloWorld;").is_none(),
            "isolate class requests must discard the loaded class graph"
        );
        decompiler
            .class("LSimpleIf;")
            .expect("second isolate class after scope clear");
        assert!(decompiler.reader().get_class("LHelloWorld;").is_none());
        assert!(decompiler.reader().get_class("LSimpleIf;").is_none());
    }

    #[test]
    fn isolate_java_decompiler_enables_method_parallelism() {
        let decompiler = JavaDecompiler::new(JavaDecompilerConfig::default());
        assert!(decompiler.parallel_methods());
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
