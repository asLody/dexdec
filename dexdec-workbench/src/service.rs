use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use dexdec::ir::{AnalysisEvent, AnalysisEventKind, AnalysisObserver, NullAnalysisObserver};
use dexdec::{
    ArchiveCatalog, ClassKind, ClassOutline, ClassSelector, ClassSummary, DecompileOptions,
    Decompiler, FieldOutline, JavaDecompilerConfig, KotlinDecompilerConfig, MethodOutline,
    MethodRequest, ReferenceTarget, SourceLanguage,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::apk_overview::ApkOverviewDto;
use crate::code_search::{
    CodeSearchDocument, CodeSearchEngine, CodeSearchEventDto, CodeSearchObserver,
    CodeSearchRequestDto, CodeSearchSummaryDto,
};
use crate::resources::{ApkResourceArchive, ResourceDocumentDto, ResourceEntryDto};
use crate::symbol_search::{SymbolSearchIndex, SymbolSearchResultDto};

pub struct Workbench {
    sessions: Mutex<HashMap<u64, Arc<Mutex<ArchiveSession>>>>,
    next_session_id: AtomicU64,
    requests: Arc<RequestRegistry>,
}

impl Default for Workbench {
    fn default() -> Self {
        Self {
            sessions: Mutex::new(HashMap::new()),
            next_session_id: AtomicU64::new(1),
            requests: Arc::new(RequestRegistry::default()),
        }
    }
}

impl Workbench {
    pub fn open(&self, path: PathBuf) -> Result<ArchiveDto, ServiceError> {
        let decompiler = Decompiler::open(&path).map_err(ServiceError::decompile)?;
        let resources = ApkResourceArchive::open(&path).map_err(ServiceError::resource)?;
        let catalog = decompiler.catalog();
        let session_id = self.next_session_id.fetch_add(1, Ordering::Relaxed);
        let archive = ArchiveDto::new(
            session_id,
            &path,
            &catalog,
            resources.as_ref().map_or(&[], |archive| archive.entries()),
            resources.as_ref().map(|archive| archive.overview().clone()),
        );
        let session = Arc::new(Mutex::new(ArchiveSession {
            archive: archive.clone(),
            decompiler,
            resources,
            symbol_search: None,
        }));
        self.lock_sessions()?.insert(session_id, session);
        Ok(archive)
    }

    pub fn projects(&self) -> Result<Vec<ArchiveDto>, ServiceError> {
        let sessions = self.lock_sessions()?;
        let mut projects = sessions
            .values()
            .map(|session| {
                session
                    .lock()
                    .map(|session| session.archive.clone())
                    .map_err(|_| ServiceError::StatePoisoned)
            })
            .collect::<Result<Vec<_>, _>>()?;
        projects.sort_unstable_by_key(|project| project.session_id);
        Ok(projects)
    }

    pub fn project(&self, session_id: u64) -> Result<ArchiveDto, ServiceError> {
        let session = self.session(session_id)?;
        let archive = session
            .lock()
            .map_err(|_| ServiceError::StatePoisoned)?
            .archive
            .clone();
        Ok(archive)
    }

    pub fn close(&self, session_id: u64) -> Result<(), ServiceError> {
        self.cancel_requests(session_id);
        if self.lock_sessions()?.remove(&session_id).is_none() {
            return Err(ServiceError::SessionExpired);
        }
        Ok(())
    }

    pub fn read_resource(
        &self,
        session_id: u64,
        path: &str,
    ) -> Result<ResourceDocumentDto, ServiceError> {
        let session = self.session(session_id)?;
        let session = session.lock().map_err(|_| ServiceError::StatePoisoned)?;
        session
            .resources
            .as_ref()
            .ok_or_else(|| ServiceError::Resource("the archive has no resources".to_string()))?
            .read(path)
            .map_err(ServiceError::resource)
    }

    pub fn inspect_class(
        &self,
        session_id: u64,
        descriptor: String,
    ) -> Result<ClassOutlineDto, ServiceError> {
        let session = self.session(session_id)?;
        let mut session = session.lock().map_err(|_| ServiceError::StatePoisoned)?;
        session.decompiler.clear_analysis_scope();
        let outline = session
            .decompiler
            .class_outline(descriptor)
            .map_err(ServiceError::decompile);
        session.decompiler.clear_analysis_scope();
        Ok(outline?.into())
    }

    pub fn begin_request(&self, session_id: u64, request_id: u64) -> Result<(), ServiceError> {
        self.session(session_id)?;
        self.requests
            .begin(RequestDomain::Interactive, session_id, request_id)?;
        Ok(())
    }

    pub fn begin_code_search(&self, session_id: u64, request_id: u64) -> Result<(), ServiceError> {
        self.session(session_id)?;
        self.requests
            .begin(RequestDomain::CodeSearch, session_id, request_id)?;
        Ok(())
    }

    pub fn cancel_requests(&self, session_id: u64) {
        self.requests.cancel_project(session_id);
    }

    pub fn cancel_all_requests(&self) {
        self.requests.cancel_all();
    }

    pub fn cancel_request(&self, session_id: u64, request_id: u64) {
        self.requests
            .cancel(RequestDomain::Interactive, session_id, request_id);
    }

    pub fn cancel_code_search(&self, session_id: u64, request_id: u64) {
        self.requests
            .cancel(RequestDomain::CodeSearch, session_id, request_id);
    }

    pub fn decompile_class(
        &self,
        session_id: u64,
        request_id: u64,
        descriptor: String,
        language: String,
        options: DecompileOptionsDto,
    ) -> Result<SourceDocumentDto, ServiceError> {
        let request = self
            .requests
            .acquire(RequestDomain::Interactive, session_id, request_id)?;
        request.ensure_current()?;
        let session = self.session(session_id)?;
        let mut session = session.lock().map_err(|_| ServiceError::StatePoisoned)?;
        request.ensure_current()?;
        let language = match language_request(&language)? {
            LanguageRequest::Fixed(language) => language,
            LanguageRequest::Auto => session
                .decompiler
                .source_language(descriptor.clone())
                .map_err(ServiceError::decompile)?,
        };
        session.decompiler.clear_analysis_scope();
        let current_options = session.decompiler.options().clone();
        session
            .decompiler
            .set_options(options.apply(current_options, language));
        session
            .decompiler
            .set_observer(Arc::new(RequestObserver::new(request.token())));
        let started = Instant::now();
        let result = (|| {
            let outline = session
                .decompiler
                .class_outline(descriptor.clone())
                .map_err(ServiceError::decompile)?;
            request.ensure_current()?;
            let unit = session
                .decompiler
                .class(descriptor)
                .map_err(ServiceError::decompile)?;
            Ok(SourceDocumentDto {
                descriptor: unit.class,
                language: source_language_name(unit.language).to_string(),
                source_path: unit.path.to_string_lossy().into_owned(),
                source: unit.source,
                method_count: unit.method_count,
                elapsed_ms: elapsed_millis(started),
                outline: outline.into(),
            })
        })();
        session
            .decompiler
            .set_observer(Arc::new(NullAnalysisObserver));
        session.decompiler.clear_analysis_scope();
        result
    }

    pub fn decompile_method(
        &self,
        session_id: u64,
        request_id: u64,
        request: MethodRequestDto,
        language: String,
        options: DecompileOptionsDto,
    ) -> Result<MethodDocumentDto, ServiceError> {
        let request_guard =
            self.requests
                .acquire(RequestDomain::Interactive, session_id, request_id)?;
        request_guard.ensure_current()?;
        let session = self.session(session_id)?;
        let mut session = session.lock().map_err(|_| ServiceError::StatePoisoned)?;
        request_guard.ensure_current()?;
        let language = match language_request(&language)? {
            LanguageRequest::Fixed(language) => language,
            LanguageRequest::Auto => session
                .decompiler
                .source_language(request.class.clone())
                .map_err(ServiceError::decompile)?,
        };
        session.decompiler.clear_analysis_scope();
        let current_options = session.decompiler.options().clone();
        session
            .decompiler
            .set_options(options.apply(current_options, language));
        session
            .decompiler
            .set_observer(Arc::new(RequestObserver::new(request_guard.token())));
        let started = Instant::now();
        let mut method = MethodRequest::new(request.class, request.method);
        if let Some(descriptor) = request.descriptor {
            method = method.with_descriptor(descriptor);
        }
        let output = session
            .decompiler
            .method(method)
            .map_err(ServiceError::decompile);
        session
            .decompiler
            .set_observer(Arc::new(NullAnalysisObserver));
        session.decompiler.clear_analysis_scope();
        let output = output?;
        Ok(MethodDocumentDto {
            class: output.request.class,
            method: output.request.method,
            descriptor: output.request.descriptor,
            language: source_language_name(output.language).to_string(),
            source: output.source,
            elapsed_ms: elapsed_millis(started),
        })
    }

    pub fn find_references(
        &self,
        session_id: u64,
        request_id: u64,
        target: ReferenceTargetDto,
    ) -> Result<ReferenceResultsDto, ServiceError> {
        let request = self
            .requests
            .acquire(RequestDomain::Interactive, session_id, request_id)?;
        request.ensure_current()?;
        let session = self.session(session_id)?;
        let mut session = session.lock().map_err(|_| ServiceError::StatePoisoned)?;
        request.ensure_current()?;
        session
            .decompiler
            .set_observer(Arc::new(RequestObserver::new(request.token())));
        let started = Instant::now();
        let result = session
            .decompiler
            .references(target.into())
            .map_err(ServiceError::decompile);
        session
            .decompiler
            .set_observer(Arc::new(NullAnalysisObserver));
        session.decompiler.clear_analysis_scope();
        let results = result?;
        request.ensure_current()?;
        Ok(ReferenceResultsDto {
            locations: results
                .locations
                .into_iter()
                .map(|location| ReferenceLocationDto {
                    class_descriptor: location.class,
                    method: location.method,
                    descriptor: location.descriptor,
                    offset: location.offset,
                })
                .collect(),
            elapsed_ms: elapsed_millis(started),
        })
    }

    pub fn search_symbols(
        &self,
        session_id: u64,
        query: &str,
        limit: usize,
    ) -> Result<Vec<SymbolSearchResultDto>, ServiceError> {
        let session = self.session(session_id)?;
        let mut session = session.lock().map_err(|_| ServiceError::StatePoisoned)?;
        if session.symbol_search.is_none() {
            let classes = session.decompiler.catalog();
            let resources = session
                .resources
                .as_ref()
                .map_or(&[][..], |archive| archive.entries());
            let mut builder = SymbolSearchIndex::builder(&classes, resources);
            session
                .decompiler
                .visit_members(&mut builder)
                .map_err(ServiceError::decompile)?;
            session.symbol_search = Some(builder.finish());
        }
        Ok(session
            .symbol_search
            .as_ref()
            .expect("symbol index initialized above")
            .search(query, limit))
    }

    pub fn search_code(
        &self,
        session_id: u64,
        request_id: u64,
        search: CodeSearchRequestDto,
        language: String,
        options: DecompileOptionsDto,
        observer: &mut dyn CodeSearchObserver,
    ) -> Result<CodeSearchSummaryDto, ServiceError> {
        let request = self
            .requests
            .acquire(RequestDomain::CodeSearch, session_id, request_id)?;
        request.ensure_current()?;
        let mut engine = CodeSearchEngine::new(&search).map_err(ServiceError::search)?;
        let session = self.session(session_id)?;
        let mut session = session.lock().map_err(|_| ServiceError::StatePoisoned)?;
        request.ensure_current()?;

        // Search always presents one coherent source dialect. The UI no longer
        // exposes automatic per-class language selection; old persisted `auto`
        // preferences are interpreted as Java for deterministic result lines.
        let language = match language_request(&language)? {
            LanguageRequest::Fixed(language) => language,
            LanguageRequest::Auto => SourceLanguage::Java,
        };
        let current_options = session.decompiler.options().clone();
        session
            .decompiler
            .set_options(options.apply(current_options, language));
        session
            .decompiler
            .set_observer(Arc::new(RequestObserver::new(request.token())));
        session.decompiler.clear_analysis_scope();

        let started = Instant::now();
        let result = (|| {
            let mut batch = session
                .decompiler
                .classes(ClassSelector::All)
                .map_err(ServiceError::decompile)?;
            let total_classes = batch.len();
            let mut scanned_classes = 0;
            let mut failed_classes = 0;
            emit_search_progress(
                observer,
                scanned_classes,
                total_classes,
                failed_classes,
                engine.matches(),
            )?;

            for item in &mut batch {
                request.ensure_current()?;
                scanned_classes += 1;
                match item {
                    Ok(unit) => {
                        let source_path = unit.path.to_string_lossy();
                        engine
                            .scan(
                                CodeSearchDocument {
                                    class_descriptor: &unit.class,
                                    source_path: &source_path,
                                    source: &unit.source,
                                },
                                observer,
                            )
                            .map_err(ServiceError::search)?;
                    }
                    Err(_) => {
                        request.ensure_current()?;
                        failed_classes += 1;
                    }
                }
                if scanned_classes % 16 == 0 || engine.truncated() {
                    emit_search_progress(
                        observer,
                        scanned_classes,
                        total_classes,
                        failed_classes,
                        engine.matches(),
                    )?;
                }
                if engine.truncated() {
                    break;
                }
            }
            request.ensure_current()?;
            engine.finish(observer).map_err(ServiceError::search)?;
            emit_search_progress(
                observer,
                scanned_classes,
                total_classes,
                failed_classes,
                engine.matches(),
            )?;
            Ok(CodeSearchSummaryDto {
                scanned_classes,
                total_classes,
                failed_classes,
                matches: engine.matches(),
                truncated: engine.truncated(),
                elapsed_ms: elapsed_millis(started),
            })
        })();
        session
            .decompiler
            .set_observer(Arc::new(NullAnalysisObserver));
        session.decompiler.clear_analysis_scope();
        result
    }

    fn lock_sessions(
        &self,
    ) -> Result<std::sync::MutexGuard<'_, HashMap<u64, Arc<Mutex<ArchiveSession>>>>, ServiceError>
    {
        self.sessions
            .lock()
            .map_err(|_| ServiceError::StatePoisoned)
    }

    fn session(&self, session_id: u64) -> Result<Arc<Mutex<ArchiveSession>>, ServiceError> {
        self.lock_sessions()?
            .get(&session_id)
            .cloned()
            .ok_or(ServiceError::SessionExpired)
    }
}

struct ArchiveSession {
    archive: ArchiveDto,
    decompiler: Decompiler,
    resources: Option<ApkResourceArchive>,
    symbol_search: Option<SymbolSearchIndex>,
}

fn emit_search_progress(
    observer: &mut dyn CodeSearchObserver,
    scanned_classes: usize,
    total_classes: usize,
    failed_classes: usize,
    matches: usize,
) -> Result<(), ServiceError> {
    observer
        .emit(CodeSearchEventDto::Progress {
            scanned_classes,
            total_classes,
            failed_classes,
            matches,
        })
        .then_some(())
        .ok_or(ServiceError::RequestCancelled)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum RequestDomain {
    Interactive,
    CodeSearch,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RequestKey {
    domain: RequestDomain,
    session_id: u64,
    request_id: u64,
}

#[derive(Default)]
struct RequestRegistry {
    active: Mutex<HashMap<RequestKey, Arc<AtomicBool>>>,
}

impl RequestRegistry {
    fn begin(
        &self,
        domain: RequestDomain,
        session_id: u64,
        request_id: u64,
    ) -> Result<(), ServiceError> {
        let key = RequestKey {
            domain,
            session_id,
            request_id,
        };
        let mut active = self
            .active
            .lock()
            .map_err(|_| ServiceError::StatePoisoned)?;
        if let Some(previous) = active.insert(key, Arc::new(AtomicBool::new(false))) {
            previous.store(true, Ordering::Release);
        }
        Ok(())
    }

    fn acquire(
        self: &Arc<Self>,
        domain: RequestDomain,
        session_id: u64,
        request_id: u64,
    ) -> Result<RequestLease, ServiceError> {
        let key = RequestKey {
            domain,
            session_id,
            request_id,
        };
        let token = self
            .active
            .lock()
            .map_err(|_| ServiceError::StatePoisoned)?
            .entry(key)
            .or_insert_with(|| Arc::new(AtomicBool::new(false)))
            .clone();
        Ok(RequestLease {
            key,
            token,
            registry: Arc::clone(self),
        })
    }

    fn cancel(&self, domain: RequestDomain, session_id: u64, request_id: u64) {
        let key = RequestKey {
            domain,
            session_id,
            request_id,
        };
        if let Ok(active) = self.active.lock() {
            if let Some(token) = active.get(&key) {
                token.store(true, Ordering::Release);
            }
        }
    }

    fn cancel_project(&self, session_id: u64) {
        if let Ok(active) = self.active.lock() {
            for (key, token) in active.iter() {
                if key.session_id == session_id {
                    token.store(true, Ordering::Release);
                }
            }
        }
    }

    fn cancel_all(&self) {
        if let Ok(active) = self.active.lock() {
            for token in active.values() {
                token.store(true, Ordering::Release);
            }
        }
    }

    fn finish(&self, key: RequestKey, token: &Arc<AtomicBool>) {
        if let Ok(mut active) = self.active.lock() {
            if active
                .get(&key)
                .is_some_and(|current| Arc::ptr_eq(current, token))
            {
                active.remove(&key);
            }
        }
    }
}

struct RequestLease {
    key: RequestKey,
    token: Arc<AtomicBool>,
    registry: Arc<RequestRegistry>,
}

impl RequestLease {
    fn token(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.token)
    }

    fn ensure_current(&self) -> Result<(), ServiceError> {
        if self.token.load(Ordering::Acquire) {
            Err(ServiceError::RequestCancelled)
        } else {
            Ok(())
        }
    }
}

impl Drop for RequestLease {
    fn drop(&mut self) {
        self.registry.finish(self.key, &self.token);
    }
}

struct RequestObserver {
    cancelled: Arc<AtomicBool>,
}

impl RequestObserver {
    fn new(cancelled: Arc<AtomicBool>) -> Self {
        Self { cancelled }
    }
}

impl AnalysisObserver for RequestObserver {
    fn is_enabled(&self, _kind: AnalysisEventKind) -> bool {
        false
    }

    fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }

    fn observe(&self, _event: AnalysisEvent<'_>) {}
}

#[derive(Debug, thiserror::Error)]
pub enum ServiceError {
    #[error("the archive session has changed")]
    SessionExpired,
    #[error("request was cancelled or superseded")]
    RequestCancelled,
    #[error("the decompiler service state is unavailable")]
    StatePoisoned,
    #[error("unsupported source language: {0}")]
    UnsupportedLanguage(String),
    #[error("{0}")]
    Search(String),
    #[error("{0}")]
    Decompile(String),
    #[error("{0}")]
    Resource(String),
}

impl ServiceError {
    fn decompile(error: impl std::fmt::Display) -> Self {
        Self::Decompile(error.to_string())
    }

    fn resource(error: impl std::fmt::Display) -> Self {
        Self::Resource(error.to_string())
    }

    fn search(error: impl std::fmt::Display) -> Self {
        Self::Search(error.to_string())
    }
}

/// What the client asked to read a class as.
#[derive(Debug, Clone, Copy)]
enum LanguageRequest {
    /// Read it as whatever it was written in.
    Auto,
    Fixed(SourceLanguage),
}

fn language_request(value: &str) -> Result<LanguageRequest, ServiceError> {
    match value {
        "auto" => Ok(LanguageRequest::Auto),
        "java" => Ok(LanguageRequest::Fixed(SourceLanguage::Java)),
        "kotlin" => Ok(LanguageRequest::Fixed(SourceLanguage::Kotlin)),
        _ => Err(ServiceError::UnsupportedLanguage(value.to_string())),
    }
}

fn source_language_name(language: SourceLanguage) -> &'static str {
    match language {
        SourceLanguage::Java => "java",
        SourceLanguage::Kotlin => "kotlin",
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ArchiveDto {
    pub session_id: u64,
    pub path: String,
    pub name: String,
    pub class_count: usize,
    pub classes: Vec<ClassSummaryDto>,
    pub resources: Vec<ResourceEntryDto>,
    pub overview: Option<ApkOverviewDto>,
}

impl ArchiveDto {
    fn new(
        session_id: u64,
        path: &Path,
        catalog: &ArchiveCatalog,
        resources: &[ResourceEntryDto],
        overview: Option<ApkOverviewDto>,
    ) -> Self {
        Self {
            session_id,
            path: path.to_string_lossy().into_owned(),
            name: path.file_name().map_or_else(
                || "DEX archive".to_string(),
                |name| name.to_string_lossy().into(),
            ),
            class_count: catalog.len(),
            classes: catalog
                .classes()
                .iter()
                .map(ClassSummaryDto::from)
                .collect(),
            resources: resources.to_vec(),
            overview,
        }
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ClassSummaryDto {
    pub descriptor: String,
    pub qualified_name: String,
    pub package: String,
    pub binary_name: String,
    pub display_name: String,
    pub parent_descriptor: Option<String>,
    pub source_path: String,
}

impl From<&ClassSummary> for ClassSummaryDto {
    fn from(class: &ClassSummary) -> Self {
        Self {
            descriptor: class.descriptor.clone(),
            qualified_name: class.qualified_name.clone(),
            package: class.package.clone(),
            binary_name: class.binary_name.clone(),
            display_name: class.display_name.clone(),
            parent_descriptor: class.parent_descriptor.clone(),
            source_path: class.source_path.to_string_lossy().into_owned(),
        }
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ClassOutlineDto {
    pub descriptor: String,
    pub qualified_name: String,
    pub kind: &'static str,
    pub access_flags: u32,
    pub super_class: Option<String>,
    pub interfaces: Vec<String>,
    pub source_file: Option<String>,
    pub parent_class: Option<String>,
    pub nested_classes: Vec<String>,
    pub fields: Vec<FieldOutlineDto>,
    pub methods: Vec<MethodOutlineDto>,
}

impl From<ClassOutline> for ClassOutlineDto {
    fn from(class: ClassOutline) -> Self {
        let kind = match class.kind {
            ClassKind::Class => "class",
            ClassKind::Interface => "interface",
            ClassKind::Annotation => "annotation",
            ClassKind::Enum => "enum",
            _ => "class",
        };
        Self {
            descriptor: class.descriptor,
            qualified_name: class.qualified_name,
            kind,
            access_flags: class.access_flags,
            super_class: class.super_class,
            interfaces: class.interfaces,
            source_file: class.source_file,
            parent_class: class.parent_class,
            nested_classes: class.nested_classes,
            fields: class
                .fields
                .into_iter()
                .map(FieldOutlineDto::from)
                .collect(),
            methods: class
                .methods
                .into_iter()
                .map(MethodOutlineDto::from)
                .collect(),
        }
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct FieldOutlineDto {
    pub name: String,
    pub descriptor: String,
    pub display_type: String,
    pub access_flags: u32,
}

impl From<FieldOutline> for FieldOutlineDto {
    fn from(field: FieldOutline) -> Self {
        Self {
            name: field.name,
            descriptor: field.descriptor,
            display_type: field.display_type,
            access_flags: field.access_flags,
        }
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct MethodOutlineDto {
    pub name: String,
    pub descriptor: String,
    pub display_signature: String,
    pub access_flags: u32,
    pub has_code: bool,
    pub constructor: bool,
}

impl From<MethodOutline> for MethodOutlineDto {
    fn from(method: MethodOutline) -> Self {
        Self {
            name: method.name,
            descriptor: method.descriptor,
            display_signature: method.display_signature,
            access_flags: method.access_flags,
            has_code: method.has_code,
            constructor: method.constructor,
        }
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct SourceDocumentDto {
    pub descriptor: String,
    pub language: String,
    pub source_path: String,
    pub source: String,
    pub method_count: usize,
    pub elapsed_ms: u64,
    pub outline: ClassOutlineDto,
}

/// Output settings the desktop client lets the user change per request.
#[derive(Debug, Clone, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct DecompileOptionsDto {
    pub indent_width: u8,
    pub include_nested: bool,
}

impl DecompileOptionsDto {
    fn apply(&self, options: DecompileOptions, language: SourceLanguage) -> DecompileOptions {
        let indent = " ".repeat(self.indent_width.clamp(1, 8) as usize);
        let mut java = JavaDecompilerConfig::default();
        java.indent = indent.clone();
        let mut kotlin = KotlinDecompilerConfig::default();
        kotlin.indent = indent;
        options
            .with_language(language)
            .with_java(java)
            .with_kotlin(kotlin)
            .with_nested(self.include_nested)
    }
}

#[derive(Debug, Clone, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct MethodRequestDto {
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct MethodDocumentDto {
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
    pub language: String,
    pub source: Option<String>,
    pub elapsed_ms: u64,
}

#[derive(Debug, Clone, Deserialize, JsonSchema)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum ReferenceTargetDto {
    Class {
        #[serde(rename = "classDescriptor")]
        class_descriptor: String,
    },
    Field {
        #[serde(rename = "classDescriptor")]
        class_descriptor: String,
        name: String,
        descriptor: String,
    },
    Method {
        #[serde(rename = "classDescriptor")]
        class_descriptor: String,
        name: String,
        descriptor: String,
    },
}

impl From<ReferenceTargetDto> for ReferenceTarget {
    fn from(target: ReferenceTargetDto) -> Self {
        match target {
            ReferenceTargetDto::Class { class_descriptor } => {
                ReferenceTarget::class(class_descriptor)
            }
            ReferenceTargetDto::Field {
                class_descriptor,
                name,
                descriptor,
            } => ReferenceTarget::field(class_descriptor, name, descriptor),
            ReferenceTargetDto::Method {
                class_descriptor,
                name,
                descriptor,
            } => ReferenceTarget::method(class_descriptor, name, descriptor),
        }
    }
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceLocationDto {
    pub class_descriptor: String,
    pub method: String,
    pub descriptor: String,
    pub offset: u32,
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ReferenceResultsDto {
    pub locations: Vec<ReferenceLocationDto>,
    pub elapsed_ms: u64,
}

fn elapsed_millis(started: Instant) -> u64 {
    started.elapsed().as_millis().min(u64::MAX as u128) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cancellation_is_scoped_to_one_project_request() {
        let registry = Arc::new(RequestRegistry::default());
        registry.begin(RequestDomain::Interactive, 1, 7).unwrap();
        registry.begin(RequestDomain::Interactive, 2, 7).unwrap();
        let first = registry.acquire(RequestDomain::Interactive, 1, 7).unwrap();
        let second = registry.acquire(RequestDomain::Interactive, 2, 7).unwrap();

        registry.cancel(RequestDomain::Interactive, 1, 7);

        assert!(matches!(
            first.ensure_current(),
            Err(ServiceError::RequestCancelled)
        ));
        assert!(second.ensure_current().is_ok());
    }

    #[test]
    fn code_search_cancellation_does_not_cancel_interactive_work() {
        let registry = Arc::new(RequestRegistry::default());
        registry.begin(RequestDomain::Interactive, 1, 7).unwrap();
        registry.begin(RequestDomain::CodeSearch, 1, 7).unwrap();
        let interactive = registry.acquire(RequestDomain::Interactive, 1, 7).unwrap();
        let search = registry.acquire(RequestDomain::CodeSearch, 1, 7).unwrap();

        registry.cancel(RequestDomain::CodeSearch, 1, 7);

        assert!(interactive.ensure_current().is_ok());
        assert!(matches!(
            search.ensure_current(),
            Err(ServiceError::RequestCancelled)
        ));
    }
}
