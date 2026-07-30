//! Clap-free request models for the command-line application.

use std::path::PathBuf;

use crate::SourceLanguage;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputFormat {
    Text,
    Json,
    JsonLines,
}

#[derive(Debug, Clone, Copy)]
pub struct OutputOptions {
    pub format: OutputFormat,
    pub pretty: bool,
    pub quiet: bool,
}

#[derive(Debug, Clone)]
pub struct Invocation {
    pub output: OutputOptions,
    pub command: Command,
}

#[derive(Debug, Clone)]
pub enum Command {
    Capabilities,
    Inspect(InspectRequest),
    Search(SearchRequest),
    Decompile(DecompileRequest),
    References(ReferencesRequest),
    Resources(ResourcesRequest),
    Debug(DebugRequest),
    Symbols(SymbolsRequest),
}

#[derive(Debug, Clone)]
pub struct InspectRequest {
    pub input: PathBuf,
    pub class: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchKind {
    Any,
    Class,
    Field,
    Method,
    Resource,
}

#[derive(Debug, Clone)]
pub struct SearchRequest {
    pub input: PathBuf,
    pub query: String,
    pub kind: SearchKind,
    pub offset: usize,
    pub limit: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LanguageSelection {
    Auto,
    Fixed(SourceLanguage),
}

#[derive(Debug, Clone)]
pub struct DecompileRequest {
    pub input: PathBuf,
    pub classes: Vec<String>,
    pub class_file: Option<PathBuf>,
    pub method: Option<String>,
    pub descriptor: Option<String>,
    pub output_dir: Option<PathBuf>,
    pub output_file: Option<PathBuf>,
    pub language: LanguageSelection,
    pub include_nested: bool,
    pub fail_fast: bool,
}

#[derive(Debug, Clone)]
pub struct ReferencesRequest {
    pub input: PathBuf,
    pub target: ReferenceQuery,
}

#[derive(Debug, Clone)]
pub enum ReferenceQuery {
    Class {
        class: String,
    },
    Field {
        class: String,
        name: String,
        descriptor: Option<String>,
    },
    Method {
        class: String,
        name: String,
        descriptor: Option<String>,
    },
}

#[derive(Debug, Clone)]
pub enum ResourcesRequest {
    List(ResourceListRequest),
    Read(ResourceReadRequest),
}

#[derive(Debug, Clone)]
pub struct ResourceListRequest {
    pub input: PathBuf,
    pub query: Option<String>,
    pub kind: Option<String>,
    pub offset: usize,
    pub limit: usize,
}

#[derive(Debug, Clone)]
pub struct ResourceReadRequest {
    pub input: PathBuf,
    pub path: String,
    pub output_file: Option<PathBuf>,
    pub raw: bool,
    pub max_bytes: u64,
}

#[derive(Debug, Clone)]
pub enum DebugRequest {
    Cfg(CfgRequest),
    Ir(IrRequest),
    TracePasses(TracePassesRequest),
    TraceRegions(TraceRegionsRequest),
    TraceSemantic(TraceSemanticRequest),
}

#[derive(Debug, Clone)]
pub struct CfgRequest {
    pub input: PathBuf,
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
    pub format: String,
    pub output: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct IrRequest {
    pub input: PathBuf,
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
    pub output: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct TracePassesRequest {
    pub input: PathBuf,
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
    pub blocks: Option<String>,
    pub changed_details: bool,
    pub output: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct TraceRegionsRequest {
    pub input: PathBuf,
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
    pub output: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct TraceSemanticRequest {
    pub input: PathBuf,
    pub class: String,
    pub method: String,
    pub descriptor: Option<String>,
    pub language: SourceLanguage,
    pub output: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub enum SymbolsRequest {
    Build(SymbolsBuildRequest),
    Inspect(SymbolsInspectRequest),
}

#[derive(Debug, Clone)]
pub struct SymbolsBuildRequest {
    pub output: PathBuf,
    pub base_database: Option<PathBuf>,
    pub jdk_home: Option<PathBuf>,
    pub java_release: Option<u16>,
    pub jdk_modules: Vec<String>,
    pub android_sdk: Option<PathBuf>,
    pub android_apis: Vec<u16>,
    pub library_archives: Vec<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct SymbolsInspectRequest {
    pub database: PathBuf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExitStatus {
    Success,
    PartialFailure,
}

impl ExitStatus {
    pub fn code(self) -> i32 {
        match self {
            Self::Success => 0,
            Self::PartialFailure => 5,
        }
    }
}
