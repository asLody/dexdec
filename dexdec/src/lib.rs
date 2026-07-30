//! Dex Decompiler Core Library
//!
//! This library provides DEX file parsing and decompilation capabilities.
//!
//! ## Architecture
//!
//! ```text
//! DEX -> normalized SSA CFG -> RegionGraph -> Semantic IR
//!     -> sparse value and type recovery -> typed source AST -> language printer
//! ```
//!
//! Control-flow meaning is recovered once in Region IR. Value recovery and
//! language backends consume semantic facts and never infer meaning from
//! rendered source shapes.
//!
//! ## Modules
//!
//! - `ir` - Intermediate Representation (types, args, instructions, blocks, CFG, passes, exception)
//! - `decoder` - Dalvik bytecode decoder
//! - `frontend` - DEX file parsing and class/method structures
//! - `api` - High-level decompilation API
//! - `visualizer` - CFG and IR visualization
//! - `analysis` - Value, type, hierarchy, and language-backend analyses
//! - `language` - Typed target-language ASTs and printers

pub mod analysis;
pub mod api;
#[cfg(feature = "cli")]
pub mod cli;
pub mod decoder;
pub mod frontend;
pub mod ir;
pub mod language;
pub mod platform_symbols;
pub mod profiling;
pub mod visualizer;

// Re-export main types for convenience
pub use api::{
    decode_method, java_source_path, kotlin_source_path, load_dex, source_path, ArchiveCatalog,
    ArchiveMemberCatalog, BatchSummary, ClassBatch, ClassFailure, ClassKind, ClassOutline,
    ClassSelector, ClassSummary, DecodedMethod, DecompileError, DecompileOptions, Decompiler,
    DecompilerContext, FieldOutline, MemberKind, MemberSummary, MemberVisitor, MethodOutline,
    MethodOutput, MethodRequest, ReferenceLocation, ReferenceResults, ReferenceTarget,
    SourceLanguage, SourceUnit,
};
pub use frontend::{ClassNode, DexError, DexFileReader, DexResult, MethodCode, MethodNode};
pub use platform_symbols::{
    default_platform_symbols, PlatformAnnotation, PlatformAnnotationValue, PlatformClass,
    PlatformConstant, PlatformConstantDomain, PlatformConstantKind, PlatformConstantMember,
    PlatformFamily, PlatformField, PlatformFieldReference, PlatformMethod, PlatformSymbolDatabase,
    PlatformSymbolSet, PlatformTarget, SymbolAvailability, SymbolDatabaseStats, SymbolProvider,
    SymbolSource,
};
#[cfg(feature = "symbol-builder")]
pub use platform_symbols::{
    AndroidMetadataStats, PlatformSymbolBuilder, SymbolArchive, SymbolBuildStats,
};

// IR types
pub use ir::{ArgType, InsnArg, InsnNode, InsnType, RegisterArg};
pub use ir::{Block, BlockId, EdgeKind, ExceptionHandler, CFG};
pub use ir::{Pass, PassResult, Splitter};

// Exception analysis
pub use ir::{CatchHandler, ExceptionAnalysis, TryRegion};

// Visualization
pub use visualizer::{method_to_dot, method_to_text};

// Analysis and code generation
pub use analysis::{
    JavaDecompiler, JavaDecompilerConfig, JavaDecompilerError, KotlinDecompiler,
    KotlinDecompilerConfig, KotlinDecompilerError,
};
