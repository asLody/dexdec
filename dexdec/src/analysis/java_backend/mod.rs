//! Java source backend.
//!
//! The backend consumes semantic methods, lowers them to a typed Java AST, and
//! prints declarations and statements. It does not infer control-flow meaning.

mod anonymous_lowering;
mod constants;
mod constructor_syntax;
mod declaration_lowering;
mod enum_lowering;
mod exception_contract;
mod field_initialization;
mod function_object_types;
mod generator;
mod java_model;
mod lexical_owners;
mod member_names;
mod method_pipeline;
mod semantic_naming;
mod signature_inference;
mod static_initialization;
mod synthetic_members;
mod type_names;
mod type_ownership;
mod type_uses;
mod type_variable_closure;

use std::sync::Arc;

use crate::analysis::value_recovery::ValueRecoveryError;
use crate::ir::{
    analysis::{ClassHierarchyIndex, SourceVariableError, SsaInvariantError, TypeConstraintError},
    passes::CfgPipelineError,
    structure::StructureError,
    ExceptionInvariantError, RegionInvariantError, SemanticInvariantError,
};
use crate::language::java::{JavaLoweringError, JavaPrintError};
pub use constants::JavaConstantError;
pub use type_names::JavaTypeNameError;

pub(crate) use java_model::{FunctionObjectClass, JavaSourceAbi};
pub(crate) use signature_inference::SourceSignatureInference;
pub(crate) use type_ownership::NestedTypeOwnership;

/// Configuration for Java decompilation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct JavaDecompilerConfig {
    /// Indent string (default: 4 spaces)
    pub indent: String,
}

impl Default for JavaDecompilerConfig {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
        }
    }
}

/// Java decompiler entry point.
pub struct JavaDecompiler {
    config: JavaDecompilerConfig,
    type_hierarchy: Arc<ClassHierarchyIndex>,
    observer: Arc<dyn crate::ir::AnalysisObserver>,
    source_abi: Arc<JavaSourceAbi>,
}

impl JavaDecompiler {
    /// Create a Java decompiler.
    pub fn new(config: JavaDecompilerConfig) -> Self {
        Self {
            config,
            type_hierarchy: Arc::new(ClassHierarchyIndex::default()),
            observer: Arc::new(crate::ir::NullAnalysisObserver),
            source_abi: Arc::new(JavaSourceAbi::default()),
        }
    }

    pub fn with_shared_type_hierarchy(mut self, hierarchy: Arc<ClassHierarchyIndex>) -> Self {
        self.type_hierarchy = hierarchy;
        self
    }

    pub fn with_analysis_observer(
        mut self,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Self {
        self.observer = observer;
        self
    }

    pub(crate) fn with_source_abi(mut self, source_abi: Arc<JavaSourceAbi>) -> Self {
        self.source_abi = source_abi;
        self
    }
}

/// Errors produced while recovering or emitting Java source.
#[derive(Debug)]
pub enum JavaDecompilerError {
    Cancelled(crate::ir::AnalysisCancelled),
    /// A class member failed while building the class model.
    MethodFailed {
        method: String,
        descriptor: String,
        source: Box<JavaDecompilerError>,
    },
    MissingDecodedCfg {
        owner: String,
        method: String,
        descriptor: String,
    },
    NestedClassCycle(String),
    MissingNestedClass(String),
    MalformedNestedClassStack {
        expected: usize,
        actual: usize,
    },
    MalformedDeclarationStack,
    Cfg(CfgPipelineError),
    SourceVariables(SourceVariableError),
    SsaInvariant(SsaInvariantError),
    Exception(ExceptionInvariantError),
    Region(RegionInvariantError),
    Structure(StructureError),
    SemanticInvariant(SemanticInvariantError),
    Semantic(crate::ir::SemanticFoldError),
    Type(TypeConstraintError),
    Value(ValueRecoveryError),
    Java(JavaLoweringError),
    Print(JavaPrintError),
    TypeName(JavaTypeNameError),
    Constant(JavaConstantError),
    GenericSignature(crate::ir::generic_types::SignatureError),
}

impl JavaDecompilerError {
    pub(crate) fn is_cancelled(&self) -> bool {
        match self {
            Self::Cancelled(_) => true,
            Self::MethodFailed { source, .. } => source.is_cancelled(),
            Self::Cfg(crate::ir::passes::CfgPipelineError::Cancelled(_)) => true,
            _ => false,
        }
    }
}

impl std::fmt::Display for JavaDecompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cancelled(error) => error.fmt(f),
            Self::MethodFailed {
                method,
                descriptor,
                source,
            } => write!(f, "Method {method}{descriptor} failed: {source}"),
            Self::MissingDecodedCfg {
                owner,
                method,
                descriptor,
            } => {
                write!(
                    f,
                    "decoded CFG is missing for {owner}->{method}{descriptor}"
                )
            }
            Self::NestedClassCycle(class) => {
                write!(
                    f,
                    "nested-class ownership is cyclic or duplicated at {class}"
                )
            }
            Self::MissingNestedClass(class) => {
                write!(
                    f,
                    "nested class {class} is absent from the loaded DEX graph"
                )
            }
            Self::MalformedNestedClassStack { expected, actual } => write!(
                f,
                "nested-class model stack has {actual} entries, expected at least {expected}"
            ),
            Self::MalformedDeclarationStack => {
                f.write_str("Java declaration lowering stack is malformed")
            }
            Self::Cfg(error) => write!(f, "CFG recovery failed: {error}"),
            Self::SourceVariables(error) => {
                write!(f, "source variable allocation failed: {error}")
            }
            Self::SsaInvariant(error) => write!(f, "SSA invariant failed: {error}"),
            Self::Exception(error) => write!(f, "exception recovery failed: {error}"),
            Self::Region(error) => write!(f, "region recovery failed: {error}"),
            Self::Structure(error) => write!(f, "structuring failed: {error}"),
            Self::SemanticInvariant(error) => {
                write!(f, "semantic invariant failed: {error}")
            }
            Self::Semantic(error) => write!(f, "semantic traversal failed: {error}"),
            Self::Type(error) => write!(f, "type recovery failed: {error}"),
            Self::Value(error) => write!(f, "value recovery failed: {error}"),
            Self::Java(error) => write!(f, "Java lowering failed: {error}"),
            Self::Print(error) => write!(f, "Java printing failed: {error}"),
            Self::TypeName(error) => write!(f, "Java type naming failed: {error}"),
            Self::Constant(error) => write!(f, "Java constant lowering failed: {error}"),
            Self::GenericSignature(error) => write!(f, "generic signature is invalid: {error}"),
        }
    }
}

impl std::error::Error for JavaDecompilerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Cancelled(source) => Some(source),
            Self::MethodFailed { source, .. } => Some(source.as_ref()),
            Self::Cfg(source) => Some(source),
            Self::SourceVariables(source) => Some(source),
            Self::SsaInvariant(source) => Some(source),
            Self::Exception(source) => Some(source),
            Self::Region(source) => Some(source),
            Self::Structure(source) => Some(source),
            Self::SemanticInvariant(source) => Some(source),
            Self::Semantic(source) => Some(source),
            Self::Type(source) => Some(source),
            Self::Value(source) => Some(source),
            Self::Java(source) => Some(source),
            Self::Print(source) => Some(source),
            Self::TypeName(source) => Some(source),
            Self::Constant(source) => Some(source),
            Self::GenericSignature(source) => Some(source),
            Self::MissingDecodedCfg { .. }
            | Self::NestedClassCycle(_)
            | Self::MissingNestedClass(_)
            | Self::MalformedNestedClassStack { .. }
            | Self::MalformedDeclarationStack => None,
        }
    }
}

impl From<StructureError> for JavaDecompilerError {
    fn from(e: StructureError) -> Self {
        Self::Structure(e)
    }
}

macro_rules! backend_error_conversion {
    ($source:ty, $variant:ident) => {
        impl From<$source> for JavaDecompilerError {
            fn from(error: $source) -> Self {
                Self::$variant(error)
            }
        }
    };
}

backend_error_conversion!(CfgPipelineError, Cfg);
backend_error_conversion!(crate::ir::AnalysisCancelled, Cancelled);
backend_error_conversion!(SourceVariableError, SourceVariables);
backend_error_conversion!(SsaInvariantError, SsaInvariant);
backend_error_conversion!(ExceptionInvariantError, Exception);
backend_error_conversion!(RegionInvariantError, Region);
backend_error_conversion!(SemanticInvariantError, SemanticInvariant);
backend_error_conversion!(crate::ir::SemanticFoldError, Semantic);
backend_error_conversion!(TypeConstraintError, Type);
backend_error_conversion!(ValueRecoveryError, Value);
backend_error_conversion!(JavaLoweringError, Java);
backend_error_conversion!(JavaPrintError, Print);
backend_error_conversion!(JavaTypeNameError, TypeName);
backend_error_conversion!(JavaConstantError, Constant);
backend_error_conversion!(crate::ir::generic_types::SignatureError, GenericSignature);
