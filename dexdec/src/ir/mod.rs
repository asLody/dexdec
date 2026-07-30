//! Intermediate Representation (IR)
//!
//! ## Components
//!
//! - `ty` - Type system
//! - `arg` - Instruction arguments
//! - `insn` - Instructions
//! - `block` - Basic blocks
//! - `cfg` - Control Flow Graph
//! - `passes` - Pass framework and built-in passes
//! - `analysis` - SSA identity, dominance, liveness, object and type analysis
//! - `splitter` - CFG builder
//! - `exception` - Exception handling structures
//! - `region` - Region/leave based structured control-flow IR
//! - `bool_expr` - Boolean expressions for reaching conditions
//! - `bdd` - BDD utilities for boolean equivalence

pub mod analysis;
pub mod arg;
pub mod bdd;
pub mod block;
pub mod bool_expr;
pub mod cfg;
pub mod diagnostics;
pub mod exception;
pub mod generic_types;
pub mod insn;
pub mod instruction_tree;
pub mod passes;
pub mod reference;
pub mod region;
pub mod semantic;
pub mod splitter;
pub mod structure;
pub mod ty;
pub mod utf16;

// Types
pub use arg::{InsnArg, LiteralArg, RegNum, RegisterArg};
pub use insn::{
    ArithOp, CmpBias, IfOp, InsnNode, InsnPayload, InsnType, InstructionEquivalence, InstructionId,
    InvokeType, UnaryOp,
};
pub use instruction_tree::{
    InstructionTransform, InstructionTree, InstructionTreeError, InstructionVisitor,
};
pub use ty::{ArgType, DescriptorParseError, MethodDescriptor, PrimitiveType};
pub use utf16::Utf16String;

// Block and CFG
pub use block::{Block, BlockId, ExceptionHandler};
pub use cfg::{EdgeKind, MethodContext, CFG};
pub use diagnostics::{
    AnalysisCancelled, AnalysisEvent, AnalysisEventKind, AnalysisObserver, GatedPhiDiagnostic,
    GatedPhiRejection, InvocationTypeDiagnostic, NullAnalysisObserver, SemanticStage,
    SourceTypeDiagnostics, SourceTypeEquationDiagnostic, ValueRecoveryDiagnostics,
};
pub use reference::{FieldReference, MemberReference, MethodReference, ReferenceParseError};

// Passes
pub use passes::{Pass, PassResult, PruneUnreachable, ValidateCFG};

// Splitter
pub use splitter::Splitter;

// Exception handling
pub use exception::{
    CatchHandler, ExceptionAnalysis, ExceptionAnalyzer, ExceptionInvariantError, HandlerKind,
    TryRegion,
};

// Boolean expressions
pub use bool_expr::{BoolExpr, BoolVariable};

// Region-based structured IR
pub use region::{
    CatchRegion, LoopRegion, RegionEdge, RegionExit, RegionExitKind, RegionGraph,
    RegionGraphBuilder, RegionId, RegionInvariantError, RegionKind, RegionLeave, RegionTransfer,
    RegionTransferKind, RegionTree, ResolvedRegionExit, StructuredRegion, SwitchRegion,
    SynchronizedRegion,
};
pub(crate) use semantic::SemanticSiteNumbering;
pub use semantic::{
    SemanticBindingKind, SemanticBlock, SemanticBuildError, SemanticCatch, SemanticContext,
    SemanticExpression, SemanticExpressionFacts, SemanticExpressionTransform, SemanticFinally,
    SemanticFoldControl, SemanticFoldError, SemanticFolder, SemanticInstructions,
    SemanticInvariantError, SemanticLabel, SemanticLabelKind, SemanticLeave, SemanticLeaveKind,
    SemanticLoopControl, SemanticLoopKind, SemanticLoopTest, SemanticMethod, SemanticNode,
    SemanticOperand, SemanticOperation, SemanticPredicate, SemanticSiteId, SemanticStatement,
    SemanticStatementKind, SemanticSwitchCase, SemanticVisitor, SourceSemantics,
    SourceSyntaxSemantics, SourceVariableContext, SsaSemantics, StatementOrigin,
    StringBuilderProtocol, StringBuildingRecovery, ValueSemantics,
};

// Structuring algorithm
pub use structure::StructureError;
