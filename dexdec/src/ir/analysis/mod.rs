//! IR Analysis Module
//!
//! This module provides various analyses on the CFG including:
//! - Dominator tree computation
//! - Edge-sensitive SSA liveness and value identity

mod control_contractions;
mod control_flow;
mod dominance_frontier;
mod dominator_tree;
mod effects;
mod evaluation;
mod lexical_boundary;
mod objects;
mod post_dominators;
mod reaching_conditions;
mod register_liveness;
mod scc;
mod semantic_flow;
mod source_variables;
mod ssa;
mod termination;
mod types;
mod value_origins;
mod variable_semantics;

pub use control_contractions::{ControlContractions, NormalCopySite};
pub use control_flow::{ControlContinuations, ControlFlowFacts};
pub use dominance_frontier::DominanceFrontier;
pub use dominator_tree::{DominanceError, DominatorTree};
pub use effects::{InstructionEffects, ThrowEffect};
pub use evaluation::{SourceEvaluation, SourceEvaluationError};
pub use lexical_boundary::{LexicalBoundary, LexicalBoundaryAnalysis};
pub use objects::{ObjectInitialization, ObjectInitializationError, ObjectInitializations};
pub use post_dominators::PostDominatorTree;
pub use reaching_conditions::{ReachingCondition, ReachingConditionError, ReachingConditions};
pub use register_liveness::RegisterLiveness;
pub use scc::{StrongComponent, StrongComponents};
pub use semantic_flow::{
    SemanticFlowEdgeKind, SemanticFlowGraph, SemanticFlowPoint, SemanticReachability,
    SemanticReachingValues, SemanticValueDefinition,
};
pub use source_variables::{SourceVariableAllocation, SourceVariableError};
pub use ssa::{
    CodeVariables, InsnPosition, PhiInput, PhiMerge, SsaClasses, SsaInvariantError, SsaUseSite,
    SsaValue, SsaValueGraph, SsaVar, UsePosition, ValueCopy,
};
pub use termination::MethodTermination;
pub use types::{
    ClassHierarchyIndex, ReferenceTypeInfo, SourceTypeEnvironment, SsaTypeEnvironment,
    SubtypeRelation, TypeConstraintError, TypeHierarchy, TypeSolver,
};
pub use value_origins::SsaOrigins;
pub use variable_semantics::{
    OperationNode, OperationOperand, RecurrenceKind, StructuralVariableRoleAnalysis, VariableEdge,
    VariableEdgeKind, VariableNode, VariableRole, VariableRoleAnalysis, VariableRoleScores,
    VariableSemanticGraph,
};
