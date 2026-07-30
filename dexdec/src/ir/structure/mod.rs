//! Control flow structuring for decompilation.
//!
//! Region ownership is established before this module runs. The local reducer
//! receives one region-local CFG and builds semantic IR directly.
//!
//! Reducible SESE subgraphs become structured nodes. Remaining control flow
//! is reduced by SCC normalization, controlled node splitting and lexical
//! NoMoreGotos labels before Semantic IR leaves this module.

mod acyclic;
mod continuation;
mod flow_graph;
mod graph_structurer;
mod loop_classifier;
mod region_reducer;
mod switch_structurer;
mod types;

// Re-export public API
pub use acyclic::AcyclicStructureError;
pub(crate) use loop_classifier::LoopClassifier;
pub use region_reducer::RegionReducer;
pub use types::StructureError;
