//! Pass Framework
//!
//! A composable pass system for CFG analysis and transformation.
//!
//! ## Module Structure
//!
//! - [`Pass`] - The core trait for all passes
//! - [`PassResult`] - Indicates whether a pass modified the CFG
//!
//! This layer is limited to CFG invariants, SSA construction, and topology
//! normalization. Source-expression and structured-control recovery live above
//! it and are not expressed as CFG pass chains.
//!
mod bind_results;
mod canonicalize;
mod cfg_pipeline;
mod phi_simplify;
mod pipeline;
mod prune_unreachable;
mod recover_constructors;
mod split_critical_edges;
mod split_monitor_entries;
mod ssa_transform;
mod validate;

pub use bind_results::{BindResults, ResultBindingError};
pub use canonicalize::{CanonicalizationError, CanonicalizeCFG};
pub use cfg_pipeline::{CfgAnalysis, CfgPipeline, CfgPipelineError};
pub use phi_simplify::{PhiSimplificationError, PhiSimplify};
pub use pipeline::{Pass, PassResult};
pub use prune_unreachable::PruneUnreachable;
pub use recover_constructors::{ConstructorRecoveryError, RecoverConstructors};
pub use split_critical_edges::SplitCriticalEdges;
pub use split_monitor_entries::{MonitorSplitError, SplitMonitorEntries};
pub use ssa_transform::{SSATransform, SsaTransformError};
pub use validate::{CfgInvariantError, ValidateCFG};
