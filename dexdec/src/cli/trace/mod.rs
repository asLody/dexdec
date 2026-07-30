//! Diagnostic trace commands (CFG passes, regions, semantic IR).

mod cfg_trace;
mod format;
mod passes;
mod regions;
mod semantic;

pub use passes::TracePassesCommand;
pub use regions::TraceRegionsCommand;
pub use semantic::TraceSemanticCommand;
