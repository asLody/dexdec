//! Contract for one verified CFG transformation.

use crate::ir::cfg::CFG;

/// Pass result indicating whether the CFG was modified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PassResult {
    /// The pass did not modify the CFG.
    Unchanged,
    /// The pass modified the CFG.
    Changed,
}

impl From<bool> for PassResult {
    fn from(changed: bool) -> Self {
        if changed {
            Self::Changed
        } else {
            Self::Unchanged
        }
    }
}

/// The core trait for all CFG passes.
///
/// A pass is a single analysis or transformation step that operates on a CFG.
pub trait Pass {
    type Error: std::error::Error;

    /// Returns the name of this pass for debugging and error reporting.
    fn name(&self) -> &'static str;

    /// Run the pass on the given CFG.
    ///
    /// Returns [`PassResult::Changed`] if the CFG was modified,
    /// [`PassResult::Unchanged`] otherwise.
    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error>;
}
