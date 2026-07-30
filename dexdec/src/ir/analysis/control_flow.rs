//! Immutable ordinary-control-flow facts shared by region analyses.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BlockId, InsnType, CFG};

use super::{DominanceError, DominatorTree, PostDominatorTree};

#[derive(Debug, Clone)]
pub struct ControlFlowFacts {
    predecessors: BTreeMap<BlockId, Vec<BlockId>>,
    semantic_predecessors: BTreeMap<BlockId, Vec<BlockId>>,
    dominators: DominatorTree,
    semantic_dominators: DominatorTree,
    postdominators: PostDominatorTree,
    continuations: ControlContinuations,
    structural_continuations: ControlContinuations,
}

impl ControlFlowFacts {
    pub fn analyze(cfg: &CFG) -> Result<Self, DominanceError> {
        let predecessors = cfg.normal_predecessor_snapshot();
        let semantic_predecessors = cfg.predecessor_snapshot();
        let dominators = DominatorTree::compute_normal(cfg, cfg.block_ids(), &predecessors)?;
        let semantic_dominators = DominatorTree::compute(cfg)?;
        let postdominators = PostDominatorTree::compute(cfg)?;
        let continuations = ControlContinuations::analyze(cfg);
        let structural_continuations = ControlContinuations::preserving(cfg, &BTreeSet::new());
        Ok(Self {
            predecessors,
            semantic_predecessors,
            dominators,
            semantic_dominators,
            postdominators,
            continuations,
            structural_continuations,
        })
    }

    pub fn predecessors(&self, block: BlockId) -> Option<&[BlockId]> {
        self.predecessors.get(&block).map(Vec::as_slice)
    }

    pub fn semantic_predecessors(&self, block: BlockId) -> Option<&[BlockId]> {
        self.semantic_predecessors.get(&block).map(Vec::as_slice)
    }

    pub fn dominators(&self) -> &DominatorTree {
        &self.dominators
    }

    pub fn semantic_dominators(&self) -> &DominatorTree {
        &self.semantic_dominators
    }

    pub fn postdominators(&self) -> &PostDominatorTree {
        &self.postdominators
    }

    pub fn continuation(&self, target: BlockId) -> BlockId {
        self.continuations.destination(target)
    }

    /// Returns the semantic destination used by structural control analysis.
    ///
    /// Unlike [`Self::continuation`], this view contracts transparent synthetic
    /// edge blocks even when they anchor Phi inputs. The physical blocks remain
    /// in the CFG so edge-specific copies retain their identity.
    pub fn structural_continuation(&self, target: BlockId) -> BlockId {
        self.structural_continuations.destination(target)
    }
}

#[derive(Debug, Clone)]
pub struct ControlContinuations {
    destinations: BTreeMap<BlockId, BlockId>,
}

impl ControlContinuations {
    pub fn analyze(cfg: &CFG) -> Self {
        let boundaries = cfg
            .blocks
            .values()
            .flat_map(|block| &block.insns)
            .filter(|instruction| instruction.insn_type == InsnType::Phi)
            .flat_map(|instruction| {
                instruction
                    .payload
                    .phi_edges
                    .iter()
                    .map(|(predecessor, _)| *predecessor)
            })
            .collect::<BTreeSet<_>>();
        Self::preserving(cfg, &boundaries)
    }

    pub fn preserving(cfg: &CFG, boundaries: &BTreeSet<BlockId>) -> Self {
        let destinations = cfg
            .block_ids()
            .into_iter()
            .map(|target| (target, Self::find_destination(cfg, boundaries, target)))
            .collect();
        Self { destinations }
    }

    fn find_destination(
        cfg: &CFG,
        phi_predecessors: &BTreeSet<BlockId>,
        target: BlockId,
    ) -> BlockId {
        let mut current = target;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            let Some(block) = cfg.block(current) else {
                break;
            };
            if !block.synthetic
                || phi_predecessors.contains(&current)
                || cfg
                    .incoming_edges(current)
                    .iter()
                    .any(|(_, kind)| kind.is_exception())
                || cfg
                    .successors_with_kind(current)
                    .iter()
                    .any(|(_, kind)| kind.is_exception())
                || !block.insns.iter().all(|instruction| {
                    matches!(instruction.insn_type, InsnType::Nop | InsnType::Goto)
                })
            {
                break;
            }
            let successors = cfg.normal_successors(current).collect::<Vec<_>>();
            let [successor] = successors.as_slice() else {
                break;
            };
            current = *successor;
        }
        current
    }

    pub fn destination(&self, target: BlockId) -> BlockId {
        self.destinations.get(&target).copied().unwrap_or(target)
    }
}
