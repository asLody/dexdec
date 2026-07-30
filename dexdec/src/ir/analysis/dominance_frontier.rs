//! Dominance-frontier computation over the canonical dominator tree.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BlockId, CFG};

use super::{DominanceError, DominatorTree};

#[derive(Debug, Clone)]
pub struct DominanceFrontier {
    frontiers: BTreeMap<BlockId, BTreeSet<BlockId>>,
}

impl DominanceFrontier {
    pub fn compute(cfg: &CFG, dominators: &DominatorTree) -> Result<Self, DominanceError> {
        for block in cfg.block_ids() {
            if !dominators.contains(block) {
                return Err(DominanceError::MissingTopology(block));
            }
        }
        let mut frontiers = cfg
            .block_ids()
            .into_iter()
            .map(|block| (block, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();

        for block in cfg.block_ids() {
            for successor in cfg.successors(block) {
                if dominators.idom(successor) != Some(block) {
                    frontiers
                        .get_mut(&block)
                        .ok_or(DominanceError::MissingTopology(block))?
                        .insert(successor);
                }
            }
        }

        for block in dominators.postorder() {
            for child in dominators.children(block) {
                let child_frontier = frontiers
                    .get(&child)
                    .ok_or(DominanceError::MissingTopology(child))?
                    .iter()
                    .copied()
                    .collect::<Vec<_>>();
                for boundary in child_frontier {
                    if dominators.idom(boundary) != Some(block) {
                        frontiers
                            .get_mut(&block)
                            .ok_or(DominanceError::MissingTopology(block))?
                            .insert(boundary);
                    }
                }
            }
        }
        Ok(Self { frontiers })
    }

    pub fn frontier(&self, block: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.frontiers
            .get(&block)
            .into_iter()
            .flat_map(|frontier| frontier.iter().copied())
    }

    pub fn in_frontier(&self, block: BlockId, of: BlockId) -> bool {
        self.frontiers
            .get(&of)
            .is_some_and(|frontier| frontier.contains(&block))
    }
}
