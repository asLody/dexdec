//! Post-dominance as dominance over the reversed normal-flow graph.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BlockId, CFG};

use super::{DominanceError, DominatorTree};

#[derive(Debug, Clone)]
pub struct PostDominatorTree {
    tree: DominatorTree,
}

impl PostDominatorTree {
    pub fn compute(cfg: &CFG) -> Result<Self, DominanceError> {
        let virtual_exit = BlockId::INVALID;
        let mut nodes = cfg.block_ids();
        nodes.push(virtual_exit);

        let mut predecessors = nodes
            .iter()
            .copied()
            .map(|node| (node, Vec::new()))
            .collect::<BTreeMap<_, _>>();
        let mut successors = predecessors.clone();
        let mut exits = Vec::new();

        for source in cfg.block_ids() {
            let targets = cfg.normal_successors(source).collect::<Vec<_>>();
            if targets.is_empty() {
                exits.push(source);
                predecessors.entry(source).or_default().push(virtual_exit);
                continue;
            }
            for target in targets {
                successors.entry(target).or_default().push(source);
                predecessors.entry(source).or_default().push(target);
            }
        }
        successors.insert(virtual_exit, exits);
        for edges in predecessors.values_mut().chain(successors.values_mut()) {
            edges.sort();
            edges.dedup();
        }

        Ok(Self {
            tree: DominatorTree::compute_reachable_topology(
                virtual_exit,
                nodes,
                &predecessors,
                &successors,
            )?,
        })
    }

    pub fn nearest_common(&self, entries: &[BlockId]) -> Option<BlockId> {
        let mut candidate = *entries.first()?;
        loop {
            if candidate != BlockId::INVALID
                && entries
                    .iter()
                    .all(|entry| self.tree.dominates(candidate, *entry))
            {
                return Some(candidate);
            }
            candidate = self.tree.idom(candidate)?;
        }
    }

    /// Rank concrete convergence points shared by at least `minimum` entries.
    ///
    /// Unlike `nearest_common`, this does not require abrupt paths to share a
    /// concrete postdominator. Candidates covering more entries rank first;
    /// ties prefer the point nearest to the entries rather than the virtual
    /// method exit.
    pub fn convergences(&self, entries: &[BlockId], minimum: usize) -> Vec<BlockId> {
        let mut coverage = BTreeMap::<BlockId, usize>::new();
        for entry in entries.iter().copied().collect::<BTreeSet<_>>() {
            let mut current = Some(entry);
            let mut visited = BTreeSet::new();
            while let Some(node) = current {
                if node == BlockId::INVALID || !visited.insert(node) {
                    break;
                }
                *coverage.entry(node).or_default() += 1;
                current = self.tree.idom(node);
            }
        }
        let mut candidates = coverage
            .into_iter()
            .filter(|(node, count)| *node != BlockId::INVALID && *count >= minimum)
            .map(|(node, count)| (node, count, self.depth(node)))
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(node, count, depth)| {
            (std::cmp::Reverse(*count), std::cmp::Reverse(*depth), *node)
        });
        candidates.into_iter().map(|(node, _, _)| node).collect()
    }

    pub fn immediate(&self, node: BlockId) -> Option<BlockId> {
        self.tree
            .idom(node)
            .filter(|postdominator| *postdominator != BlockId::INVALID)
    }

    pub fn postdominates(&self, postdominator: BlockId, node: BlockId) -> bool {
        postdominator != BlockId::INVALID && self.tree.dominates(postdominator, node)
    }

    fn depth(&self, node: BlockId) -> usize {
        let mut depth = 0usize;
        let mut current = node;
        let mut visited = BTreeSet::new();
        while current != BlockId::INVALID && visited.insert(current) {
            let Some(parent) = self.tree.idom(current) else {
                break;
            };
            depth += 1;
            current = parent;
        }
        depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, EdgeKind};

    #[test]
    fn partial_convergence_ignores_an_abrupt_arm() {
        let mut cfg = CFG::new("partial_convergence");
        for id in 0..=6 {
            cfg.add_block(Block::new(id));
        }
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(0), BlockId::new(2), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(0), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(4), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(4), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(5), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(4), BlockId::new(6), EdgeKind::Normal);

        let postdominators = PostDominatorTree::compute(&cfg).expect("postdominator tree");
        let entries = [BlockId::new(1), BlockId::new(2), BlockId::new(3)];

        assert_eq!(postdominators.nearest_common(&entries), None);
        assert_eq!(
            postdominators.convergences(&entries, 2).first().copied(),
            Some(BlockId::new(4))
        );
    }
}
