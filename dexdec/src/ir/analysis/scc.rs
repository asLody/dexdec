//! Strongly connected components of the normal-flow graph.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{BlockId, CFG};

#[derive(Debug, Clone)]
pub struct StrongComponent {
    pub nodes: BTreeSet<BlockId>,
    pub entries: BTreeSet<BlockId>,
    pub cyclic: bool,
}

#[derive(Debug, Clone, Default)]
pub struct StrongComponents {
    components: Vec<StrongComponent>,
    ownership: BTreeMap<BlockId, usize>,
}

impl StrongComponents {
    pub fn analyze(cfg: &CFG, nodes: impl IntoIterator<Item = BlockId>) -> Self {
        Self::analyze_with(cfg, nodes, false)
    }

    pub fn analyze_semantic(cfg: &CFG, nodes: impl IntoIterator<Item = BlockId>) -> Self {
        Self::analyze_with(cfg, nodes, true)
    }

    fn analyze_with(
        cfg: &CFG,
        nodes: impl IntoIterator<Item = BlockId>,
        include_exceptions: bool,
    ) -> Self {
        let universe = nodes.into_iter().collect::<BTreeSet<_>>();
        let predecessors = if include_exceptions {
            cfg.predecessor_snapshot()
        } else {
            cfg.normal_predecessor_snapshot()
        };
        let finish_order = Self::finish_order(cfg, &universe, include_exceptions);
        let mut assigned = BTreeSet::new();
        let mut node_sets = Vec::new();
        for root in finish_order.into_iter().rev() {
            if assigned.contains(&root) {
                continue;
            }
            let mut component = BTreeSet::new();
            let mut pending = vec![root];
            while let Some(node) = pending.pop() {
                if !universe.contains(&node) || !assigned.insert(node) {
                    continue;
                }
                component.insert(node);
                pending.extend(predecessors.get(&node).into_iter().flatten().copied());
            }
            node_sets.push(component);
        }

        let mut components = node_sets
            .into_iter()
            .map(|nodes| {
                let entries = nodes
                    .iter()
                    .copied()
                    .filter(|node| {
                        *node == cfg.entry
                            || predecessors
                                .get(node)
                                .into_iter()
                                .flatten()
                                .any(|predecessor| !nodes.contains(predecessor))
                    })
                    .collect();
                let cyclic = nodes.len() > 1
                    || nodes.iter().copied().any(|node| {
                        Self::successors(cfg, node, include_exceptions)
                            .any(|successor| successor == node)
                    });
                StrongComponent {
                    nodes,
                    entries,
                    cyclic,
                }
            })
            .collect::<Vec<_>>();
        components.sort_by_key(|component| component.nodes.first().copied());
        let ownership = components
            .iter()
            .enumerate()
            .flat_map(|(index, component)| {
                component
                    .nodes
                    .iter()
                    .copied()
                    .map(move |node| (node, index))
            })
            .collect();
        Self {
            components,
            ownership,
        }
    }

    pub fn components(&self) -> &[StrongComponent] {
        &self.components
    }

    pub fn component_of(&self, block: BlockId) -> Option<&StrongComponent> {
        self.ownership
            .get(&block)
            .and_then(|index| self.components.get(*index))
    }

    pub fn is_acyclic(&self) -> bool {
        self.components.iter().all(|component| !component.cyclic)
    }

    fn finish_order(
        cfg: &CFG,
        universe: &BTreeSet<BlockId>,
        include_exceptions: bool,
    ) -> Vec<BlockId> {
        let mut visited = BTreeSet::new();
        let mut order = Vec::with_capacity(universe.len());
        for root in universe.iter().copied() {
            if visited.contains(&root) {
                continue;
            }
            let mut stack = vec![(root, false)];
            while let Some((node, exiting)) = stack.pop() {
                if exiting {
                    order.push(node);
                    continue;
                }
                if !universe.contains(&node) || !visited.insert(node) {
                    continue;
                }
                stack.push((node, true));
                let mut successors = Self::successors(cfg, node, include_exceptions)
                    .filter(|successor| universe.contains(successor))
                    .collect::<Vec<_>>();
                successors.sort_by(|left, right| right.cmp(left));
                stack.extend(successors.into_iter().map(|successor| (successor, false)));
            }
        }
        order
    }

    fn successors(
        cfg: &CFG,
        node: BlockId,
        include_exceptions: bool,
    ) -> impl Iterator<Item = BlockId> + '_ {
        cfg.successors_with_kind(node)
            .iter()
            .filter(move |(_, kind)| include_exceptions || !kind.is_exception())
            .map(|(target, _)| *target)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, EdgeKind};

    #[test]
    fn semantic_component_includes_a_handler_that_rejoins_the_latch() {
        let mut cfg = CFG::new("handler_loop");
        for id in 0..=5 {
            cfg.add_block(Block::new(id));
        }
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::True);
        cfg.add_edge(BlockId::new(1), BlockId::new(5), EdgeKind::False);
        cfg.add_edge(BlockId::new(2), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(4), EdgeKind::Exception);
        cfg.add_edge(BlockId::new(4), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(1), EdgeKind::Normal);

        let normal = StrongComponents::analyze(&cfg, cfg.block_ids());
        let normal_loop = normal.component_of(BlockId::new(1)).unwrap();
        assert_eq!(normal_loop.entries.len(), 2);

        let semantic = StrongComponents::analyze_semantic(&cfg, cfg.block_ids());
        let semantic_loop = semantic.component_of(BlockId::new(1)).unwrap();
        assert_eq!(semantic_loop.entries, BTreeSet::from([BlockId::new(1)]));
        assert!(semantic_loop.nodes.contains(&BlockId::new(4)));
    }
}
