//! Dominator Tree computation
//!
//! This module provides dominator tree computation for CFG analysis,
//! used by region ownership and semantic scheduling.

use crate::ir::{BlockId, EdgeKind, CFG};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DominanceError {
    MissingEntry(BlockId),
    MissingTopology(BlockId),
    InconsistentEdge { source: BlockId, target: BlockId },
    InvalidTraversal(BlockId),
    MissingDominator(BlockId),
    Unreachable(Vec<BlockId>),
}

impl std::fmt::Display for DominanceError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingEntry(entry) => write!(formatter, "dominance entry {entry} is absent"),
            Self::MissingTopology(block) => {
                write!(formatter, "dominance topology is missing block {block}")
            }
            Self::InconsistentEdge { source, target } => write!(
                formatter,
                "dominance topology contains an inconsistent edge {source} -> {target}"
            ),
            Self::InvalidTraversal(block) => {
                write!(formatter, "dominance traversal is malformed at {block}")
            }
            Self::MissingDominator(block) => {
                write!(formatter, "dominance algorithm did not resolve {block}")
            }
            Self::Unreachable(blocks) => {
                write!(
                    formatter,
                    "dominance topology has unreachable blocks {blocks:?}"
                )
            }
        }
    }
}

impl std::error::Error for DominanceError {}

/// Dominator Tree structure
#[derive(Debug, Clone)]
pub struct DominatorTree {
    /// Immediate dominator for each node
    /// idom[n] = immediate dominator of n
    idom: BTreeMap<BlockId, BlockId>,
    /// Children in dominator tree
    /// children[n] = nodes immediately dominated by n
    children: BTreeMap<BlockId, Vec<BlockId>>,
    /// Entry node (root of dominator tree)
    entry: BlockId,
    nodes: BTreeSet<BlockId>,
}

impl DominatorTree {
    /// Compute exact dominance over every CFG edge using Lengauer-Tarjan.
    pub fn compute(cfg: &CFG) -> Result<Self, DominanceError> {
        let entry = cfg.entry;
        let blocks: Vec<BlockId> = cfg.block_ids();
        let predecessors = cfg.predecessor_snapshot();
        Self::compute_with_predecessors(cfg, entry, blocks, &predecessors)
    }

    /// Compute a dominator tree for an explicit topology snapshot.
    ///
    /// Structuring keeps original block bodies after removing graph-topology
    /// nodes, so callers can pass only the live graph nodes and a cached
    /// predecessor snapshot to avoid scanning preserved-but-dead blocks.
    pub fn compute_with_predecessors(
        cfg: &CFG,
        entry: BlockId,
        blocks: Vec<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<Self, DominanceError> {
        Self::compute_in(cfg, entry, blocks, predecessors)
    }

    /// Compute a dominance forest over ordinary control flow. A synthetic root
    /// connects the method entry and exception-dispatch entries that ordinary
    /// control flow cannot reach from the method entry.
    pub fn compute_normal(
        cfg: &CFG,
        mut blocks: Vec<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<Self, DominanceError> {
        let block_set = blocks.iter().copied().collect::<BTreeSet<_>>();
        let virtual_root = BlockId::INVALID;
        if block_set.contains(&virtual_root) {
            return Err(DominanceError::MissingEntry(virtual_root));
        }
        let mut normal_predecessors = blocks
            .iter()
            .copied()
            .map(|block| {
                let sources = predecessors
                    .get(&block)
                    .cloned()
                    .ok_or(DominanceError::MissingTopology(block))?;
                Ok((block, sources))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let mut successors = blocks
            .iter()
            .copied()
            .map(|block| {
                let targets = cfg
                    .successors_with_kind(block)
                    .iter()
                    .filter(|(_, kind)| *kind != EdgeKind::Exception)
                    .map(|(target, _)| *target)
                    .filter(|target| block_set.contains(target))
                    .collect();
                (block, targets)
            })
            .collect::<BTreeMap<_, _>>();
        let roots = NormalFlowEntries::discover(cfg, &block_set, &successors)?;
        for root in &roots {
            normal_predecessors
                .get_mut(root)
                .ok_or(DominanceError::MissingTopology(*root))?
                .push(virtual_root);
        }
        normal_predecessors.insert(virtual_root, Vec::new());
        successors.insert(virtual_root, roots.into_iter().collect());
        blocks.push(virtual_root);
        Self::compute_topology(virtual_root, blocks, &normal_predecessors, &successors)
    }

    fn compute_in(
        cfg: &CFG,
        entry: BlockId,
        blocks: Vec<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<Self, DominanceError> {
        let block_set = blocks.iter().copied().collect::<BTreeSet<_>>();
        let successors = blocks
            .iter()
            .copied()
            .map(|block| {
                let targets = cfg
                    .successors_with_kind(block)
                    .iter()
                    .map(|(target, _)| *target)
                    .filter(|target| block_set.contains(target))
                    .collect();
                (block, targets)
            })
            .collect();
        Self::compute_topology(entry, blocks, predecessors, &successors)
    }

    pub(crate) fn compute_topology(
        entry: BlockId,
        blocks: Vec<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
        successors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<Self, DominanceError> {
        Self::compute_topology_with_policy(entry, blocks, predecessors, successors, true)
    }

    pub(crate) fn compute_reachable_topology(
        entry: BlockId,
        blocks: Vec<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
        successors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<Self, DominanceError> {
        Self::compute_topology_with_policy(entry, blocks, predecessors, successors, false)
    }

    fn compute_topology_with_policy(
        entry: BlockId,
        blocks: Vec<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
        successors: &BTreeMap<BlockId, Vec<BlockId>>,
        require_all_reachable: bool,
    ) -> Result<Self, DominanceError> {
        let topology = Topology::new(blocks, predecessors, successors)?;
        if !topology.nodes.contains(&entry) {
            return Err(DominanceError::MissingEntry(entry));
        }

        let traversal = DepthFirstNumbering::compute(entry, &topology.successors)?;
        if require_all_reachable && traversal.indices.len() != topology.nodes.len() {
            let reachable = traversal.indices.keys().copied().collect::<BTreeSet<_>>();
            let unreachable = topology.nodes.difference(&reachable).copied().collect();
            return Err(DominanceError::Unreachable(unreachable));
        }

        let mut algorithm = LengauerTarjan::new(&traversal, &topology.predecessors);
        let immediate = algorithm.compute()?;
        let nodes = traversal.indices.keys().copied().collect::<BTreeSet<_>>();
        let idom = immediate
            .into_iter()
            .filter_map(|(node, parent)| parent.map(|parent| (node, parent)))
            .collect::<BTreeMap<_, _>>();
        let mut children = nodes
            .iter()
            .copied()
            .map(|node| (node, Vec::new()))
            .collect::<BTreeMap<_, _>>();
        for (&node, &parent) in &idom {
            let children = children
                .get_mut(&parent)
                .ok_or(DominanceError::MissingDominator(parent))?;
            children.push(node);
        }
        for children in children.values_mut() {
            children.sort();
        }

        Ok(Self {
            idom,
            children,
            entry,
            nodes,
        })
    }

    /// Get immediate dominator of a node
    pub fn idom(&self, node: BlockId) -> Option<BlockId> {
        self.idom.get(&node).copied()
    }

    /// Get children of a node in dominator tree
    pub fn children(&self, node: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.children
            .get(&node)
            .into_iter()
            .flat_map(|children| children.iter().copied())
    }

    pub fn contains(&self, node: BlockId) -> bool {
        self.nodes.contains(&node)
    }

    /// Get all nodes dominated by the given node (including itself)
    pub fn dominated_by(&self, node: BlockId) -> BTreeSet<BlockId> {
        if !self.nodes.contains(&node) {
            return BTreeSet::new();
        }
        let mut result = BTreeSet::new();
        let mut pending = vec![node];
        while let Some(current) = pending.pop() {
            if result.insert(current) {
                pending.extend(self.children(current));
            }
        }
        result
    }

    /// Check if `dom` dominates `node`
    pub fn dominates(&self, dom: BlockId, node: BlockId) -> bool {
        if !self.nodes.contains(&dom) || !self.nodes.contains(&node) {
            return false;
        }
        if dom == node {
            return true;
        }
        let mut current = node;
        while let Some(idom) = self.idom(current) {
            if idom == dom {
                return true;
            }
            if idom == current {
                // Reached entry or cycle
                break;
            }
            current = idom;
        }
        false
    }

    /// Check if `sdom` strictly dominates `node` (dominates but not equal)
    pub fn strictly_dominates(&self, sdom: BlockId, node: BlockId) -> bool {
        sdom != node && self.dominates(sdom, node)
    }

    /// Get entry node
    pub fn entry(&self) -> BlockId {
        self.entry
    }

    /// Get all nodes in dominator tree preorder
    pub fn preorder(&self) -> Vec<BlockId> {
        let mut result = Vec::new();
        let mut pending = vec![self.entry];
        while let Some(node) = pending.pop() {
            result.push(node);
            let mut children = self.children(node).collect::<Vec<_>>();
            children.reverse();
            pending.extend(children);
        }
        result
    }

    /// Get all nodes in dominator tree postorder
    pub fn postorder(&self) -> Vec<BlockId> {
        let mut result = Vec::new();
        let mut pending = vec![(self.entry, false)];
        while let Some((node, exiting)) = pending.pop() {
            if exiting {
                result.push(node);
                continue;
            }
            pending.push((node, true));
            let mut children = self.children(node).collect::<Vec<_>>();
            children.reverse();
            pending.extend(children.into_iter().map(|child| (child, false)));
        }
        result
    }
}

struct NormalFlowEntries;

impl NormalFlowEntries {
    fn discover(
        cfg: &CFG,
        blocks: &BTreeSet<BlockId>,
        successors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<BTreeSet<BlockId>, DominanceError> {
        let reachable = Self::reachable_from(cfg.entry, successors)?;
        let mut entries = BTreeSet::from([cfg.entry]);
        for source in blocks {
            entries.extend(
                cfg.successors_with_kind(*source)
                    .iter()
                    .filter(|(target, kind)| {
                        *kind == EdgeKind::Exception
                            && blocks.contains(target)
                            && !reachable.contains(target)
                    })
                    .map(|(target, _)| *target),
            );
        }
        Ok(entries)
    }

    fn reachable_from(
        entry: BlockId,
        successors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<BTreeSet<BlockId>, DominanceError> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !reachable.insert(block) {
                continue;
            }
            pending.extend(
                successors
                    .get(&block)
                    .ok_or(DominanceError::MissingTopology(block))?,
            );
        }
        Ok(reachable)
    }
}

struct Topology {
    nodes: BTreeSet<BlockId>,
    predecessors: BTreeMap<BlockId, Vec<BlockId>>,
    successors: BTreeMap<BlockId, Vec<BlockId>>,
}

impl Topology {
    fn new(
        blocks: Vec<BlockId>,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
        successors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<Self, DominanceError> {
        let nodes = blocks.into_iter().collect::<BTreeSet<_>>();
        let mut induced_successors = BTreeMap::new();
        let mut induced_predecessors = BTreeMap::new();
        for node in &nodes {
            let targets = successors
                .get(node)
                .ok_or(DominanceError::MissingTopology(*node))?
                .iter()
                .copied()
                .filter(|target| nodes.contains(target))
                .collect::<BTreeSet<_>>();
            induced_successors.insert(*node, targets.into_iter().collect::<Vec<_>>());

            let sources = predecessors
                .get(node)
                .ok_or(DominanceError::MissingTopology(*node))?
                .iter()
                .copied()
                .filter(|source| nodes.contains(source))
                .collect::<BTreeSet<_>>();
            induced_predecessors.insert(*node, sources.into_iter().collect::<Vec<_>>());
        }
        for (&source, targets) in &induced_successors {
            for target in targets {
                if !induced_predecessors
                    .get(target)
                    .is_some_and(|sources| sources.binary_search(&source).is_ok())
                {
                    return Err(DominanceError::InconsistentEdge {
                        source,
                        target: *target,
                    });
                }
            }
        }
        for (&target, sources) in &induced_predecessors {
            for source in sources {
                if !induced_successors
                    .get(source)
                    .is_some_and(|targets| targets.binary_search(&target).is_ok())
                {
                    return Err(DominanceError::InconsistentEdge {
                        source: *source,
                        target,
                    });
                }
            }
        }
        Ok(Self {
            nodes,
            predecessors: induced_predecessors,
            successors: induced_successors,
        })
    }
}

struct DepthFirstNumbering {
    vertices: Vec<BlockId>,
    indices: BTreeMap<BlockId, usize>,
    parents: Vec<Option<usize>>,
}

impl DepthFirstNumbering {
    fn compute(
        entry: BlockId,
        successors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Result<Self, DominanceError> {
        let mut vertices = vec![entry];
        let mut indices = BTreeMap::from([(entry, 0)]);
        let mut parents = vec![None];
        let mut pending = vec![(entry, 0usize)];
        while let Some((node, next_child)) = pending.last_mut() {
            let targets = successors
                .get(node)
                .ok_or(DominanceError::InvalidTraversal(*node))?;
            if *next_child == targets.len() {
                pending.pop();
                continue;
            }
            let target = targets[*next_child];
            *next_child += 1;
            if indices.contains_key(&target) {
                continue;
            }
            let parent = indices[node];
            let index = vertices.len();
            vertices.push(target);
            indices.insert(target, index);
            parents.push(Some(parent));
            pending.push((target, 0));
        }
        Ok(Self {
            vertices,
            indices,
            parents,
        })
    }
}

struct LengauerTarjan {
    vertices: Vec<BlockId>,
    predecessors: Vec<Vec<usize>>,
    parents: Vec<Option<usize>>,
    semi: Vec<usize>,
    labels: Vec<usize>,
    ancestors: Vec<Option<usize>>,
    buckets: Vec<Vec<usize>>,
    immediate: Vec<Option<usize>>,
}

impl LengauerTarjan {
    fn new(
        traversal: &DepthFirstNumbering,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
    ) -> Self {
        let count = traversal.vertices.len();
        let predecessor_indices = traversal
            .vertices
            .iter()
            .map(|node| {
                predecessors[node]
                    .iter()
                    .filter_map(|source| traversal.indices.get(source).copied())
                    .collect()
            })
            .collect();
        Self {
            vertices: traversal.vertices.clone(),
            predecessors: predecessor_indices,
            parents: traversal.parents.clone(),
            semi: (0..count).collect(),
            labels: (0..count).collect(),
            ancestors: vec![None; count],
            buckets: vec![Vec::new(); count],
            immediate: vec![None; count],
        }
    }

    fn compute(&mut self) -> Result<BTreeMap<BlockId, Option<BlockId>>, DominanceError> {
        for node in (1..self.vertices.len()).rev() {
            for predecessor in self.predecessors[node].clone() {
                let representative = self.evaluate(predecessor)?;
                self.semi[node] = self.semi[node].min(self.semi[representative]);
            }
            self.buckets[self.semi[node]].push(node);
            let parent =
                self.parents[node].ok_or(DominanceError::InvalidTraversal(self.vertices[node]))?;
            self.ancestors[node] = Some(parent);
            for member in std::mem::take(&mut self.buckets[parent]) {
                let representative = self.evaluate(member)?;
                self.immediate[member] = Some(if self.semi[representative] < self.semi[member] {
                    representative
                } else {
                    parent
                });
            }
        }
        for node in 1..self.vertices.len() {
            if self.immediate[node] != Some(self.semi[node]) {
                let provisional = self.immediate[node]
                    .ok_or(DominanceError::MissingDominator(self.vertices[node]))?;
                self.immediate[node] = self.immediate[provisional];
            }
        }
        Ok(self
            .vertices
            .iter()
            .enumerate()
            .map(|(index, node)| {
                (
                    *node,
                    self.immediate[index].map(|parent| self.vertices[parent]),
                )
            })
            .collect())
    }

    fn evaluate(&mut self, node: usize) -> Result<usize, DominanceError> {
        if self.ancestors[node].is_none() {
            return Ok(self.labels[node]);
        }
        let mut path = Vec::new();
        let mut current = node;
        while let Some(parent) = self.ancestors[current] {
            if self.ancestors[parent].is_none() {
                break;
            }
            path.push(current);
            current = parent;
        }
        for member in path.into_iter().rev() {
            let parent = self.ancestors[member]
                .ok_or(DominanceError::InvalidTraversal(self.vertices[member]))?;
            if self.semi[self.labels[parent]] < self.semi[self.labels[member]] {
                self.labels[member] = self.labels[parent];
            }
            self.ancestors[member] = self.ancestors[parent];
        }
        Ok(self.labels[node])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::block::Block;
    use crate::ir::cfg::EdgeKind;

    fn make_cfg_diamond() -> CFG {
        // Diamond pattern:
        //     0 (entry)
        //    / \
        //   1   2
        //    \ /
        //     3
        let mut cfg = CFG::new("diamond");
        cfg.add_block(Block::new(BlockId::new(0)));
        cfg.add_block(Block::new(BlockId::new(1)));
        cfg.add_block(Block::new(BlockId::new(2)));
        cfg.add_block(Block::new(BlockId::new(3)));

        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::True);
        cfg.add_edge(BlockId::new(0), BlockId::new(2), EdgeKind::False);
        cfg.add_edge(BlockId::new(1), BlockId::new(3), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(3), EdgeKind::Normal);

        cfg.entry = BlockId::new(0);
        cfg
    }

    fn make_cfg_while_loop() -> CFG {
        // While loop:
        //   0 (entry)
        //   |
        //   1 (header) <----
        //  / \              |
        // 2   3 (body) -----
        //
        let mut cfg = CFG::new("while");
        cfg.add_block(Block::new(BlockId::new(0)));
        cfg.add_block(Block::new(BlockId::new(1)));
        cfg.add_block(Block::new(BlockId::new(2)));
        cfg.add_block(Block::new(BlockId::new(3)));

        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::False); // exit
        cfg.add_edge(BlockId::new(1), BlockId::new(3), EdgeKind::True); // body
        cfg.add_edge(BlockId::new(3), BlockId::new(1), EdgeKind::Normal); // back edge

        cfg.entry = BlockId::new(0);
        cfg
    }

    fn make_cfg_nested_if() -> CFG {
        // Nested if:
        //      0
        //     / \
        //    1   4
        //   / \
        //  2   3
        //   \ /
        //    4
        let mut cfg = CFG::new("nested_if");
        cfg.add_block(Block::new(BlockId::new(0)));
        cfg.add_block(Block::new(BlockId::new(1)));
        cfg.add_block(Block::new(BlockId::new(2)));
        cfg.add_block(Block::new(BlockId::new(3)));
        cfg.add_block(Block::new(BlockId::new(4)));

        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::True);
        cfg.add_edge(BlockId::new(0), BlockId::new(4), EdgeKind::False);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::True);
        cfg.add_edge(BlockId::new(1), BlockId::new(3), EdgeKind::False);
        cfg.add_edge(BlockId::new(2), BlockId::new(4), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(4), EdgeKind::Normal);

        cfg.entry = BlockId::new(0);
        cfg
    }

    #[test]
    fn test_domtree_diamond() {
        let cfg = make_cfg_diamond();
        let dom = DominatorTree::compute(&cfg).unwrap();

        // 0 dominates all
        assert!(dom.dominates(BlockId::new(0), BlockId::new(0)));
        assert!(dom.dominates(BlockId::new(0), BlockId::new(1)));
        assert!(dom.dominates(BlockId::new(0), BlockId::new(2)));
        assert!(dom.dominates(BlockId::new(0), BlockId::new(3)));

        // 1 and 2 only dominate themselves
        assert!(dom.dominates(BlockId::new(1), BlockId::new(1)));
        assert!(!dom.dominates(BlockId::new(1), BlockId::new(3)));
        assert!(dom.dominates(BlockId::new(2), BlockId::new(2)));
        assert!(!dom.dominates(BlockId::new(2), BlockId::new(3)));

        // idom of 3 is 0 (not 1 or 2)
        assert_eq!(dom.idom(BlockId::new(3)), Some(BlockId::new(0)));
    }

    #[test]
    fn test_domtree_while_loop() {
        let cfg = make_cfg_while_loop();
        let dom = DominatorTree::compute(&cfg).unwrap();

        // 0 dominates all
        assert!(dom.dominates(BlockId::new(0), BlockId::new(1)));
        assert!(dom.dominates(BlockId::new(0), BlockId::new(2)));
        assert!(dom.dominates(BlockId::new(0), BlockId::new(3)));

        // 1 (header) dominates 2 and 3
        assert!(dom.dominates(BlockId::new(1), BlockId::new(2)));
        assert!(dom.dominates(BlockId::new(1), BlockId::new(3)));

        // idom of 1 is 0
        assert_eq!(dom.idom(BlockId::new(1)), Some(BlockId::new(0)));
        // idom of 3 is 1
        assert_eq!(dom.idom(BlockId::new(3)), Some(BlockId::new(1)));
    }

    #[test]
    fn test_domtree_nested_if() {
        let cfg = make_cfg_nested_if();
        let dom = DominatorTree::compute(&cfg).unwrap();

        // 0 dominates all
        for i in 0..5 {
            assert!(dom.dominates(BlockId::new(0), BlockId::new(i)));
        }

        // 1 dominates 2 and 3
        assert!(dom.dominates(BlockId::new(1), BlockId::new(2)));
        assert!(dom.dominates(BlockId::new(1), BlockId::new(3)));
        // 1 does not dominate 4 (multiple paths to 4)
        assert!(!dom.dominates(BlockId::new(1), BlockId::new(4)));
    }

    #[test]
    fn test_dominated_by() {
        let cfg = make_cfg_nested_if();
        let dom = DominatorTree::compute(&cfg).unwrap();

        // Nodes dominated by 1
        let dom_by_1 = dom.dominated_by(BlockId::new(1));
        assert!(dom_by_1.contains(&BlockId::new(1)));
        assert!(dom_by_1.contains(&BlockId::new(2)));
        assert!(dom_by_1.contains(&BlockId::new(3)));
        assert!(!dom_by_1.contains(&BlockId::new(4)));
    }

    #[test]
    fn normal_flow_ignores_exception_shortcuts_and_back_edges() {
        let mut cfg = CFG::new("normal_flow_with_exception_edges");
        for id in 0..3 {
            cfg.add_block(Block::new(BlockId::new(id)));
        }
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(0), BlockId::new(2), EdgeKind::Exception);
        cfg.add_edge(BlockId::new(2), BlockId::new(1), EdgeKind::Exception);

        let predecessors = cfg.normal_predecessor_snapshot();
        let dom = DominatorTree::compute_normal(&cfg, cfg.block_ids(), &predecessors).unwrap();
        assert_eq!(dom.idom(BlockId::new(2)), Some(BlockId::new(1)));
    }

    #[test]
    fn test_preorder_postorder() {
        let cfg = make_cfg_diamond();
        let dom = DominatorTree::compute(&cfg).unwrap();

        let pre = dom.preorder();
        let post = dom.postorder();

        // Entry should be first in preorder, last in postorder
        assert_eq!(pre[0], BlockId::new(0));
        assert_eq!(*post.last().unwrap(), BlockId::new(0));

        // Both should have all nodes
        assert_eq!(pre.len(), 4);
        assert_eq!(post.len(), 4);
    }
}
