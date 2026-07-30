//! Semantic construction for a DEX switch region.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::semantic::SemanticFactory;
use crate::ir::{
    BlockId, EdgeKind, InsnType, RegionId, SemanticFoldError, SemanticFolder, SemanticLabel,
    SemanticLeaveKind, SemanticLoopControl, SemanticNode, SemanticSwitchCase, SemanticVisitor, CFG,
};

use super::{graph_structurer::GraphStructurer, StructureError};

#[derive(Debug, Default)]
struct ArmLabels {
    values: Vec<i32>,
    is_default: bool,
}

#[derive(Debug)]
struct SwitchArm {
    entry: BlockId,
    labels: ArmLabels,
    nodes: BTreeSet<BlockId>,
}

#[derive(Debug)]
struct SwitchPartition {
    selector: crate::ir::InsnArg,
    arms: Vec<SwitchArm>,
    is_structured: bool,
}

#[derive(Debug, Default)]
struct SwitchFallthrough {
    successors: BTreeMap<BlockId, BlockId>,
    predecessors: BTreeMap<BlockId, BlockId>,
    shared_suffixes: BTreeMap<(BlockId, BlockId), BTreeSet<BlockId>>,
}

impl SwitchFallthrough {
    fn analyze(
        cfg: &CFG,
        arms: &[SwitchArm],
        terminal_boundaries: &BTreeSet<BlockId>,
        semantic_entries: &BTreeSet<BlockId>,
    ) -> Option<Self> {
        let entries = arms.iter().map(|arm| arm.entry).collect::<BTreeSet<_>>();
        let mut graph = Self::default();
        for arm in arms {
            let targets = arm
                .nodes
                .iter()
                .copied()
                .flat_map(|source| cfg.normal_successors(source))
                .filter(|target| *target != arm.entry && entries.contains(target))
                .collect::<BTreeSet<_>>();
            if targets.len() > 1 {
                return None;
            }
            let Some(target) = targets.first().copied() else {
                continue;
            };
            if !graph.insert(arm.entry, target) {
                return None;
            }
        }
        for (left_index, left) in arms.iter().enumerate() {
            for right in &arms[left_index + 1..] {
                let shared = left
                    .nodes
                    .intersection(&right.nodes)
                    .copied()
                    .filter(|node| !terminal_boundaries.contains(node))
                    .collect::<BTreeSet<_>>();
                if shared.is_empty() {
                    continue;
                }
                let candidates = [(left, right), (right, left)]
                    .into_iter()
                    .filter(|(upstream, downstream)| {
                        Self::enters(cfg, upstream, &shared)
                            && Self::transparent_prefix(cfg, downstream, &shared, semantic_entries)
                    })
                    .collect::<Vec<_>>();
                let [(upstream, downstream)] = candidates.as_slice() else {
                    return None;
                };
                if !graph.insert(upstream.entry, downstream.entry) {
                    return None;
                }
                graph
                    .shared_suffixes
                    .insert((upstream.entry, downstream.entry), shared);
            }
        }
        graph.is_acyclic(&entries).then_some(graph)
    }

    fn insert(&mut self, source: BlockId, target: BlockId) -> bool {
        match self.successors.get(&source) {
            Some(existing) if *existing != target => return false,
            Some(_) => {}
            None => {
                self.successors.insert(source, target);
            }
        }
        match self.predecessors.get(&target) {
            Some(existing) if *existing != source => false,
            Some(_) => true,
            None => {
                self.predecessors.insert(target, source);
                true
            }
        }
    }

    fn enters(cfg: &CFG, arm: &SwitchArm, shared: &BTreeSet<BlockId>) -> bool {
        arm.nodes.difference(shared).copied().any(|source| {
            cfg.normal_successors(source)
                .any(|target| shared.contains(&target))
        })
    }

    fn transparent_prefix(
        cfg: &CFG,
        arm: &SwitchArm,
        shared: &BTreeSet<BlockId>,
        semantic_entries: &BTreeSet<BlockId>,
    ) -> bool {
        let prefix = arm
            .nodes
            .difference(shared)
            .copied()
            .collect::<BTreeSet<_>>();
        if !prefix.contains(&arm.entry) {
            return true;
        }
        let mut reached = false;
        for node in &prefix {
            if semantic_entries.contains(node) {
                return false;
            }
            let Some(block) = cfg.block(*node) else {
                return false;
            };
            if !block
                .insns
                .iter()
                .all(|instruction| matches!(instruction.insn_type, InsnType::Nop | InsnType::Goto))
            {
                return false;
            }
            for successor in cfg.normal_successors(*node) {
                if shared.contains(&successor) {
                    reached = true;
                } else if !prefix.contains(&successor) {
                    return false;
                }
            }
        }
        reached
    }

    fn partition(&self, arms: &mut [SwitchArm]) {
        let indices = arms
            .iter()
            .enumerate()
            .map(|(index, arm)| (arm.entry, index))
            .collect::<BTreeMap<_, _>>();
        for ((upstream, _), shared) in &self.shared_suffixes {
            if let Some(index) = indices.get(upstream).copied() {
                arms[index].nodes = arms[index].nodes.difference(shared).copied().collect();
            }
        }
    }

    fn is_acyclic(&self, entries: &BTreeSet<BlockId>) -> bool {
        let mut visited = BTreeSet::new();
        for entry in entries {
            let mut chain = BTreeSet::new();
            let mut current = *entry;
            while chain.insert(current) {
                if !visited.insert(current) {
                    break;
                }
                let Some(next) = self.successors.get(&current).copied() else {
                    break;
                };
                current = next;
            }
            if self.successors.contains_key(&current) && chain.contains(&current) {
                return false;
            }
        }
        true
    }

    fn order(&self, arms: &[SwitchArm]) -> Option<Vec<BlockId>> {
        let by_entry = arms
            .iter()
            .map(|arm| (arm.entry, arm))
            .collect::<BTreeMap<_, _>>();
        let mut heads = arms
            .iter()
            .filter(|arm| !self.predecessors.contains_key(&arm.entry))
            .collect::<Vec<_>>();
        heads.sort_by_key(|arm| {
            (
                arm.labels.is_default,
                arm.labels.values.iter().copied().min().unwrap_or(i32::MAX),
                arm.entry,
            )
        });
        let mut ordered = Vec::with_capacity(arms.len());
        let mut visited = BTreeSet::new();
        for head in heads {
            let mut current = head.entry;
            loop {
                if !visited.insert(current) {
                    return None;
                }
                ordered.push(current);
                let Some(next) = self.successors.get(&current).copied() else {
                    break;
                };
                if !by_entry.contains_key(&next) {
                    return None;
                }
                current = next;
            }
        }
        (ordered.len() == arms.len()).then_some(ordered)
    }
}

pub(super) struct SwitchControlDomain {
    region: RegionId,
    label: SemanticLabel,
    active: usize,
    bound: usize,
}

impl SwitchControlDomain {
    pub(super) fn bind(
        region: RegionId,
        body: SemanticNode,
    ) -> Result<SemanticNode, StructureError> {
        let label = SemanticLabel::block(region, SemanticIdentity::next(&body, region)?);
        let mut binding = Self {
            region,
            label,
            active: 0,
            bound: 0,
        };
        let body = binding.fold_node(body).map_err(StructureError::from)?;
        Ok(if binding.bound == 0 {
            body
        } else {
            SemanticNode::Label {
                label,
                body: Box::new(body),
            }
        })
    }
}

impl SemanticFolder for SwitchControlDomain {
    type Error = SemanticFoldError;

    fn enter_node(&mut self, node: &SemanticNode) {
        if matches!(
            node,
            SemanticNode::Switch {
                region: Some(region),
                ..
            } if *region == self.region
        ) {
            self.active += 1;
        }
    }

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        if let SemanticNode::Leave(leave) = &mut node {
            if self.active == 0
                && leave.target == self.region
                && matches!(leave.kind, SemanticLeaveKind::Break)
            {
                leave.kind = SemanticLeaveKind::BreakLabel(self.label);
                self.bound += 1;
            }
        }
        if matches!(
            &node,
            SemanticNode::Switch {
                region: Some(region),
                ..
            } if *region == self.region
        ) {
            self.active -= 1;
        }
        Ok(node)
    }
}

#[derive(Default)]
struct SemanticIdentity {
    maximum: Option<u32>,
}

impl SemanticIdentity {
    fn next(body: &SemanticNode, region: RegionId) -> Result<BlockId, StructureError> {
        let mut identity = Self::default();
        identity.visit_node(body);
        let next = identity
            .maximum
            .unwrap_or_default()
            .checked_add(1)
            .ok_or(StructureError::GraphNodeIdExhausted(region))?;
        Ok(BlockId::new(next))
    }

    fn record(&mut self, block: BlockId) {
        self.maximum = Some(
            self.maximum
                .map_or(block.raw(), |value| value.max(block.raw())),
        );
    }
}

impl SemanticVisitor for SemanticIdentity {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::BasicBlock(block) => self.record(block.id),
            SemanticNode::Label { label, .. } => self.record(label.block),
            SemanticNode::Loop {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: SemanticLoopControl::Label(label),
                ..
            } => self.record(label.block),
            _ => {}
        }
    }
}

impl SwitchPartition {
    fn analyze(
        cfg: &CFG,
        terminal_boundaries: &BTreeSet<BlockId>,
        semantic_entries: &BTreeSet<BlockId>,
    ) -> Result<Self, StructureError> {
        let header = cfg.entry;
        let block = cfg
            .block(header)
            .ok_or(StructureError::MissingBlock(header))?;
        let terminator = block
            .terminator()
            .ok_or(StructureError::SwitchMissingTerminator(header))?;
        if terminator.insn_type != InsnType::Switch {
            return Err(StructureError::SwitchWrongTerminator(header));
        }
        let selector = terminator
            .args
            .first()
            .cloned()
            .ok_or(StructureError::SwitchMissingSelector(header))?;
        let mut labels = Self::labels(cfg, header)?;
        if labels.is_empty() {
            return Err(StructureError::SwitchMissingArms(header));
        }

        let mut entries = labels.keys().copied().collect::<Vec<_>>();
        for entry in &entries {
            if cfg.block(*entry).is_none() {
                return Err(StructureError::MissingBlock(*entry));
            }
        }
        entries.sort_by_key(|entry| {
            let block = &cfg.blocks[entry];
            (block.offset, block.id)
        });
        let entry_set = entries.iter().copied().collect::<BTreeSet<_>>();
        let mut arms = Vec::with_capacity(entries.len());
        for entry in entries.iter().copied() {
            let nodes = Self::arm_nodes(cfg, entry, &entry_set);
            arms.push(SwitchArm {
                entry,
                labels: labels
                    .remove(&entry)
                    .ok_or(StructureError::SwitchMissingArmLabels { header, arm: entry })?,
                nodes,
            });
        }
        let mut is_structured = true;
        match SwitchFallthrough::analyze(cfg, &arms, terminal_boundaries, semantic_entries) {
            Some(graph) => {
                graph.partition(&mut arms);
                let Some(order) = graph.order(&arms) else {
                    is_structured = false;
                    return Ok(Self {
                        selector,
                        arms,
                        is_structured,
                    });
                };
                let mut by_entry = arms
                    .into_iter()
                    .map(|arm| (arm.entry, arm))
                    .collect::<BTreeMap<_, _>>();
                arms = order
                    .into_iter()
                    .filter_map(|entry| by_entry.remove(&entry))
                    .collect();
            }
            None => is_structured = false,
        }
        let mut claimed = BTreeSet::from([header]);
        for (index, arm) in arms.iter().enumerate() {
            let lexical_next = arms.get(index + 1).map(|next| next.entry);
            let overlaps = arm
                .nodes
                .iter()
                .any(|node| claimed.contains(node) && !terminal_boundaries.contains(node));
            let crosses = arm.nodes.iter().copied().any(|source| {
                cfg.normal_successors(source)
                    .any(|target| entry_set.contains(&target) && Some(target) != lexical_next)
            });
            is_structured &= !overlaps && !crosses;
            claimed.extend(
                arm.nodes
                    .iter()
                    .copied()
                    .filter(|node| !terminal_boundaries.contains(node)),
            );
        }
        Ok(Self {
            selector,
            arms,
            is_structured,
        })
    }

    fn labels(cfg: &CFG, header: BlockId) -> Result<BTreeMap<BlockId, ArmLabels>, StructureError> {
        let mut labels = BTreeMap::<BlockId, ArmLabels>::new();
        for &(target, kind) in cfg.successors_with_kind(header) {
            match kind {
                EdgeKind::SwitchCase(value) => {
                    labels.entry(target).or_default().values.push(value);
                }
                EdgeKind::SwitchDefault => labels.entry(target).or_default().is_default = true,
                EdgeKind::Exception => {}
                _ => return Err(StructureError::MalformedSwitchEdge { header, edge: kind }),
            }
        }
        Ok(labels)
    }

    fn arm_nodes(cfg: &CFG, entry: BlockId, entries: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut nodes = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(node) = pending.pop() {
            if node == cfg.entry
                || (node != entry && entries.contains(&node))
                || !nodes.insert(node)
            {
                continue;
            }
            pending.extend(cfg.normal_successors(node));
        }
        nodes
    }
}

pub(super) struct SwitchStructurer<'a, 'semantic> {
    cfg: &'a CFG,
    semantic: &'semantic SemanticFactory<'semantic>,
    region: RegionId,
    seeded: BTreeMap<BlockId, SemanticNode>,
    terminal_seeds: BTreeSet<BlockId>,
}

impl<'a, 'semantic> SwitchStructurer<'a, 'semantic> {
    pub(super) fn new(
        cfg: &'a CFG,
        semantic: &'semantic SemanticFactory<'semantic>,
        region: RegionId,
        seeded: BTreeMap<BlockId, SemanticNode>,
    ) -> Self {
        Self {
            cfg,
            semantic,
            region,
            seeded,
            terminal_seeds: BTreeSet::new(),
        }
    }

    pub(super) fn terminal_seeds(mut self, blocks: BTreeSet<BlockId>) -> Self {
        self.terminal_seeds = blocks;
        self
    }

    pub(super) fn structure(mut self) -> Result<SemanticNode, StructureError> {
        let header = self.cfg.entry;
        let semantic_entries = self.seeded.keys().copied().collect::<BTreeSet<_>>();
        let SwitchPartition {
            selector,
            arms,
            is_structured,
        } = SwitchPartition::analyze(self.cfg, &self.terminal_seeds, &semantic_entries)?;
        let seed_owners = self
            .seeded
            .keys()
            .map(|seed| {
                (
                    *seed,
                    arms.iter().filter(|arm| arm.nodes.contains(seed)).count(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let seeds_are_partitioned = seed_owners.values().all(|owners| *owners != 0);
        let shared_seeds_are_terminal = seed_owners
            .iter()
            .all(|(seed, owners)| *owners <= 1 || self.terminal_seeds.contains(seed));
        if !is_structured || !seeds_are_partitioned || !shared_seeds_are_terminal {
            return self.graph_reduction();
        }
        let mut cases = Vec::with_capacity(arms.len());
        for arm in arms {
            let seeded = arm
                .nodes
                .iter()
                .filter_map(|node| {
                    let body = if seed_owners.get(node).copied().unwrap_or(0) > 1 {
                        self.seeded.get(node).cloned()
                    } else {
                        self.seeded.remove(node)
                    }?;
                    Some((*node, body))
                })
                .collect();
            let body = self.arm_body(arm.entry, &arm.nodes, seeded)?;
            let mut labels = arm.labels;
            labels.values.sort();
            labels.values.dedup();
            cases.push(SemanticSwitchCase {
                values: labels.values,
                is_default: labels.is_default,
                body,
            });
        }

        Ok(SemanticNode::sequence([
            self.semantic.block(header, true)?,
            SemanticNode::Switch {
                region: Some(self.region),
                selector: crate::ir::SemanticOperand::new(
                    crate::ir::SemanticExpression::from_argument(selector)?,
                ),
                cases,
            },
        ]))
    }

    fn graph_reduction(self) -> Result<SemanticNode, StructureError> {
        GraphStructurer::new(self.cfg, self.semantic, self.region)
            .seeded(self.seeded)
            .terminal_seeds(self.terminal_seeds)
            .force_graph_reduction(true)
            .structure()
    }

    fn arm_body(
        &self,
        entry: BlockId,
        nodes: &BTreeSet<BlockId>,
        mut seeded: BTreeMap<BlockId, SemanticNode>,
    ) -> Result<SemanticNode, StructureError> {
        let mut cfg = self
            .cfg
            .subgraph(format!("{}::switch-arm", self.cfg.label()));
        cfg.entry = entry;
        let terminal_exits = nodes
            .iter()
            .copied()
            .flat_map(|source| self.cfg.normal_successors(source))
            .filter(|target| !nodes.contains(target) && self.terminal_seeds.contains(target))
            .collect::<BTreeSet<_>>();
        for node in nodes.iter().chain(&terminal_exits) {
            let block = self
                .cfg
                .block(*node)
                .cloned()
                .ok_or(StructureError::MissingBlock(*node))?;
            cfg.add_block(block);
        }
        for source in nodes {
            for &(target, kind) in self.cfg.successors_with_kind(*source) {
                if !kind.is_exception()
                    && (nodes.contains(&target) || terminal_exits.contains(&target))
                {
                    cfg.add_edge(*source, target, kind);
                }
            }
        }
        seeded.extend(
            terminal_exits
                .iter()
                .filter_map(|target| self.seeded.get(target).cloned().map(|body| (*target, body))),
        );
        let terminal_seeds = self
            .terminal_seeds
            .intersection(nodes)
            .copied()
            .chain(terminal_exits)
            .collect();
        GraphStructurer::new(&cfg, self.semantic, self.region)
            .seeded(seeded)
            .terminal_seeds(terminal_seeds)
            .structure()
    }
}
