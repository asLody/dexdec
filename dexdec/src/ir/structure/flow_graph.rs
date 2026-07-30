//! Semantic control graph reduction.
//!
//! Region-local graph nodes own semantic fragments. Their exits remain explicit
//! until this graph is reduced, so nested exception regions never lose the
//! path that selected a continuation. Reducible SCCs become lexical loops;
//! irreducible entries are split by semantics-preserving node duplication; and
//! the remaining DAG is translated with the NoMoreGotos nested-label scheme.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::semantic::SemanticCompletion;
use crate::ir::semantic::SemanticFactory;
use crate::ir::{
    Block, BlockId, BoolExpr, EdgeKind, InsnArg, InsnType, RegionId, SemanticFoldError,
    SemanticFolder, SemanticLabel, SemanticLeaveKind, SemanticNode, SemanticPredicate,
    SemanticSwitchCase, SemanticVisitor, CFG,
};

use super::{
    acyclic::{AcyclicStructure, AcyclicStructurer},
    loop_classifier::LoopClassifier,
    StructureError,
};

#[derive(Debug, Clone)]
enum FlowTransfer {
    Fragment {
        normal: Option<BlockId>,
        open: BTreeSet<BlockId>,
    },
    Stop,
    Jump(BlockId),
    Branch {
        condition: SemanticPredicate,
        when_true: BlockId,
        when_false: BlockId,
    },
    Switch {
        selector: InsnArg,
        cases: Vec<(Vec<i32>, BlockId)>,
        default: Option<BlockId>,
    },
}

#[derive(Debug)]
struct FlowBoundary {
    targets: BTreeSet<BlockId>,
    open: BTreeSet<BlockId>,
    bound: BTreeSet<BlockId>,
}

impl FlowBoundary {
    fn analyze(region: RegionId, body: &SemanticNode, targets: BTreeSet<BlockId>) -> Self {
        let mut jumps = OpenTargetCollector::new(region);
        jumps.visit_node(body);
        let open = targets
            .intersection(&jumps.targets)
            .copied()
            .collect::<BTreeSet<_>>();
        Self {
            targets,
            open,
            bound: BTreeSet::new(),
        }
    }

    fn bind_targets(mut self, targets: impl IntoIterator<Item = BlockId>) -> Self {
        self.bound = targets
            .into_iter()
            .filter(|target| self.targets.contains(target))
            .collect();
        self
    }

    fn implicit_targets(&self) -> BTreeSet<BlockId> {
        self.targets
            .difference(&self.open)
            .filter(|target| !self.bound.contains(target))
            .copied()
            .collect::<BTreeSet<_>>()
    }

    fn unique_implicit_target(&self) -> Option<BlockId> {
        let implicit = self.implicit_targets();
        (implicit.len() == 1)
            .then(|| implicit.first().copied())
            .flatten()
    }
}

impl FlowTransfer {
    fn targets(&self) -> BTreeSet<BlockId> {
        match self {
            Self::Fragment { normal, open } => {
                normal.iter().copied().chain(open.iter().copied()).collect()
            }
            Self::Stop => BTreeSet::new(),
            Self::Jump(target) => BTreeSet::from([*target]),
            Self::Branch {
                when_true,
                when_false,
                ..
            } => BTreeSet::from([*when_true, *when_false]),
            Self::Switch { cases, default, .. } => cases
                .iter()
                .map(|(_, target)| *target)
                .chain(default.iter().copied())
                .collect(),
        }
    }

    fn remap(&mut self, mapping: &BTreeMap<BlockId, BlockId>) {
        let remap = |target: &mut BlockId| {
            if let Some(replacement) = mapping.get(target) {
                *target = *replacement;
            }
        };
        match self {
            Self::Fragment { normal, open } => {
                if let Some(target) = normal {
                    remap(target);
                }
                *open = open
                    .iter()
                    .map(|target| mapping.get(target).copied().unwrap_or(*target))
                    .collect();
            }
            Self::Jump(target) => remap(target),
            Self::Branch {
                when_true,
                when_false,
                ..
            } => {
                remap(when_true);
                remap(when_false);
            }
            Self::Switch { cases, default, .. } => {
                for (_, target) in cases {
                    remap(target);
                }
                if let Some(default) = default {
                    remap(default);
                }
            }
            Self::Stop => {}
        }
    }

    fn fragment(
        block: BlockId,
        body: &SemanticNode,
        boundary: FlowBoundary,
    ) -> Result<Self, StructureError> {
        let normal_candidates = boundary.implicit_targets();
        let completion = SemanticCompletion::analyze(body);
        let malformed = || StructureError::MalformedFlowNode(block);
        let normal = if completion.can_complete_normally() {
            match normal_candidates.len() {
                0 => None,
                1 => normal_candidates.first().copied(),
                _ => return Err(malformed()),
            }
        } else {
            if !normal_candidates.is_empty() {
                return Err(malformed());
            }
            None
        };
        Ok(Self::Fragment {
            normal,
            open: boundary.open,
        })
    }
}

#[derive(Debug, Clone)]
struct FlowNode {
    body: SemanticNode,
    transfer: FlowTransfer,
}

#[derive(Debug, Clone)]
struct LoopContinuation {
    label: SemanticLabel,
    members: BTreeSet<BlockId>,
}

impl LoopContinuation {
    fn scoped(label: SemanticLabel, members: BTreeSet<BlockId>) -> Self {
        Self { label, members }
    }

    #[cfg(test)]
    fn unscoped(label: SemanticLabel) -> Self {
        Self {
            label,
            members: BTreeSet::new(),
        }
    }

    fn accepts(&self, source: BlockId) -> bool {
        self.members.is_empty() || self.members.contains(&source)
    }
}

pub(super) struct SemanticFlowGraph {
    region: RegionId,
    entry: BlockId,
    nodes: BTreeMap<BlockId, FlowNode>,
    next_id: u32,
    continues: BTreeMap<BlockId, LoopContinuation>,
    exits: BTreeSet<BlockId>,
}

impl SemanticFlowGraph {
    fn allocate_label(
        &mut self,
        kind: crate::ir::SemanticLabelKind,
    ) -> Result<SemanticLabel, StructureError> {
        let block = BlockId::new(self.next_id);
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or(StructureError::GraphNodeIdExhausted(self.region))?;
        Ok(SemanticLabel {
            region: self.region,
            block,
            kind,
        })
    }

    pub(super) fn build(
        cfg: &CFG,
        semantic: &SemanticFactory<'_>,
        region: RegionId,
        seeded: &BTreeMap<BlockId, SemanticNode>,
        fragments: &BTreeSet<BlockId>,
    ) -> Result<Self, StructureError> {
        let graph_nodes = cfg.graph_node_ids().into_iter().collect::<BTreeSet<_>>();
        let mut nodes = BTreeMap::new();
        for block in &graph_nodes {
            let source = cfg
                .block(*block)
                .ok_or(StructureError::MissingBlock(*block))?;
            let successors = cfg
                .successors_with_kind(*block)
                .iter()
                .filter(|(_, kind)| !kind.is_exception())
                .copied()
                .collect::<Vec<_>>();
            let prefix_only = source.terminator().is_some_and(|terminator| {
                matches!(terminator.insn_type, InsnType::If | InsnType::Switch)
            });
            let body = match seeded.get(block) {
                Some(body) => body.clone(),
                None => semantic.block(*block, prefix_only)?,
            };
            let transfer = if fragments.contains(block) {
                let targets = successors.iter().map(|(target, _)| *target).collect();
                let boundary = FlowBoundary::analyze(region, &body, targets);
                FlowTransfer::fragment(*block, &body, boundary)?
            } else {
                Self::transfer(semantic, *block, source.terminator(), &successors)?
            };
            nodes.insert(*block, FlowNode { body, transfer });
        }
        let next_id = graph_nodes
            .iter()
            .map(|block| block.raw())
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(StructureError::GraphNodeIdExhausted(region))?;
        let mut graph = Self {
            region,
            entry: cfg.entry,
            nodes,
            next_id,
            continues: BTreeMap::new(),
            exits: BTreeSet::new(),
        };
        graph.prune();
        Ok(graph)
    }

    fn transfer(
        semantic: &SemanticFactory<'_>,
        block: BlockId,
        terminator: Option<&crate::ir::InsnNode>,
        successors: &[(BlockId, EdgeKind)],
    ) -> Result<FlowTransfer, StructureError> {
        match terminator.map(|instruction| instruction.insn_type) {
            Some(InsnType::If) => {
                let when_true = successors
                    .iter()
                    .find_map(|(target, kind)| (*kind == EdgeKind::True).then_some(*target));
                let when_false = successors
                    .iter()
                    .find_map(|(target, kind)| (*kind == EdgeKind::False).then_some(*target));
                Ok(FlowTransfer::Branch {
                    condition: semantic.predicate(BoolExpr::block(block))?,
                    when_true: when_true.ok_or(StructureError::MalformedFlowNode(block))?,
                    when_false: when_false.ok_or(StructureError::MalformedFlowNode(block))?,
                })
            }
            Some(InsnType::Switch) => {
                let selector = terminator
                    .and_then(|instruction| instruction.args.first())
                    .cloned()
                    .ok_or(StructureError::SwitchMissingSelector(block))?;
                let mut cases = BTreeMap::<BlockId, Vec<i32>>::new();
                let mut default = None;
                for &(target, kind) in successors {
                    match kind {
                        EdgeKind::SwitchCase(value) => cases.entry(target).or_default().push(value),
                        EdgeKind::SwitchDefault => default = Some(target),
                        _ => return Err(StructureError::MalformedFlowNode(block)),
                    }
                }
                Ok(FlowTransfer::Switch {
                    selector,
                    cases: cases
                        .into_iter()
                        .map(|(target, mut values)| {
                            values.sort();
                            (values, target)
                        })
                        .collect(),
                    default,
                })
            }
            _ => match successors {
                [] => Ok(FlowTransfer::Stop),
                [(target, _)] => Ok(FlowTransfer::Jump(*target)),
                _ => Err(StructureError::MalformedFlowNode(block)),
            },
        }
    }

    pub(super) fn reduce(
        self,
        semantic: &SemanticFactory<'_>,
    ) -> Result<SemanticNode, StructureError> {
        self.reduce_state(semantic).map(|(body, _)| body)
    }

    fn reduce_state(
        mut self,
        semantic: &SemanticFactory<'_>,
    ) -> Result<(SemanticNode, u32), StructureError> {
        loop {
            self.prune();
            FragmentNormalizer::apply(&mut self)?;
            self.bind_embedded_continuations()?;
            self.verify_lexical_domains()?;
            let components = self.components();
            let Some(component) = components
                .into_iter()
                .find(|component| self.is_cyclic(component))
            else {
                if semantic.is_switch_region(self.region) {
                    while let Some(switch) = SwitchRegion::analyze(&self)? {
                        self.collapse_switch(switch, semantic)?;
                        self.prune();
                        self.verify_lexical_domains()?;
                    }
                }
                if let Some(body) = self.structure_acyclic(semantic)? {
                    return Ok((body, self.next_id));
                }
                while let Some(branch) = BranchRegion::analyze(&self)? {
                    self.collapse_branch(branch, semantic)?;
                    self.prune();
                    self.verify_lexical_domains()?;
                    if let Some(body) = self.structure_acyclic(semantic)? {
                        return Ok((body, self.next_id));
                    }
                }
                let lowering = AcyclicLabelLowering::new(&self)?;
                let next_id = lowering.next_id();
                let body = lowering.lower()?;
                return Ok((body, next_id));
            };
            let entries = self.component_entries(&component);
            if entries.len() > 1 {
                self.split_entries(&component, &entries)?;
            } else {
                let header = entries
                    .first()
                    .copied()
                    .or_else(|| component.first().copied())
                    .ok_or(StructureError::MalformedFlowGraph(self.region))?;
                self.collapse_loop(component, header, semantic)?;
            }
        }
    }

    fn collapse_loop(
        &mut self,
        component: BTreeSet<BlockId>,
        header: BlockId,
        semantic: &SemanticFactory<'_>,
    ) -> Result<(), StructureError> {
        let label = self.allocate_label(crate::ir::SemanticLabelKind::Loop)?;
        let external = component
            .iter()
            .flat_map(|block| self.targets(*block))
            .filter(|target| !component.contains(target))
            .collect::<BTreeSet<_>>();
        let mut inner_nodes = component
            .iter()
            .map(|block| {
                self.nodes
                    .remove(block)
                    .map(|node| (*block, node))
                    .ok_or(StructureError::MalformedFlowNode(*block))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let mut inner = Self {
            region: self.region,
            entry: header,
            nodes: std::mem::take(&mut inner_nodes),
            next_id: self.next_id,
            continues: self.continues.clone(),
            exits: BTreeSet::new(),
        };
        inner
            .continues
            .insert(header, LoopContinuation::scoped(label, component.clone()));
        let (body, next_id) = inner.reduce_state(semantic)?;
        self.next_id = self.next_id.max(next_id);

        let boundary = FlowBoundary::analyze(self.region, &body, external.clone())
            .bind_targets(self.continues.keys().copied());
        let follow = boundary.unique_implicit_target();
        let body = LoopClassifier::for_label(label, follow)
            .preserve_blocks(semantic.phi_copy_blocks())
            .classify(body)?;
        if !LexicalLabelClosure::is_closed(&body, label) {
            return Err(StructureError::EscapedLoopLabel {
                region: self.region,
                label,
            });
        }
        let boundary = FlowBoundary::analyze(self.region, &body, external)
            .bind_targets(self.continues.keys().copied());
        let replacement = FlowNode {
            transfer: FlowTransfer::fragment(header, &body, boundary)?,
            body,
        };
        self.nodes.insert(header, replacement);
        let mapping = component
            .iter()
            .copied()
            .filter(|block| *block != header)
            .map(|block| (block, header))
            .collect::<BTreeMap<_, _>>();
        for node in self.nodes.values_mut() {
            node.transfer.remap(&mapping);
            node.body = OpenTargetRemap::new(self.region, &mapping)
                .fold_node(std::mem::replace(&mut node.body, SemanticNode::Empty))?;
        }
        Ok(())
    }

    fn collapse_branch(
        &mut self,
        branch: BranchRegion,
        semantic: &SemanticFactory<'_>,
    ) -> Result<(), StructureError> {
        let when_true =
            self.lower_arm(branch.when_true, &branch.true_arm, branch.join, semantic)?;
        let when_false =
            self.lower_arm(branch.when_false, &branch.false_arm, branch.join, semantic)?;
        let source = self
            .nodes
            .get_mut(&branch.source)
            .ok_or(StructureError::MalformedFlowNode(branch.source))?;
        let condition = match &source.transfer {
            FlowTransfer::Branch { condition, .. } => condition.clone(),
            _ => return Err(StructureError::MalformedFlowNode(branch.source)),
        };
        source.body = SemanticNode::sequence([
            std::mem::replace(&mut source.body, SemanticNode::Empty),
            SemanticNode::branch(condition, when_true, Some(when_false)),
        ]);
        source.transfer = FlowTransfer::Jump(branch.join);
        for block in branch
            .true_arm
            .nodes
            .into_iter()
            .chain(branch.false_arm.nodes)
        {
            self.nodes.remove(&block);
        }
        Ok(())
    }

    fn collapse_switch(
        &mut self,
        switch: SwitchRegion,
        semantic: &SemanticFactory<'_>,
    ) -> Result<(), StructureError> {
        let mut cases = Vec::with_capacity(switch.arms.len());
        for arm in switch.arms {
            let nodes = arm
                .nodes
                .iter()
                .map(|block| {
                    self.nodes
                        .get(block)
                        .cloned()
                        .map(|node| (*block, node))
                        .ok_or(StructureError::MalformedFlowNode(*block))
                })
                .collect::<Result<BTreeMap<_, _>, _>>()?;
            let exits = arm
                .nodes
                .iter()
                .copied()
                .flat_map(|block| self.targets(block))
                .filter(|target| !arm.nodes.contains(target))
                .chain(switch.join.filter(|join| arm.entry == *join).into_iter())
                .collect();
            let body = if switch.join == Some(arm.entry) {
                SemanticNode::Empty
            } else {
                let inner = Self {
                    region: self.region,
                    entry: arm.entry,
                    nodes,
                    next_id: self.next_id,
                    continues: self.continues.clone(),
                    exits,
                };
                let (body, next_id) = inner.reduce_state(semantic)?;
                self.next_id = self.next_id.max(next_id);
                body
            };
            let body = if SemanticCompletion::analyze(&body).can_complete_normally() {
                SemanticNode::sequence([
                    body,
                    SemanticNode::Leave(crate::ir::SemanticLeave {
                        site: None,
                        condition: None,
                        kind: SemanticLeaveKind::Break,
                        edge: None,
                        origin: None,
                        source: self.region,
                        destination: self.region,
                        target: self.region,
                        cleanup: Vec::new(),
                    }),
                ])
            } else {
                body
            };
            cases.push(SemanticSwitchCase {
                values: arm.values,
                is_default: arm.is_default,
                body,
            });
        }

        let source = self
            .nodes
            .get_mut(&switch.source)
            .ok_or(StructureError::MalformedFlowNode(switch.source))?;
        source.body = SemanticNode::sequence([
            std::mem::replace(&mut source.body, SemanticNode::Empty),
            SemanticNode::Switch {
                region: Some(self.region),
                selector: crate::ir::SemanticOperand::new(
                    crate::ir::SemanticExpression::from_argument(switch.selector)?,
                ),
                cases,
            },
        ]);
        source.transfer = switch.join.map_or(FlowTransfer::Stop, FlowTransfer::Jump);
        for block in switch.nodes {
            self.nodes.remove(&block);
        }
        Ok(())
    }

    fn lower_arm(
        &mut self,
        entry: BlockId,
        arm: &BranchArm,
        join: BlockId,
        semantic: &SemanticFactory<'_>,
    ) -> Result<SemanticNode, StructureError> {
        if entry == join {
            return Ok(SemanticNode::Empty);
        }
        let nodes = arm
            .nodes
            .iter()
            .map(|block| {
                self.nodes
                    .remove(block)
                    .map(|node| (*block, node))
                    .ok_or(StructureError::MalformedFlowNode(*block))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let mut exits = self.exits.clone();
        exits.insert(join);
        if let Some(continuation) = &arm.continuation {
            exits.insert(continuation.entry);
        }
        let inner = Self {
            region: self.region,
            entry,
            nodes,
            next_id: self.next_id,
            continues: self.continues.clone(),
            exits,
        };
        let (body, next_id) = inner.reduce_state(semantic)?;
        self.next_id = self.next_id.max(next_id);
        Ok(match &arm.continuation {
            Some(continuation) => SemanticNode::sequence([body, continuation.body(self)?]),
            None => body,
        })
    }

    fn structure_acyclic(
        &mut self,
        semantic: &SemanticFactory<'_>,
    ) -> Result<Option<SemanticNode>, StructureError> {
        let Some((cfg, predicates)) = self.acyclic_cfg()? else {
            return Ok(None);
        };
        let mut seeded = self
            .nodes
            .iter_mut()
            .map(|(block, node)| {
                (
                    *block,
                    std::mem::replace(&mut node.body, SemanticNode::Empty),
                )
            })
            .collect::<BTreeMap<_, _>>();
        seeded.extend(
            cfg.block_ids()
                .into_iter()
                .filter(|block| !self.nodes.contains_key(block))
                .map(|block| (block, SemanticNode::Empty)),
        );
        let result = AcyclicStructurer::new(&cfg, semantic, &mut seeded)
            .predicates(&predicates)
            .structure()
            .map_err(|source| StructureError::Acyclic {
                region: self.region,
                source,
            })?;
        match result {
            AcyclicStructure::Structured(body) => Ok(Some(body)),
            AcyclicStructure::RequiresGraphReduction(_reason) => {
                for (block, body) in seeded {
                    if let Some(node) = self.nodes.get_mut(&block) {
                        node.body = body;
                    }
                }
                Ok(None)
            }
        }
    }

    fn acyclic_cfg(
        &self,
    ) -> Result<Option<(CFG, BTreeMap<BlockId, SemanticPredicate>)>, StructureError> {
        let mut cfg = CFG::new(format!("semantic::{}", self.region));
        cfg.entry = self.entry;
        let mut predicates = BTreeMap::new();
        for (block, node) in &self.nodes {
            let mut skeleton = Block::synthetic(*block);
            match &node.transfer {
                FlowTransfer::Branch { condition, .. } => {
                    skeleton.push(crate::ir::InsnNode::new(InsnType::If, 0));
                    predicates.insert(*block, condition.clone());
                }
                FlowTransfer::Switch { .. } | FlowTransfer::Fragment { .. } => return Ok(None),
                FlowTransfer::Stop | FlowTransfer::Jump(_) => {}
            }
            let mut jumps = OpenTargetCollector::new(self.region);
            jumps.visit_node(&node.body);
            if jumps
                .targets
                .iter()
                .any(|target| self.is_internal_target(*target))
            {
                return Ok(None);
            }
            cfg.add_block(skeleton);
        }
        for exit in self
            .exits
            .iter()
            .copied()
            .filter(|exit| !self.nodes.contains_key(exit))
        {
            cfg.add_block(Block::synthetic(exit));
        }
        for (block, node) in &self.nodes {
            match &node.transfer {
                FlowTransfer::Stop => {}
                FlowTransfer::Jump(target) if self.is_acyclic_target(*target) => {
                    cfg.add_edge(*block, *target, EdgeKind::Normal);
                }
                FlowTransfer::Jump(_) => return Ok(None),
                FlowTransfer::Branch {
                    when_true,
                    when_false,
                    ..
                } => {
                    if !self.is_acyclic_target(*when_true) || !self.is_acyclic_target(*when_false) {
                        return Ok(None);
                    }
                    cfg.add_edge(*block, *when_true, EdgeKind::True);
                    cfg.add_edge(*block, *when_false, EdgeKind::False);
                }
                FlowTransfer::Switch { .. } | FlowTransfer::Fragment { .. } => return Ok(None),
            }
        }
        cfg.prune_unreachable_graph_nodes();
        predicates.retain(|block, _| cfg.is_graph_node(*block));
        Ok(Some((cfg, predicates)))
    }

    fn is_internal_target(&self, target: BlockId) -> bool {
        self.nodes.contains_key(&target) && !self.continues.contains_key(&target)
    }

    fn is_control_boundary(&self, target: BlockId) -> bool {
        self.exits.contains(&target)
            || self.continues.contains_key(&target)
            || !self.nodes.contains_key(&target)
    }

    fn is_acyclic_target(&self, target: BlockId) -> bool {
        self.is_internal_target(target) || self.exits.contains(&target)
    }

    fn split_entries(
        &mut self,
        component: &BTreeSet<BlockId>,
        entries: &BTreeSet<BlockId>,
    ) -> Result<(), StructureError> {
        let plan = IrreducibleEntryAnalysis::new(self, component, entries).analyze()?;
        let predecessors = self.predecessors();
        for (entry, slice) in plan.copies {
            let mapping = slice
                .iter()
                .copied()
                .map(|block| self.allocate().map(|clone| (block, clone)))
                .collect::<Result<BTreeMap<_, _>, _>>()?;
            let mut bindings = LexicalBindings::default();
            for block in &slice {
                let node = self
                    .nodes
                    .get(block)
                    .ok_or(StructureError::MalformedFlowNode(*block))?;
                bindings.visit_node(&node.body);
            }
            let mut lexical_mapping = BTreeMap::new();
            for label in bindings.labels {
                let block = self.allocate()?;
                lexical_mapping.insert(
                    label,
                    SemanticLabel {
                        region: label.region,
                        block,
                        kind: label.kind,
                    },
                );
            }
            let mut clones = BTreeMap::new();
            for block in &slice {
                let mut node = self
                    .nodes
                    .get(block)
                    .cloned()
                    .ok_or(StructureError::MalformedFlowNode(*block))?;
                node.transfer.remap(&mapping);
                node.body = LexicalAlphaRenaming::new(&lexical_mapping).fold_node(node.body)?;
                node.body = OpenTargetRemap::new(self.region, &mapping).fold_node(node.body)?;
                clones.insert(mapping[block], node);
            }
            self.nodes.extend(clones);
            let replacement = BTreeMap::from([(entry, mapping[&entry])]);
            for predecessor in predecessors.get(&entry).into_iter().flatten() {
                if component.contains(predecessor) {
                    continue;
                }
                let node = self
                    .nodes
                    .get_mut(predecessor)
                    .ok_or(StructureError::MalformedFlowNode(*predecessor))?;
                node.transfer.remap(&replacement);
                node.body = OpenTargetRemap::new(self.region, &replacement)
                    .fold_node(std::mem::replace(&mut node.body, SemanticNode::Empty))?;
            }
        }
        Ok(())
    }

    fn allocate(&mut self) -> Result<BlockId, StructureError> {
        let block = BlockId::new(self.next_id);
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or(StructureError::GraphNodeIdExhausted(self.region))?;
        Ok(block)
    }

    fn component_entries(&self, component: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let predecessors = self.predecessors();
        component
            .iter()
            .copied()
            .filter(|node| {
                *node == self.entry
                    || predecessors
                        .get(node)
                        .into_iter()
                        .flatten()
                        .any(|predecessor| !component.contains(predecessor))
            })
            .collect()
    }

    fn is_cyclic(&self, component: &BTreeSet<BlockId>) -> bool {
        component.len() > 1
            || component
                .iter()
                .any(|node| self.successors(*node).any(|successor| successor == *node))
    }

    fn bind_embedded_continuations(&mut self) -> Result<(), StructureError> {
        if self.continues.is_empty() {
            return Ok(());
        }
        for (block, node) in &mut self.nodes {
            node.body = EmbeddedContinuationBinding::new(self.region, *block, &self.continues)
                .fold_node(std::mem::replace(&mut node.body, SemanticNode::Empty))?;
        }
        Ok(())
    }

    fn verify_lexical_domains(&self) -> Result<(), StructureError> {
        for (block, node) in &self.nodes {
            for label in FreeLabelReferences::collect(&node.body) {
                let valid = self
                    .continues
                    .values()
                    .find(|continuation| continuation.label == label)
                    .is_some_and(|continuation| continuation.accepts(*block));
                if !valid {
                    return Err(StructureError::EscapedGraphLabel {
                        region: self.region,
                        node: *block,
                        label,
                    });
                }
            }
        }
        Ok(())
    }

    fn successors(&self, node: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.targets(node).into_iter().filter(move |target| {
            self.nodes.contains_key(target) && !self.continues.contains_key(target)
        })
    }

    fn targets(&self, block: BlockId) -> BTreeSet<BlockId> {
        let Some(node) = self.nodes.get(&block) else {
            return BTreeSet::new();
        };
        let mut targets = node.transfer.targets();
        let mut collector = OpenTargetCollector::new(self.region);
        collector.visit_node(&node.body);
        targets.extend(collector.targets);
        targets
    }

    fn predecessors(&self) -> BTreeMap<BlockId, BTreeSet<BlockId>> {
        let mut predecessors = self
            .nodes
            .keys()
            .copied()
            .map(|node| (node, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for source in self.nodes.keys().copied() {
            for target in self.successors(source) {
                predecessors.entry(target).or_default().insert(source);
            }
        }
        predecessors
    }

    fn target_use_count(&self, source: BlockId, target: BlockId) -> usize {
        let Some(node) = self.nodes.get(&source) else {
            return 0;
        };
        let body_uses = OpenTargetUseCounter::count(self.region, &node.body, target);
        body_uses
            + match &node.transfer {
                FlowTransfer::Fragment { normal, .. } => usize::from(*normal == Some(target)),
                FlowTransfer::Stop => 0,
                FlowTransfer::Jump(successor) => usize::from(*successor == target),
                FlowTransfer::Branch {
                    when_true,
                    when_false,
                    ..
                } => usize::from(*when_true == target) + usize::from(*when_false == target),
                FlowTransfer::Switch { cases, default, .. } => {
                    cases
                        .iter()
                        .filter(|(_, successor)| *successor == target)
                        .count()
                        + usize::from(*default == Some(target))
                }
            }
    }

    fn components(&self) -> Vec<BTreeSet<BlockId>> {
        let mut visited = BTreeSet::new();
        let mut order = Vec::new();
        for root in self.nodes.keys().copied() {
            let mut pending = vec![(root, false)];
            while let Some((node, exiting)) = pending.pop() {
                if exiting {
                    order.push(node);
                    continue;
                }
                if !visited.insert(node) {
                    continue;
                }
                pending.push((node, true));
                pending.extend(self.successors(node).map(|target| (target, false)));
            }
        }
        let predecessors = self.predecessors();
        let mut assigned = BTreeSet::new();
        let mut components = Vec::new();
        for root in order.into_iter().rev() {
            if assigned.contains(&root) {
                continue;
            }
            let mut component = BTreeSet::new();
            let mut pending = vec![root];
            while let Some(node) = pending.pop() {
                if !assigned.insert(node) {
                    continue;
                }
                component.insert(node);
                pending.extend(predecessors.get(&node).into_iter().flatten().copied());
            }
            components.push(component);
        }
        components.sort_by_key(|component| component.first().copied());
        components
    }

    fn prune(&mut self) {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![self.entry];
        while let Some(node) = pending.pop() {
            if !self.nodes.contains_key(&node) || !reachable.insert(node) {
                continue;
            }
            pending.extend(
                self.targets(node)
                    .into_iter()
                    .filter(|target| self.nodes.contains_key(target)),
            );
        }
        self.nodes.retain(|node, _| reachable.contains(node));
    }

    fn topological_order(&self) -> Result<Vec<BlockId>, StructureError> {
        let mut indegree = self
            .predecessors()
            .into_iter()
            .map(|(node, predecessors)| (node, predecessors.len()))
            .collect::<BTreeMap<_, _>>();
        let mut ready = indegree
            .iter()
            .filter_map(|(node, degree)| (*degree == 0).then_some(*node))
            .collect::<BTreeSet<_>>();
        let mut order = Vec::with_capacity(self.nodes.len());
        while let Some(node) = ready.pop_first() {
            order.push(node);
            for target in self.successors(node) {
                let degree = indegree
                    .get_mut(&target)
                    .ok_or(StructureError::MalformedFlowNode(target))?;
                *degree = degree.saturating_sub(1);
                if *degree == 0 {
                    ready.insert(target);
                }
            }
        }
        if order.len() != self.nodes.len() {
            return Err(StructureError::CyclicFlowGraph(self.region));
        }
        Ok(order)
    }
}

struct EntrySplitPlan {
    primary: BlockId,
    copies: Vec<(BlockId, BTreeSet<BlockId>)>,
}

struct IrreducibleEntryAnalysis<'a> {
    graph: &'a SemanticFlowGraph,
    component: &'a BTreeSet<BlockId>,
    entries: &'a BTreeSet<BlockId>,
    weights: BTreeMap<BlockId, usize>,
}

impl<'a> IrreducibleEntryAnalysis<'a> {
    fn new(
        graph: &'a SemanticFlowGraph,
        component: &'a BTreeSet<BlockId>,
        entries: &'a BTreeSet<BlockId>,
    ) -> Self {
        let weights = component
            .iter()
            .filter_map(|block| {
                graph
                    .nodes
                    .get(block)
                    .map(|node| (*block, SemanticWeight::of(&node.body)))
            })
            .collect();
        Self {
            graph,
            component,
            entries,
            weights,
        }
    }

    fn analyze(&self) -> Result<EntrySplitPlan, StructureError> {
        let primary = self
            .entries
            .iter()
            .copied()
            .map(|candidate| {
                (
                    self.copy_cost(candidate),
                    candidate != self.graph.entry,
                    candidate,
                )
            })
            .min()
            .map(|(_, _, candidate)| candidate)
            .ok_or(StructureError::MalformedFlowGraph(self.graph.region))?;
        let copies = self
            .entries
            .iter()
            .copied()
            .filter(|entry| *entry != primary)
            .map(|entry| {
                let slice = self.slice(entry, primary);
                if slice.is_empty() {
                    Err(StructureError::MalformedFlowNode(entry))
                } else {
                    Ok((entry, slice))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(EntrySplitPlan { primary, copies })
    }

    fn copy_cost(&self, primary: BlockId) -> usize {
        self.entries
            .iter()
            .copied()
            .filter(|entry| *entry != primary)
            .flat_map(|entry| self.slice(entry, primary))
            .fold(0usize, |cost, block| {
                cost.saturating_add(self.weights.get(&block).copied().unwrap_or(1))
            })
    }

    fn slice(&self, entry: BlockId, primary: BlockId) -> BTreeSet<BlockId> {
        let mut slice = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if block == primary || !self.component.contains(&block) || !slice.insert(block) {
                continue;
            }
            pending.extend(self.graph.successors(block));
        }
        slice
    }
}

struct SemanticWeight {
    weight: usize,
}

impl SemanticWeight {
    fn of(node: &SemanticNode) -> usize {
        let mut weight = Self { weight: 1 };
        weight.visit_node(node);
        weight.weight
    }
}

impl SemanticVisitor for SemanticWeight {
    fn enter_node(&mut self, _node: &SemanticNode) {
        self.weight = self.weight.saturating_add(1);
    }

    fn enter_operation(&mut self, _operation: &crate::ir::SemanticOperation) {
        self.weight = self.weight.saturating_add(1);
    }
}

struct EmbeddedContinuationBinding<'a> {
    region: RegionId,
    source: BlockId,
    continuations: &'a BTreeMap<BlockId, LoopContinuation>,
}

impl<'a> EmbeddedContinuationBinding<'a> {
    fn new(
        region: RegionId,
        source: BlockId,
        continuations: &'a BTreeMap<BlockId, LoopContinuation>,
    ) -> Self {
        Self {
            region,
            source,
            continuations,
        }
    }
}

impl SemanticFolder for EmbeddedContinuationBinding<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave) if leave.target == self.region => {
                let target = match &leave.kind {
                    SemanticLeaveKind::Jump(target) | SemanticLeaveKind::FallThrough(target) => {
                        *target
                    }
                    SemanticLeaveKind::BreakLabel(label)
                        if label.region == self.region
                            && label.kind == crate::ir::SemanticLabelKind::Block =>
                    {
                        label.block
                    }
                    _ => return Ok(SemanticNode::Leave(leave)),
                };
                if let Some(continuation) = self.continuations.get(&target) {
                    if continuation.accepts(self.source) {
                        leave.kind = SemanticLeaveKind::ContinueLabel(continuation.label);
                    }
                }
                SemanticNode::Leave(leave)
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

struct BlockExitBinding {
    region: RegionId,
    target: BlockId,
    label: SemanticLabel,
    count: usize,
}

impl BlockExitBinding {
    fn new(region: RegionId, target: BlockId, label: SemanticLabel) -> Self {
        Self {
            region,
            target,
            label,
            count: 0,
        }
    }
}

impl SemanticFolder for BlockExitBinding {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave)
                if leave.target == self.region
                    && matches!(
                        leave.kind,
                        SemanticLeaveKind::Jump(target) | SemanticLeaveKind::FallThrough(target)
                            if target == self.target
                    ) =>
            {
                self.count += 1;
                leave.kind = SemanticLeaveKind::BreakLabel(self.label);
                SemanticNode::Leave(leave)
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

struct FragmentNormalizer;

impl FragmentNormalizer {
    fn apply(graph: &mut SemanticFlowGraph) -> Result<(), StructureError> {
        loop {
            if let Some(continuation) = TerminalContinuation::analyze(graph)? {
                continuation.apply(graph)?;
                graph.prune();
                continue;
            }
            let fragments = graph
                .nodes
                .iter()
                .filter_map(|(block, node)| {
                    matches!(&node.transfer, FlowTransfer::Fragment { .. }).then_some(*block)
                })
                .collect::<Vec<_>>();
            for block in fragments {
                Self::normalize(graph, block)?;
            }
            let Some(continuation) = LinearContinuation::analyze(graph)? else {
                return Ok(());
            };
            continuation.apply(graph)?;
            graph.prune();
        }
    }

    fn normalize(graph: &mut SemanticFlowGraph, block: BlockId) -> Result<(), StructureError> {
        let transfer = graph
            .nodes
            .get(&block)
            .map(|node| node.transfer.clone())
            .ok_or(StructureError::MalformedFlowNode(block))?;
        let FlowTransfer::Fragment { normal, open } = transfer else {
            return Ok(());
        };
        let completion = graph
            .nodes
            .get(&block)
            .map(|node| SemanticCompletion::analyze(&node.body))
            .ok_or(StructureError::MalformedFlowNode(block))?;
        if !completion.has_open_transfer_to(graph.region) {
            let node = graph
                .nodes
                .get_mut(&block)
                .ok_or(StructureError::MalformedFlowNode(block))?;
            node.transfer = if completion.can_complete_normally() {
                normal.map_or(FlowTransfer::Stop, FlowTransfer::Jump)
            } else {
                FlowTransfer::Stop
            };
            return Ok(());
        }
        if open.is_empty() {
            let node = graph
                .nodes
                .get_mut(&block)
                .ok_or(StructureError::MalformedFlowNode(block))?;
            node.transfer = normal.map_or(FlowTransfer::Stop, FlowTransfer::Jump);
            return Ok(());
        }
        if normal.is_some() || open.len() != 1 {
            return Ok(());
        }
        let target = open
            .first()
            .copied()
            .ok_or(StructureError::MalformedFlowNode(block))?;
        let label = graph.allocate_label(crate::ir::SemanticLabelKind::Block)?;
        let node = graph
            .nodes
            .get_mut(&block)
            .ok_or(StructureError::MalformedFlowNode(block))?;
        let mut binding = BlockExitBinding::new(graph.region, target, label);
        node.body = binding.fold_node(std::mem::replace(&mut node.body, SemanticNode::Empty))?;
        if binding.count == 0 {
            return Err(StructureError::MalformedFlowNode(block));
        }
        node.body = SemanticNode::Label {
            label,
            body: Box::new(std::mem::replace(&mut node.body, SemanticNode::Empty)),
        };
        let completion = SemanticCompletion::analyze(&node.body);
        if completion.has_open_transfer_to(graph.region) {
            let mut jumps = OpenTargetCollector::new(graph.region);
            jumps.visit_node(&node.body);
            if jumps.targets.iter().any(|target| *target != graph.entry) {
                return Err(StructureError::MalformedFlowNode(block));
            }
        }
        if !completion.can_complete_normally() {
            return Err(StructureError::MalformedFlowNode(block));
        }
        node.transfer = FlowTransfer::Jump(target);
        Ok(())
    }
}

/// Closes one fragment exit over a short, linear and necessarily abrupt tail.
struct TerminalContinuation {
    source: BlockId,
    target: BlockId,
    blocks: Vec<BlockId>,
}

impl TerminalContinuation {
    const DUPLICATION_BUDGET: usize = 32;

    fn analyze(graph: &SemanticFlowGraph) -> Result<Option<Self>, StructureError> {
        let predecessors = graph.predecessors();
        for (source, node) in &graph.nodes {
            let FlowTransfer::Fragment { open, .. } = &node.transfer else {
                continue;
            };
            for target in open.iter().copied() {
                let mut blocks = Vec::new();
                let mut visited = BTreeSet::new();
                let mut expected_predecessor = *source;
                let mut current = target;
                loop {
                    if blocks.len() >= Self::DUPLICATION_BUDGET || !visited.insert(current) {
                        break;
                    }
                    let uniquely_owned =
                        predecessors.get(&current).is_some_and(|incoming| {
                            incoming.len() == 1 && incoming.contains(&expected_predecessor)
                        }) && graph.target_use_count(expected_predecessor, current) == 1;
                    let Some(continuation) = graph.nodes.get(&current) else {
                        break;
                    };
                    if !uniquely_owned {
                        if blocks.is_empty()
                            && Self::is_shareable_terminal(continuation)
                            && LexicalTransferClosure::can_embed(
                                graph,
                                *source,
                                std::slice::from_ref(&current),
                            )
                        {
                            blocks.push(current);
                            return Ok(Some(Self {
                                source: *source,
                                target,
                                blocks,
                            }));
                        }
                        break;
                    }
                    let completion = SemanticCompletion::analyze(&continuation.body);
                    blocks.push(current);
                    if !completion.can_complete_normally()
                        && !completion.has_open_transfer()
                        && completion.has_closed_transfer()
                        && matches!(&continuation.transfer, FlowTransfer::Stop)
                        && LexicalTransferClosure::can_embed(graph, *source, &blocks)
                    {
                        return Ok(Some(Self {
                            source: *source,
                            target,
                            blocks,
                        }));
                    }
                    if !completion.can_complete_normally() || !completion.is_transfer_free() {
                        break;
                    }
                    let FlowTransfer::Jump(next) = &continuation.transfer else {
                        break;
                    };
                    expected_predecessor = current;
                    current = *next;
                }
            }
        }
        Ok(None)
    }

    fn is_shareable_terminal(node: &FlowNode) -> bool {
        matches!(&node.transfer, FlowTransfer::Stop) && Self::is_pure_control(&node.body) && {
            let completion = SemanticCompletion::analyze(&node.body);
            !completion.can_complete_normally()
                && !completion.has_open_transfer()
                && completion.has_closed_transfer()
        }
    }

    fn is_pure_control(node: &SemanticNode) -> bool {
        match node {
            SemanticNode::Empty => true,
            SemanticNode::Sequence(nodes) => nodes.iter().all(Self::is_pure_control),
            SemanticNode::Leave(leave) => {
                leave.condition.is_none()
                    && leave.cleanup.is_empty()
                    && matches!(
                        &leave.kind,
                        SemanticLeaveKind::Break
                            | SemanticLeaveKind::Continue
                            | SemanticLeaveKind::BreakLabel(_)
                            | SemanticLeaveKind::ContinueLabel(_)
                    )
            }
            _ => false,
        }
    }

    fn apply(self, graph: &mut SemanticFlowGraph) -> Result<(), StructureError> {
        let continuation = SemanticNode::sequence(
            self.blocks
                .iter()
                .map(|block| {
                    graph
                        .nodes
                        .get(block)
                        .map(|node| node.body.clone())
                        .ok_or(StructureError::MalformedFlowNode(*block))
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        let region = graph.region;
        let source = graph
            .nodes
            .get_mut(&self.source)
            .ok_or(StructureError::MalformedFlowNode(self.source))?;
        let mut binding = TerminalContinuationBinding {
            region,
            target: self.target,
            continuation: &continuation,
            count: 0,
        };
        source.body =
            binding.fold_node(std::mem::replace(&mut source.body, SemanticNode::Empty))?;
        if binding.count == 0 {
            return Err(StructureError::MalformedFlowNode(self.source));
        }
        let FlowTransfer::Fragment { open, .. } = &mut source.transfer else {
            return Err(StructureError::MalformedFlowNode(self.source));
        };
        open.remove(&self.target);
        Ok(())
    }
}

/// Proves that moving a structured continuation under another graph node does
/// not move a labeled transfer outside the lexical control domain that owns it.
struct LexicalTransferClosure;

impl LexicalTransferClosure {
    fn can_embed(graph: &SemanticFlowGraph, destination: BlockId, blocks: &[BlockId]) -> bool {
        let mut identities = LexicalIdentities::default();
        let mut bindings = LexicalBindings::default();
        for block in blocks {
            let Some(node) = graph.nodes.get(block) else {
                return false;
            };
            identities.visit_node(&node.body);
            bindings.visit_node(&node.body);
        }
        identities.labels.difference(&bindings.labels).all(|label| {
            graph
                .continues
                .values()
                .find(|continuation| continuation.label == *label)
                .is_some_and(|continuation| continuation.accepts(destination))
        })
    }
}

struct LexicalLabelClosure {
    label: SemanticLabel,
    depth: usize,
    escaped: bool,
}

impl LexicalLabelClosure {
    fn is_closed(node: &SemanticNode, label: SemanticLabel) -> bool {
        let mut closure = Self {
            label,
            depth: 0,
            escaped: false,
        };
        closure.visit_node(node);
        !closure.escaped && closure.depth == 0
    }

    fn binds(&self, node: &SemanticNode) -> bool {
        matches!(
            node,
            SemanticNode::Label { label, .. } if *label == self.label
        ) || matches!(
            node,
            SemanticNode::Loop {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
                | SemanticNode::For {
                    control: crate::ir::SemanticLoopControl::Label(label),
                    ..
                }
                | SemanticNode::ForEach {
                    control: crate::ir::SemanticLoopControl::Label(label),
                    ..
                } if *label == self.label
        )
    }
}

impl SemanticVisitor for LexicalLabelClosure {
    fn enter_node(&mut self, node: &SemanticNode) {
        if self.binds(node) {
            self.depth += 1;
        }
        if matches!(
            node,
            SemanticNode::Leave(crate::ir::SemanticLeave {
                kind:
                    SemanticLeaveKind::BreakLabel(label)
                    | SemanticLeaveKind::ContinueLabel(label),
                ..
            }) if *label == self.label
        ) && self.depth == 0
        {
            self.escaped = true;
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        if self.binds(node) {
            self.depth -= 1;
        }
    }
}

#[derive(Default)]
struct FreeLabelReferences {
    active: BTreeMap<SemanticLabel, usize>,
    free: BTreeSet<SemanticLabel>,
}

impl FreeLabelReferences {
    fn collect(node: &SemanticNode) -> BTreeSet<SemanticLabel> {
        let mut references = Self::default();
        references.visit_node(node);
        references.free
    }

    fn binding(node: &SemanticNode) -> Option<SemanticLabel> {
        match node {
            SemanticNode::Label { label, .. } => Some(*label),
            SemanticNode::Loop {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            } => Some(*label),
            _ => None,
        }
    }
}

impl SemanticVisitor for FreeLabelReferences {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let Some(label) = Self::binding(node) {
            *self.active.entry(label).or_default() += 1;
        }
        if let SemanticNode::Leave(crate::ir::SemanticLeave {
            kind: SemanticLeaveKind::BreakLabel(label) | SemanticLeaveKind::ContinueLabel(label),
            ..
        }) = node
        {
            if !self.active.contains_key(label) {
                self.free.insert(*label);
            }
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let Some(label) = Self::binding(node) else {
            return;
        };
        let Some(depth) = self.active.get_mut(&label) else {
            return;
        };
        *depth -= 1;
        if *depth == 0 {
            self.active.remove(&label);
        }
    }
}

struct TerminalContinuationBinding<'a> {
    region: RegionId,
    target: BlockId,
    continuation: &'a SemanticNode,
    count: usize,
}

impl SemanticFolder for TerminalContinuationBinding<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(leave)
                if leave.target == self.region
                    && matches!(
                        leave.kind,
                        SemanticLeaveKind::Jump(target) | SemanticLeaveKind::FallThrough(target)
                            if target == self.target
                    ) =>
            {
                self.count += 1;
                self.continuation.clone()
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

/// A straight-line continuation between one fragment exit and its next exit.
///
/// Exclusive paths are moved into the fragment. Shared paths are duplicated,
/// which is the standard tail-duplication step used to recover a single-entry,
/// single-exit region. Only transfer-free, normally completing nodes qualify,
/// and a hard path budget bounds code growth.
struct LinearContinuation {
    source: BlockId,
    target: BlockId,
    frontier: BlockId,
    blocks: Vec<BlockId>,
    use_kind: ContinuationUse,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ContinuationUse {
    Exclusive,
    Shared,
}

impl LinearContinuation {
    const DUPLICATION_BUDGET: usize = 32;

    fn analyze(graph: &SemanticFlowGraph) -> Result<Option<Self>, StructureError> {
        let predecessors = graph.predecessors();
        for (source, node) in &graph.nodes {
            let FlowTransfer::Fragment { normal: None, open } = &node.transfer else {
                continue;
            };
            if open.len() <= 1 {
                continue;
            }
            for target in open.iter().copied() {
                let mut blocks = Vec::new();
                let mut visited = BTreeSet::new();
                let mut expected_predecessor = *source;
                let mut current = target;
                let mut use_kind = ContinuationUse::Exclusive;
                loop {
                    if open.contains(&current) && current != target {
                        break;
                    }
                    let incoming = predecessors.get(&current);
                    if current == graph.entry
                        || graph.exits.contains(&current)
                        || graph.continues.contains_key(&current)
                        || !visited.insert(current)
                        || blocks.len() >= Self::DUPLICATION_BUDGET
                        || !incoming
                            .is_some_and(|incoming| incoming.contains(&expected_predecessor))
                    {
                        break;
                    }
                    if incoming.is_some_and(|incoming| incoming.len() != 1) {
                        use_kind = ContinuationUse::Shared;
                    }
                    let Some(continuation) = graph.nodes.get(&current) else {
                        break;
                    };
                    let completion = SemanticCompletion::analyze(&continuation.body);
                    if !completion.can_complete_normally() || !completion.is_transfer_free() {
                        break;
                    }
                    let FlowTransfer::Jump(next) = &continuation.transfer else {
                        break;
                    };
                    blocks.push(current);
                    expected_predecessor = current;
                    current = *next;
                }
                if !blocks.is_empty() && !blocks.contains(&current) {
                    if use_kind == ContinuationUse::Shared
                        && blocks.iter().any(|block| {
                            graph.nodes.get(block).is_some_and(|node| {
                                !LexicalIdentities::collect(&node.body).labels.is_empty()
                            })
                        })
                    {
                        continue;
                    }
                    return Ok(Some(Self {
                        source: *source,
                        target,
                        frontier: current,
                        blocks,
                        use_kind,
                    }));
                }
            }
        }
        Ok(None)
    }

    fn apply(self, graph: &mut SemanticFlowGraph) -> Result<(), StructureError> {
        let continuation = SemanticNode::sequence(
            self.blocks
                .iter()
                .map(|block| {
                    graph
                        .nodes
                        .get(block)
                        .map(|node| node.body.clone())
                        .ok_or(StructureError::MalformedFlowNode(*block))
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        let source = graph
            .nodes
            .get_mut(&self.source)
            .ok_or(StructureError::MalformedFlowNode(self.source))?;
        let mut binding = OwnedContinuationBinding {
            region: graph.region,
            target: self.target,
            frontier: self.frontier,
            continuation: &continuation,
            count: 0,
        };
        source.body =
            binding.fold_node(std::mem::replace(&mut source.body, SemanticNode::Empty))?;
        if binding.count == 0 {
            return Err(StructureError::MalformedFlowNode(self.source));
        }
        let FlowTransfer::Fragment { open, .. } = &mut source.transfer else {
            return Err(StructureError::MalformedFlowNode(self.source));
        };
        open.remove(&self.target);
        open.insert(self.frontier);
        if self.use_kind == ContinuationUse::Exclusive {
            for block in self.blocks {
                graph.nodes.remove(&block);
                graph.exits.remove(&block);
            }
        }
        Ok(())
    }
}

struct OwnedContinuationBinding<'a> {
    region: RegionId,
    target: BlockId,
    frontier: BlockId,
    continuation: &'a SemanticNode,
    count: usize,
}

impl SemanticFolder for OwnedContinuationBinding<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave)
                if leave.target == self.region
                    && matches!(
                        leave.kind,
                        SemanticLeaveKind::Jump(target) | SemanticLeaveKind::FallThrough(target)
                            if target == self.target
                    ) =>
            {
                self.count += 1;
                leave.kind = SemanticLeaveKind::Jump(self.frontier);
                SemanticNode::sequence([self.continuation.clone(), SemanticNode::Leave(leave)])
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

/// A switch-owned SESE subgraph in an already acyclic region graph.
///
/// Every arm is sliced at the switch postdominator. Shared arm nodes are kept in
/// each slice and therefore undergo standard node splitting when the slices are
/// reduced. This handles compiler decision DAGs without assigning one shared
/// node to an arbitrary case.
struct SwitchRegion {
    source: BlockId,
    selector: InsnArg,
    join: Option<BlockId>,
    arms: Vec<SwitchFlowArm>,
    nodes: BTreeSet<BlockId>,
}

struct SwitchFlowArm {
    entry: BlockId,
    values: Vec<i32>,
    is_default: bool,
    nodes: BTreeSet<BlockId>,
}

impl SwitchRegion {
    fn analyze(graph: &SemanticFlowGraph) -> Result<Option<Self>, StructureError> {
        let postdominators = PostDominators::analyze(graph)?;
        let predecessors = graph.predecessors();
        for source in graph.topological_order()? {
            let Some(FlowNode {
                transfer:
                    FlowTransfer::Switch {
                        selector,
                        cases,
                        default,
                    },
                ..
            }) = graph.nodes.get(&source)
            else {
                continue;
            };
            let Some(immediate) = postdominators.immediate_node(source) else {
                continue;
            };
            let join = match immediate {
                PostNode::Block(block) | PostNode::Boundary(block) => Some(block),
                PostNode::Exit => None,
            };
            if join == Some(source) || join.is_some_and(|join| graph.continues.contains_key(&join))
            {
                continue;
            }

            let mut labels = Vec::<(BlockId, Vec<i32>, bool)>::new();
            for (values, entry) in cases {
                match labels.iter_mut().find(|(target, _, _)| target == entry) {
                    Some((_, existing, _)) => existing.extend(values.iter().copied()),
                    None => labels.push((*entry, values.clone(), false)),
                }
            }
            if let Some(entry) = default {
                match labels.iter_mut().find(|(target, _, _)| target == entry) {
                    Some((_, _, is_default)) => *is_default = true,
                    None => labels.push((*entry, Vec::new(), true)),
                }
            }
            if labels.is_empty() {
                continue;
            }

            let mut arms = Vec::with_capacity(labels.len());
            let mut nodes = BTreeSet::new();
            let mut expanded = 0usize;
            let mut valid = true;
            for (entry, mut values, is_default) in labels {
                let arm = Self::arm(graph, source, entry, join);
                if Some(entry) != join && arm.is_empty() {
                    valid = false;
                    break;
                }
                expanded = expanded.saturating_add(arm.len());
                nodes.extend(arm.iter().copied());
                values.sort();
                values.dedup();
                arms.push(SwitchFlowArm {
                    entry,
                    values,
                    is_default,
                    nodes: arm,
                });
            }
            let budget = NodeSplittingBudget::for_graph(graph);
            if !valid || !budget.accepts(nodes.len(), expanded) {
                continue;
            }
            if nodes.iter().copied().any(|block| {
                predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .any(|predecessor| *predecessor != source && !nodes.contains(predecessor))
            }) {
                continue;
            }
            return Ok(Some(Self {
                source,
                selector: selector.clone(),
                join,
                arms,
                nodes,
            }));
        }
        Ok(None)
    }

    fn arm(
        graph: &SemanticFlowGraph,
        source: BlockId,
        entry: BlockId,
        join: Option<BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut nodes = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if Some(block) == join
                || block == source
                || graph.is_control_boundary(block)
                || !graph.nodes.contains_key(&block)
                || !nodes.insert(block)
            {
                continue;
            }
            pending.extend(graph.targets(block));
        }
        nodes
    }
}

/// Bounds semantic node splitting by graph-relative growth, independent of any
/// opcode or source-language shape.
struct NodeSplittingBudget {
    limit: usize,
}

impl NodeSplittingBudget {
    fn for_graph(graph: &SemanticFlowGraph) -> Self {
        Self {
            limit: graph.nodes.len().saturating_mul(8).saturating_add(128),
        }
    }

    fn accepts(&self, unique: usize, expanded: usize) -> bool {
        expanded >= unique && expanded <= self.limit
    }
}

struct BranchRegion {
    source: BlockId,
    when_true: BlockId,
    when_false: BlockId,
    join: BlockId,
    true_arm: BranchArm,
    false_arm: BranchArm,
}

impl BranchRegion {
    fn analyze(graph: &SemanticFlowGraph) -> Result<Option<Self>, StructureError> {
        let postdominators = PostDominators::analyze(graph)?;
        let predecessors = graph.predecessors();
        let order = graph.topological_order()?;
        let ranks = order
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, block)| (block, rank))
            .collect::<BTreeMap<_, _>>();
        for source in order.into_iter().rev() {
            let Some(FlowNode {
                transfer:
                    FlowTransfer::Branch {
                        when_true,
                        when_false,
                        ..
                    },
                ..
            }) = graph.nodes.get(&source)
            else {
                continue;
            };
            let joins = BranchJoins::analyze(
                graph,
                &postdominators,
                &predecessors,
                &ranks,
                source,
                *when_true,
                *when_false,
            );
            for join in joins.iter() {
                let Some(true_arm) = BranchArm::analyze(graph, &predecessors, *when_true, join)
                else {
                    continue;
                };
                let Some(false_arm) = BranchArm::analyze(graph, &predecessors, *when_false, join)
                else {
                    continue;
                };
                if true_arm.is_empty() && false_arm.is_empty()
                    || !true_arm.nodes.is_disjoint(&false_arm.nodes)
                    || !Self::single_entry(&predecessors, source, *when_true, &true_arm.nodes)
                    || !Self::single_entry(&predecessors, source, *when_false, &false_arm.nodes)
                {
                    continue;
                }
                return Ok(Some(Self {
                    source,
                    when_true: *when_true,
                    when_false: *when_false,
                    join,
                    true_arm,
                    false_arm,
                }));
            }
        }
        Ok(None)
    }

    fn single_entry(
        predecessors: &BTreeMap<BlockId, BTreeSet<BlockId>>,
        source: BlockId,
        entry: BlockId,
        arm: &BTreeSet<BlockId>,
    ) -> bool {
        if entry == source || arm.is_empty() {
            return true;
        }
        arm.iter().copied().all(|block| {
            predecessors
                .get(&block)
                .into_iter()
                .flatten()
                .all(|predecessor| {
                    arm.contains(predecessor) || (block == entry && *predecessor == source)
                })
        })
    }
}

struct BranchArm {
    nodes: BTreeSet<BlockId>,
    continuation: Option<ContinuationTail>,
}

impl BranchArm {
    fn analyze(
        graph: &SemanticFlowGraph,
        predecessors: &BTreeMap<BlockId, BTreeSet<BlockId>>,
        entry: BlockId,
        join: BlockId,
    ) -> Option<Self> {
        if entry == join {
            return Some(Self {
                nodes: BTreeSet::new(),
                continuation: None,
            });
        }
        let mut nodes = BTreeSet::new();
        let mut pending = vec![entry];
        let mut continuation = None::<ContinuationTail>;
        let mut reaches_join = false;
        let mut open_boundaries = BTreeSet::new();
        while let Some(block) = pending.pop() {
            if block == join {
                reaches_join = true;
                continue;
            }
            if let Some(tail) = ContinuationTail::analyze(graph, predecessors, block, join) {
                if continuation
                    .as_ref()
                    .is_some_and(|current| current.entry != tail.entry)
                {
                    return None;
                }
                continuation = Some(tail);
                continue;
            }
            if !nodes.insert(block) {
                continue;
            }
            if !graph.nodes.contains_key(&block) || graph.continues.contains_key(&block) {
                return None;
            }
            for target in graph.targets(block) {
                if target == join {
                    reaches_join = true;
                } else if graph.continues.contains_key(&target) || graph.exits.contains(&target) {
                    open_boundaries.insert(target);
                    continue;
                } else if graph.nodes.contains_key(&target) {
                    pending.push(target);
                } else {
                    return None;
                }
            }
        }
        if continuation.is_some() && reaches_join {
            return None;
        }
        if open_boundaries
            .iter()
            .any(|boundary| !graph.continues.contains_key(boundary))
        {
            return None;
        }
        if !reaches_join
            && continuation.is_none()
            && open_boundaries.is_empty()
            && !Self::is_closed(graph, &nodes)
        {
            return None;
        }
        Some(Self {
            nodes,
            continuation,
        })
    }

    fn is_closed(graph: &SemanticFlowGraph, nodes: &BTreeSet<BlockId>) -> bool {
        let terminals = nodes
            .iter()
            .filter_map(|block| {
                let node = graph.nodes.get(block)?;
                graph.targets(*block).is_empty().then_some(node)
            })
            .collect::<Vec<_>>();
        !terminals.is_empty()
            && terminals
                .iter()
                .all(|node| !SemanticCompletion::analyze(&node.body).can_complete_normally())
    }

    fn is_empty(&self) -> bool {
        self.nodes.is_empty() && self.continuation.is_none()
    }
}

/// A linear, uniquely-owned loop-continuation epilogue.
///
/// Shared tails remain graph joins. Cloning a semantically safe but shared
/// epilogue preserves behavior while destroying source-level control sharing.
struct ContinuationTail {
    entry: BlockId,
    blocks: Vec<BlockId>,
}

impl ContinuationTail {
    const BLOCK_BUDGET: usize = 32;

    fn analyze(
        graph: &SemanticFlowGraph,
        predecessors: &BTreeMap<BlockId, BTreeSet<BlockId>>,
        entry: BlockId,
        join: BlockId,
    ) -> Option<Self> {
        if predecessors
            .get(&entry)
            .is_some_and(|incoming| incoming.len() > 1)
        {
            return None;
        }
        let mut blocks = Vec::new();
        let mut visited = BTreeSet::new();
        let mut current = entry;
        loop {
            if current == join || blocks.len() >= Self::BLOCK_BUDGET || !visited.insert(current) {
                return None;
            }
            let node = graph.nodes.get(&current)?;
            let completion = SemanticCompletion::analyze(&node.body);
            blocks.push(current);
            if completion.is_continue_to_region(graph.region) {
                return matches!(node.transfer, FlowTransfer::Stop)
                    .then_some(Self { entry, blocks });
            }
            if !completion.can_complete_normally() || !completion.is_transfer_free() {
                return None;
            }
            let FlowTransfer::Jump(next) = &node.transfer else {
                return None;
            };
            current = *next;
        }
    }

    fn body(&self, graph: &SemanticFlowGraph) -> Result<SemanticNode, StructureError> {
        self.blocks
            .iter()
            .map(|block| {
                graph
                    .nodes
                    .get(block)
                    .map(|node| node.body.clone())
                    .ok_or(StructureError::MalformedFlowNode(*block))
            })
            .collect::<Result<Vec<_>, _>>()
            .map(SemanticNode::sequence)
    }
}

struct BranchJoins {
    blocks: Vec<BlockId>,
}

impl BranchJoins {
    fn analyze(
        graph: &SemanticFlowGraph,
        postdominators: &PostDominators,
        predecessors: &BTreeMap<BlockId, BTreeSet<BlockId>>,
        ranks: &BTreeMap<BlockId, usize>,
        source: BlockId,
        when_true: BlockId,
        when_false: BlockId,
    ) -> Self {
        let source_rank = ranks.get(&source).copied().unwrap_or(0);
        let reachable = Self::reachable(graph, [when_true, when_false]);
        let mut blocks = Vec::new();
        if let Some(join) = postdominators.immediate(source) {
            blocks.push(join);
        }
        blocks.extend([when_true, when_false]);
        blocks.extend(predecessors.iter().filter_map(|(block, incoming)| {
            (incoming.len() > 1 && reachable.contains(block)).then_some(*block)
        }));
        blocks.retain(|block| {
            if graph.is_control_boundary(*block) {
                true
            } else {
                ranks.get(block).is_some_and(|rank| *rank > source_rank)
            }
        });
        blocks.sort_by_key(|block| {
            (
                !graph.is_control_boundary(*block),
                ranks.get(block).copied().unwrap_or(usize::MAX),
            )
        });
        blocks.dedup();
        Self { blocks }
    }

    fn reachable(
        graph: &SemanticFlowGraph,
        entries: impl IntoIterator<Item = BlockId>,
    ) -> BTreeSet<BlockId> {
        let mut reached = BTreeSet::new();
        let mut pending = entries.into_iter().collect::<Vec<_>>();
        while let Some(block) = pending.pop() {
            if !graph.nodes.contains_key(&block)
                || graph.continues.contains_key(&block)
                || !reached.insert(block)
            {
                continue;
            }
            pending.extend(graph.targets(block));
        }
        reached
    }

    fn iter(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.blocks.iter().copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PostNode {
    Block(BlockId),
    Boundary(BlockId),
    Exit,
}

struct PostDominators {
    nodes: Vec<PostNode>,
    indices: BTreeMap<PostNode, usize>,
    domains: Vec<PostDomain>,
}

impl PostDominators {
    fn analyze(graph: &SemanticFlowGraph) -> Result<Self, StructureError> {
        let order = graph.topological_order()?;
        let nodes = order
            .iter()
            .copied()
            .map(PostNode::Block)
            .chain(
                order
                    .iter()
                    .copied()
                    .flat_map(|block| graph.targets(block))
                    .filter(|target| graph.is_control_boundary(*target))
                    .map(PostNode::Boundary),
            )
            .chain(std::iter::once(PostNode::Exit))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let indices = nodes
            .iter()
            .copied()
            .enumerate()
            .map(|(index, node)| (node, index))
            .collect::<BTreeMap<_, _>>();
        let exit = indices
            .get(&PostNode::Exit)
            .copied()
            .ok_or(StructureError::MalformedFlowGraph(graph.region))?;
        let mut domains = nodes
            .iter()
            .enumerate()
            .map(|(index, node)| match node {
                PostNode::Block(_) => PostDomain::full(nodes.len()),
                PostNode::Boundary(_) => PostDomain::edge(nodes.len(), index, exit),
                PostNode::Exit => PostDomain::singleton(nodes.len(), index),
            })
            .collect::<Vec<_>>();
        let transfers = order
            .iter()
            .copied()
            .map(|block| {
                let node = indices
                    .get(&PostNode::Block(block))
                    .copied()
                    .ok_or(StructureError::MalformedFlowNode(block))?;
                let successors = Self::successors(graph, block)
                    .into_iter()
                    .map(|successor| {
                        indices.get(&successor).copied().ok_or_else(|| {
                            let block = match successor {
                                PostNode::Block(block) | PostNode::Boundary(block) => block,
                                PostNode::Exit => block,
                            };
                            StructureError::MalformedFlowNode(block)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((node, successors))
            })
            .collect::<Result<Vec<_>, StructureError>>()?;

        loop {
            let mut changed = false;
            for (node, successors) in transfers.iter().rev() {
                let mut successors = successors.iter().copied();
                let first = successors.next().ok_or(StructureError::MalformedFlowNode(
                    match nodes[*node] {
                        PostNode::Block(block) | PostNode::Boundary(block) => block,
                        PostNode::Exit => graph.entry,
                    },
                ))?;
                let mut domain = domains[first].clone();
                for successor in successors {
                    domain.intersect_with(&domains[successor]);
                }
                domain.insert(*node);
                let slot = &mut domains[*node];
                if *slot != domain {
                    *slot = domain;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Ok(Self {
            nodes,
            indices,
            domains,
        })
    }

    fn successors(graph: &SemanticFlowGraph, block: BlockId) -> BTreeSet<PostNode> {
        let targets = graph.targets(block);
        if targets.is_empty() {
            return BTreeSet::from([PostNode::Exit]);
        }
        targets
            .into_iter()
            .map(|target| {
                if !graph.is_control_boundary(target) {
                    PostNode::Block(target)
                } else {
                    PostNode::Boundary(target)
                }
            })
            .collect()
    }

    fn immediate(&self, block: BlockId) -> Option<BlockId> {
        match self.immediate_node(block)? {
            PostNode::Block(block) | PostNode::Boundary(block) => Some(block),
            PostNode::Exit => None,
        }
    }

    fn immediate_node(&self, block: BlockId) -> Option<PostNode> {
        let source = self.indices.get(&PostNode::Block(block)).copied()?;
        let strict = self
            .domains
            .get(source)?
            .members(self.nodes.len())
            .filter(|candidate| *candidate != source)
            .collect::<Vec<_>>();
        strict
            .into_iter()
            .max_by_key(|candidate| self.domains[*candidate].count())
            .map(|candidate| self.nodes[candidate])
    }
}

#[derive(Clone, PartialEq, Eq)]
struct PostDomain {
    words: Vec<u64>,
}

impl PostDomain {
    fn full(bits: usize) -> Self {
        let mut domain = Self {
            words: vec![u64::MAX; bits.div_ceil(u64::BITS as usize)],
        };
        let remainder = bits % u64::BITS as usize;
        if remainder != 0 {
            if let Some(last) = domain.words.last_mut() {
                *last = (1u64 << remainder) - 1;
            }
        }
        domain
    }

    fn singleton(bits: usize, member: usize) -> Self {
        let mut domain = Self {
            words: vec![0; bits.div_ceil(u64::BITS as usize)],
        };
        domain.insert(member);
        domain
    }

    fn edge(bits: usize, node: usize, successor: usize) -> Self {
        let mut domain = Self::singleton(bits, successor);
        domain.insert(node);
        domain
    }

    fn insert(&mut self, member: usize) {
        self.words[member / u64::BITS as usize] |= 1 << (member % u64::BITS as usize);
    }

    fn intersect_with(&mut self, other: &Self) {
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left &= *right;
        }
    }

    fn members(&self, limit: usize) -> impl Iterator<Item = usize> + '_ {
        (0..limit).filter(|member| {
            self.words[*member / u64::BITS as usize] & (1 << (*member % u64::BITS as usize)) != 0
        })
    }

    fn count(&self) -> u32 {
        self.words.iter().map(|word| word.count_ones()).sum()
    }
}

struct AcyclicLabelLowering<'a> {
    graph: &'a SemanticFlowGraph,
    nodes: BTreeSet<BlockId>,
    labels: BTreeMap<BlockId, SemanticLabel>,
    next_id: u32,
}

impl<'a> AcyclicLabelLowering<'a> {
    fn new(graph: &'a SemanticFlowGraph) -> Result<Self, StructureError> {
        let mut identities = LexicalIdentities::default();
        identities.labels.extend(
            graph
                .continues
                .values()
                .map(|continuation| continuation.label),
        );
        for node in graph.nodes.values() {
            identities.visit_node(&node.body);
        }
        let reserved = identities
            .labels
            .iter()
            .filter(|label| label.region == graph.region)
            .map(|label| label.block.raw())
            .max()
            .map(|block| {
                block
                    .checked_add(1)
                    .ok_or(StructureError::GraphNodeIdExhausted(graph.region))
            })
            .transpose()?
            .unwrap_or(0);
        let mut next_id = graph.next_id.max(reserved);
        let mut labels = BTreeMap::new();
        for target in graph.nodes.keys().chain(graph.exits.iter()).copied() {
            if graph.continues.contains_key(&target) || labels.contains_key(&target) {
                continue;
            }
            let block = BlockId::new(next_id);
            next_id = next_id
                .checked_add(1)
                .ok_or(StructureError::GraphNodeIdExhausted(graph.region))?;
            labels.insert(target, SemanticLabel::block(graph.region, block));
        }
        Ok(Self {
            graph,
            nodes: graph.nodes.keys().copied().collect(),
            labels,
            next_id,
        })
    }

    fn next_id(&self) -> u32 {
        self.next_id
    }

    fn lower(&self) -> Result<SemanticNode, StructureError> {
        let order = self.graph.topological_order()?;
        let ranks = order
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, node)| (node, rank))
            .collect::<BTreeMap<_, _>>();
        let mut intervals = BTreeMap::<BlockId, usize>::new();
        for (index, block) in order.iter().copied().enumerate() {
            let next = order.get(index + 1).copied();
            let node = self
                .graph
                .nodes
                .get(&block)
                .ok_or(StructureError::MalformedFlowNode(block))?;
            for target in node.transfer.targets().into_iter().filter(|target| {
                self.nodes.contains(target)
                    && !self.graph.continues.contains_key(target)
                    && (matches!(&node.transfer, FlowTransfer::Switch { .. })
                        || Some(*target) != next)
            }) {
                self.record_interval(&ranks, &mut intervals, index, target)?;
            }
            let body = self.body(node, next);
            let mut collector = OpenTargetCollector::new(self.graph.region);
            collector.visit_node(&body);
            for target in collector.targets.into_iter().filter(|target| {
                self.nodes.contains(target) && !self.graph.continues.contains_key(target)
            }) {
                self.record_interval(&ranks, &mut intervals, index, target)?;
            }
        }

        let mut lowered = Vec::with_capacity(order.len());
        for (index, block) in order.iter().copied().enumerate() {
            let next = order.get(index + 1).copied();
            let node = self
                .graph
                .nodes
                .get(&block)
                .ok_or(StructureError::MalformedFlowNode(block))?;
            let body = self.body(node, next);
            let body = OpenTargetBinding::new(self).fold_node(body)?;
            let transfer = self.transfer(&node.transfer, next)?;
            lowered.push(SemanticNode::sequence([body, transfer]));
        }
        if ranks.get(&self.graph.entry).copied() != Some(0) {
            return Err(StructureError::MalformedFlowGraph(self.graph.region));
        }
        let body = LabelLayout::analyze(self.graph.region, &order, intervals)?
            .lower(lowered, &self.labels)?;
        let body = self
            .graph
            .exits
            .iter()
            .filter(|exit| !self.graph.continues.contains_key(exit))
            .rev()
            .fold(body, |body, exit| SemanticNode::Label {
                label: self.label(*exit),
                body: Box::new(body),
            });
        Ok(body)
    }

    fn body(&self, node: &FlowNode, next: Option<BlockId>) -> SemanticNode {
        if matches!(&node.transfer, FlowTransfer::Fragment { .. }) {
            node.body.clone()
        } else {
            NaturalFallthrough::strip(self.graph.region, node.body.clone(), next)
        }
    }

    fn record_interval(
        &self,
        ranks: &BTreeMap<BlockId, usize>,
        intervals: &mut BTreeMap<BlockId, usize>,
        source: usize,
        target: BlockId,
    ) -> Result<(), StructureError> {
        let target_rank = ranks
            .get(&target)
            .copied()
            .ok_or(StructureError::MalformedFlowNode(target))?;
        if target_rank <= source {
            return Err(StructureError::CyclicFlowGraph(self.graph.region));
        }
        intervals
            .entry(target)
            .and_modify(|start| *start = (*start).min(source))
            .or_insert(source);
        Ok(())
    }

    fn transfer(
        &self,
        transfer: &FlowTransfer,
        next: Option<BlockId>,
    ) -> Result<SemanticNode, StructureError> {
        Ok(match transfer {
            FlowTransfer::Fragment { normal, .. } => normal
                .map(|target| self.action(target, next))
                .unwrap_or(SemanticNode::Empty),
            FlowTransfer::Stop => SemanticNode::Empty,
            FlowTransfer::Jump(target) => self.action(*target, next),
            FlowTransfer::Branch {
                condition,
                when_true,
                when_false,
            } => SemanticNode::branch(
                condition.clone(),
                self.action(*when_true, next),
                Some(self.action(*when_false, next)),
            ),
            FlowTransfer::Switch {
                selector,
                cases,
                default,
            } => SemanticNode::Switch {
                region: None,
                selector: crate::ir::SemanticOperand::new(
                    crate::ir::SemanticExpression::from_argument(selector.clone())?,
                ),
                cases: cases
                    .iter()
                    .map(|(values, target)| SemanticSwitchCase {
                        values: values.clone(),
                        is_default: false,
                        body: self.action(*target, None),
                    })
                    .chain(default.iter().map(|target| SemanticSwitchCase {
                        values: Vec::new(),
                        is_default: true,
                        body: self.action(*target, None),
                    }))
                    .collect(),
            },
        })
    }

    fn action(&self, target: BlockId, next: Option<BlockId>) -> SemanticNode {
        if let Some(label) = self.graph.continues.get(&target) {
            return self.leave(SemanticLeaveKind::ContinueLabel(label.label));
        }
        if self.graph.exits.contains(&target) {
            return self.leave(SemanticLeaveKind::BreakLabel(self.label(target)));
        }
        if !self.nodes.contains(&target) {
            return self.leave(SemanticLeaveKind::Jump(target));
        }
        if Some(target) == next {
            return SemanticNode::Empty;
        }
        self.leave(SemanticLeaveKind::BreakLabel(self.label(target)))
    }

    fn embedded_action(&self, target: BlockId) -> SemanticNode {
        if let Some(label) = self.graph.continues.get(&target) {
            return self.leave(SemanticLeaveKind::ContinueLabel(label.label));
        }
        self.action(target, None)
    }

    fn leave(&self, kind: SemanticLeaveKind) -> SemanticNode {
        SemanticNode::Leave(crate::ir::SemanticLeave {
            site: None,
            condition: None,
            kind,
            edge: None,
            origin: None,
            source: self.graph.region,
            destination: self.graph.region,
            target: self.graph.region,
            cleanup: Vec::new(),
        })
    }

    fn label(&self, block: BlockId) -> SemanticLabel {
        self.labels
            .get(&block)
            .copied()
            .expect("acyclic lexical target has allocated label")
    }
}

#[derive(Debug, Clone)]
struct LabelInterval {
    target: Option<BlockId>,
    start: usize,
    end: usize,
    children: Vec<usize>,
}

struct LabelLayout {
    region: RegionId,
    intervals: Vec<LabelInterval>,
}

impl LabelLayout {
    fn analyze(
        region: RegionId,
        order: &[BlockId],
        starts: BTreeMap<BlockId, usize>,
    ) -> Result<Self, StructureError> {
        let ranks = order
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, block)| (block, rank))
            .collect::<BTreeMap<_, _>>();
        let mut intervals = starts
            .into_iter()
            .map(|(target, start)| {
                let end = ranks
                    .get(&target)
                    .copied()
                    .ok_or(StructureError::MalformedFlowNode(target))?;
                Ok(LabelInterval {
                    target: Some(target),
                    start,
                    end,
                    children: Vec::new(),
                })
            })
            .collect::<Result<Vec<_>, StructureError>>()?;
        Self::close_crossing_intervals(&mut intervals);
        intervals.push(LabelInterval {
            target: None,
            start: 0,
            end: order.len(),
            children: Vec::new(),
        });
        let root = intervals.len() - 1;
        for child in 0..root {
            let parent = (0..intervals.len())
                .filter(|candidate| *candidate != child)
                .filter(|candidate| Self::contains(&intervals[*candidate], &intervals[child]))
                .min_by_key(|candidate| {
                    intervals[*candidate]
                        .end
                        .saturating_sub(intervals[*candidate].start)
                })
                .ok_or(StructureError::MalformedFlowGraph(region))?;
            intervals[parent].children.push(child);
        }
        let bounds = intervals
            .iter()
            .map(|interval| (interval.start, interval.end))
            .collect::<Vec<_>>();
        for interval in &mut intervals {
            interval.children.sort_by_key(|child| {
                let (start, end) = bounds[*child];
                (start, std::cmp::Reverse(end))
            });
        }
        Ok(Self { region, intervals })
    }

    fn close_crossing_intervals(intervals: &mut [LabelInterval]) {
        loop {
            let mut changed = false;
            for left in 0..intervals.len() {
                for right in 0..intervals.len() {
                    if intervals[left].start < intervals[right].start
                        && intervals[right].start < intervals[left].end
                        && intervals[left].end < intervals[right].end
                    {
                        intervals[right].start = intervals[left].start;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn contains(parent: &LabelInterval, child: &LabelInterval) -> bool {
        parent.start <= child.start
            && child.end <= parent.end
            && (parent.start < child.start || child.end < parent.end)
    }

    fn lower(
        &self,
        nodes: Vec<SemanticNode>,
        labels: &BTreeMap<BlockId, SemanticLabel>,
    ) -> Result<SemanticNode, StructureError> {
        let root = self.intervals.len() - 1;
        let mut bodies = BTreeMap::<usize, SemanticNode>::new();
        let mut postorder = (0..self.intervals.len()).collect::<Vec<_>>();
        postorder.sort_by_key(|interval| {
            self.intervals[*interval]
                .end
                .saturating_sub(self.intervals[*interval].start)
        });
        for interval_id in postorder {
            let interval = &self.intervals[interval_id];
            let mut children = interval.children.iter().copied().peekable();
            let mut position = interval.start;
            let mut sequence = Vec::new();
            while position < interval.end {
                if let Some(child) = children.peek().copied() {
                    let child_interval = &self.intervals[child];
                    if child_interval.start == position {
                        let body = bodies
                            .remove(&child)
                            .ok_or(StructureError::MalformedFlowGraph(self.region))?;
                        let target = child_interval
                            .target
                            .ok_or(StructureError::MalformedFlowGraph(self.region))?;
                        let label = labels
                            .get(&target)
                            .copied()
                            .ok_or(StructureError::MalformedFlowNode(target))?;
                        sequence.push(SemanticNode::Label {
                            label,
                            body: Box::new(body),
                        });
                        position = child_interval.end;
                        children.next();
                        continue;
                    }
                }
                sequence.push(
                    nodes
                        .get(position)
                        .cloned()
                        .ok_or(StructureError::MalformedFlowGraph(self.region))?,
                );
                position += 1;
            }
            if children.next().is_some() {
                return Err(StructureError::MalformedFlowGraph(self.region));
            }
            bodies.insert(interval_id, SemanticNode::sequence(sequence));
        }
        bodies
            .remove(&root)
            .ok_or(StructureError::MalformedFlowGraph(self.region))
    }
}

struct OpenTargetBinding<'a> {
    lowering: &'a AcyclicLabelLowering<'a>,
}

impl<'a> OpenTargetBinding<'a> {
    fn new(lowering: &'a AcyclicLabelLowering<'a>) -> Self {
        Self { lowering }
    }
}

impl SemanticFolder for OpenTargetBinding<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave) => {
                if leave.target != self.lowering.graph.region {
                    return Ok(SemanticNode::Leave(leave));
                }
                let target = match leave.kind {
                    SemanticLeaveKind::Jump(target) | SemanticLeaveKind::FallThrough(target) => {
                        target
                    }
                    _ => return Ok(SemanticNode::Leave(leave)),
                };
                match self.lowering.embedded_action(target) {
                    SemanticNode::Leave(action) => {
                        leave.kind = action.kind;
                        SemanticNode::Leave(leave)
                    }
                    SemanticNode::Empty => SemanticNode::Empty,
                    _ => return Err(SemanticFoldError::MalformedWorkStack),
                }
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

struct NaturalFallthrough;

impl NaturalFallthrough {
    fn strip(region: RegionId, node: SemanticNode, next: Option<BlockId>) -> SemanticNode {
        let Some(next) = next else {
            return node;
        };
        match node {
            SemanticNode::Sequence(mut nodes) => {
                if nodes
                    .last()
                    .is_some_and(|node| Self::targets(node, region, next))
                {
                    nodes.pop();
                }
                SemanticNode::sequence(nodes)
            }
            node if Self::targets(&node, region, next) => SemanticNode::Empty,
            node => node,
        }
    }

    fn targets(node: &SemanticNode, region: RegionId, target: BlockId) -> bool {
        matches!(
            node,
            SemanticNode::Leave(crate::ir::SemanticLeave {
                kind: SemanticLeaveKind::Jump(block) | SemanticLeaveKind::FallThrough(block),
                target: leave_target,
                ..
            }) if *leave_target == region && *block == target
        )
    }
}

struct OpenTargetRemap<'a> {
    region: RegionId,
    mapping: &'a BTreeMap<BlockId, BlockId>,
}

impl<'a> OpenTargetRemap<'a> {
    fn new(region: RegionId, mapping: &'a BTreeMap<BlockId, BlockId>) -> Self {
        Self { region, mapping }
    }
}

impl SemanticFolder for OpenTargetRemap<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave) => {
                if leave.target == self.region {
                    match &mut leave.kind {
                        SemanticLeaveKind::Jump(target)
                        | SemanticLeaveKind::FallThrough(target) => {
                            if let Some(replacement) = self.mapping.get(target) {
                                *target = *replacement;
                            }
                        }
                        _ => {}
                    }
                }
                SemanticNode::Leave(leave)
            }
            node => node,
        })
    }
}

struct OpenTargetCollector {
    region: RegionId,
    targets: BTreeSet<BlockId>,
}

impl OpenTargetCollector {
    fn new(region: RegionId) -> Self {
        Self {
            region,
            targets: BTreeSet::new(),
        }
    }
}

impl SemanticVisitor for OpenTargetCollector {
    fn enter_node(&mut self, node: &SemanticNode) {
        let SemanticNode::Leave(leave) = node else {
            return;
        };
        if leave.target != self.region {
            return;
        }
        if let SemanticLeaveKind::Jump(target) | SemanticLeaveKind::FallThrough(target) = leave.kind
        {
            self.targets.insert(target);
        }
    }
}

struct OpenTargetUseCounter {
    region: RegionId,
    target: BlockId,
    count: usize,
}

impl OpenTargetUseCounter {
    fn count(region: RegionId, node: &SemanticNode, target: BlockId) -> usize {
        let mut counter = Self {
            region,
            target,
            count: 0,
        };
        counter.visit_node(node);
        counter.count
    }
}

impl SemanticVisitor for OpenTargetUseCounter {
    fn enter_node(&mut self, node: &SemanticNode) {
        if matches!(
            node,
            SemanticNode::Leave(crate::ir::SemanticLeave {
                kind:
                    SemanticLeaveKind::Jump(target) | SemanticLeaveKind::FallThrough(target),
                target: region,
                ..
            }) if *region == self.region && *target == self.target
        ) {
            self.count += 1;
        }
    }
}

#[derive(Default)]
struct LexicalIdentities {
    labels: BTreeSet<SemanticLabel>,
}

impl LexicalIdentities {
    fn collect(node: &SemanticNode) -> Self {
        let mut identities = Self::default();
        identities.visit_node(node);
        identities
    }
}

#[derive(Default)]
struct LexicalBindings {
    labels: BTreeSet<SemanticLabel>,
}

impl SemanticVisitor for LexicalBindings {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::Label { label, .. } => {
                self.labels.insert(*label);
            }
            SemanticNode::Loop {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            } => {
                self.labels.insert(*label);
            }
            _ => {}
        }
    }
}

struct LexicalAlphaRenaming<'a> {
    mapping: &'a BTreeMap<SemanticLabel, SemanticLabel>,
}

impl<'a> LexicalAlphaRenaming<'a> {
    fn new(mapping: &'a BTreeMap<SemanticLabel, SemanticLabel>) -> Self {
        Self { mapping }
    }

    fn label(&self, label: SemanticLabel) -> SemanticLabel {
        self.mapping.get(&label).copied().unwrap_or(label)
    }

    fn control(&self, control: crate::ir::SemanticLoopControl) -> crate::ir::SemanticLoopControl {
        match control {
            crate::ir::SemanticLoopControl::Label(label) => {
                crate::ir::SemanticLoopControl::Label(self.label(label))
            }
            control => control,
        }
    }
}

impl SemanticFolder for LexicalAlphaRenaming<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Label { label, body } => SemanticNode::Label {
                label: self.label(label),
                body,
            },
            SemanticNode::Loop {
                control,
                header,
                kind,
                test,
                body,
            } => SemanticNode::Loop {
                control: self.control(control),
                header,
                kind,
                test,
                body,
            },
            SemanticNode::For {
                control,
                init,
                condition,
                update,
                body,
            } => SemanticNode::For {
                control: self.control(control),
                init,
                condition,
                update,
                body,
            },
            SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body,
            } => SemanticNode::ForEach {
                control: self.control(control),
                variable,
                iterable,
                body,
            },
            SemanticNode::Leave(mut leave) => {
                leave.kind = match leave.kind {
                    SemanticLeaveKind::BreakLabel(label) => {
                        SemanticLeaveKind::BreakLabel(self.label(label))
                    }
                    SemanticLeaveKind::ContinueLabel(label) => {
                        SemanticLeaveKind::ContinueLabel(self.label(label))
                    }
                    kind => kind,
                };
                SemanticNode::Leave(leave)
            }
            node => node,
        })
    }
}

impl SemanticVisitor for LexicalIdentities {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::Label { label, .. } => {
                self.labels.insert(*label);
            }
            SemanticNode::Loop {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: crate::ir::SemanticLoopControl::Label(label),
                ..
            } => {
                self.labels.insert(*label);
            }
            SemanticNode::Leave(leave) => match leave.kind {
                SemanticLeaveKind::BreakLabel(label) | SemanticLeaveKind::ContinueLabel(label) => {
                    self.labels.insert(label);
                }
                _ => {}
            },
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct LeaveSummary {
        boundary: SemanticLabel,
        boundary_exits: usize,
        returns: usize,
    }

    impl SemanticVisitor for LeaveSummary {
        fn enter_node(&mut self, node: &SemanticNode) {
            let SemanticNode::Leave(leave) = node else {
                return;
            };
            match leave.kind {
                SemanticLeaveKind::BreakLabel(label) if label == self.boundary => {
                    self.boundary_exits += 1;
                }
                SemanticLeaveKind::Return(_) => self.returns += 1,
                _ => {}
            }
        }
    }

    #[test]
    fn fragment_boundary_excludes_lexically_bound_targets() {
        let region = RegionId::new(0);
        let source = BlockId::new(1);
        let open = BlockId::new(2);
        let bound = BlockId::new(3);
        let body = SemanticNode::Leave(crate::ir::SemanticLeave {
            site: None,
            condition: None,
            kind: SemanticLeaveKind::Jump(open),
            edge: None,
            origin: None,
            source: region,
            destination: region,
            target: region,
            cleanup: Vec::new(),
        });
        let boundary = FlowBoundary::analyze(region, &body, BTreeSet::from([open, bound]))
            .bind_targets([bound]);

        let transfer =
            FlowTransfer::fragment(source, &body, boundary).expect("classified boundary");

        assert!(matches!(
            transfer,
            FlowTransfer::Fragment {
                normal: None,
                open: targets,
            } if targets == BTreeSet::from([open])
        ));
    }

    #[test]
    fn fragment_exit_uses_distinct_block_label() {
        let region = RegionId::new(0);
        let source = BlockId::new(1);
        let target = BlockId::new(9);
        let mut graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([(
                source,
                FlowNode {
                    body: SemanticNode::Leave(crate::ir::SemanticLeave {
                        site: None,
                        condition: None,
                        kind: SemanticLeaveKind::Jump(target),
                        edge: None,
                        origin: None,
                        source: region,
                        destination: region,
                        target: region,
                        cleanup: Vec::new(),
                    }),
                    transfer: FlowTransfer::Fragment {
                        normal: None,
                        open: BTreeSet::from([target]),
                    },
                },
            )]),
            next_id: 10,
            continues: BTreeMap::new(),
            exits: BTreeSet::new(),
        };

        FragmentNormalizer::normalize(&mut graph, source).expect("fragment normalization");

        let node = graph.nodes.get(&source).expect("source node");
        assert!(matches!(node.transfer, FlowTransfer::Jump(exit) if exit == target));
        assert!(matches!(
            &node.body,
            SemanticNode::Label { label, body }
                if *label == SemanticLabel::block(region, BlockId::new(10))
                    && matches!(
                        body.as_ref(),
                        SemanticNode::Leave(crate::ir::SemanticLeave {
                            kind: SemanticLeaveKind::BreakLabel(exit),
                            ..
                        }) if *exit == *label
                    )
        ));
    }

    #[test]
    fn acyclic_cfg_models_declared_exit_as_empty_sink() {
        let entry = BlockId::new(0);
        let branch = BlockId::new(1);
        let exit = BlockId::new(2);
        let graph = SemanticFlowGraph {
            region: RegionId::new(0),
            entry,
            nodes: BTreeMap::from([
                (
                    entry,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Branch {
                            condition: SemanticPredicate::True,
                            when_true: branch,
                            when_false: exit,
                        },
                    },
                ),
                (
                    branch,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(exit),
                    },
                ),
            ]),
            next_id: 3,
            continues: BTreeMap::new(),
            exits: BTreeSet::from([exit]),
        };

        let (cfg, _) = graph
            .acyclic_cfg()
            .expect("acyclic CFG analysis")
            .expect("declared exit sink");

        assert!(cfg.is_graph_node(exit));
        assert!(cfg.has_edge(entry, exit));
        assert!(cfg.has_edge(branch, exit));
    }

    #[test]
    fn branch_join_rejects_an_arm_that_crosses_an_open_boundary() {
        let region = RegionId::new(0);
        let source = BlockId::new(0);
        let join = BlockId::new(1);
        let arm = BlockId::new(2);
        let exit = BlockId::new(3);
        let graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Branch {
                            condition: SemanticPredicate::True,
                            when_true: join,
                            when_false: arm,
                        },
                    },
                ),
                (
                    arm,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(exit),
                    },
                ),
            ]),
            next_id: 4,
            continues: BTreeMap::new(),
            exits: BTreeSet::from([join, exit]),
        };

        assert!(BranchRegion::analyze(&graph)
            .expect("branch analysis")
            .is_none());
    }

    #[test]
    fn branch_join_accepts_an_arm_closed_by_semantic_return() {
        let region = RegionId::new(0);
        let source = BlockId::new(0);
        let join = BlockId::new(1);
        let terminal = BlockId::new(2);
        let graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Branch {
                            condition: SemanticPredicate::True,
                            when_true: join,
                            when_false: terminal,
                        },
                    },
                ),
                (
                    terminal,
                    FlowNode {
                        body: SemanticNode::Leave(crate::ir::SemanticLeave {
                            site: None,
                            condition: None,
                            kind: SemanticLeaveKind::Return(None),
                            edge: None,
                            origin: None,
                            source: region,
                            destination: region,
                            target: region,
                            cleanup: Vec::new(),
                        }),
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 3,
            continues: BTreeMap::new(),
            exits: BTreeSet::from([join]),
        };

        let branch = BranchRegion::analyze(&graph)
            .expect("branch analysis")
            .expect("closed branch arm");
        assert_eq!(branch.join, join);
    }

    #[test]
    fn postdominators_unify_distinct_control_boundaries_at_virtual_exit() {
        let source = BlockId::new(0);
        let left_exit = BlockId::new(1);
        let right_exit = BlockId::new(2);
        let graph = SemanticFlowGraph {
            region: RegionId::new(0),
            entry: source,
            nodes: BTreeMap::from([(
                source,
                FlowNode {
                    body: SemanticNode::Empty,
                    transfer: FlowTransfer::Branch {
                        condition: SemanticPredicate::True,
                        when_true: left_exit,
                        when_false: right_exit,
                    },
                },
            )]),
            next_id: 3,
            continues: BTreeMap::new(),
            exits: BTreeSet::from([left_exit, right_exit]),
        };

        let postdominators = PostDominators::analyze(&graph).expect("postdominator analysis");

        assert_eq!(postdominators.immediate_node(source), Some(PostNode::Exit));
    }

    #[test]
    fn label_lowering_keeps_fragment_exit_distinct_from_internal_terminal() {
        let region = RegionId::new(0);
        let source = BlockId::new(0);
        let terminal = BlockId::new(1);
        let exit = BlockId::new(2);
        let leave = |target| {
            SemanticNode::Leave(crate::ir::SemanticLeave {
                site: None,
                condition: None,
                kind: SemanticLeaveKind::Jump(target),
                edge: None,
                origin: None,
                source: region,
                destination: region,
                target: region,
                cleanup: Vec::new(),
            })
        };
        let graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::If {
                            condition: crate::ir::SemanticOperand::new(SemanticPredicate::True),
                            then_node: Box::new(leave(exit)),
                            else_node: Some(Box::new(leave(terminal))),
                        },
                        transfer: FlowTransfer::Fragment {
                            normal: None,
                            open: BTreeSet::from([terminal, exit]),
                        },
                    },
                ),
                (
                    terminal,
                    FlowNode {
                        body: SemanticNode::Leave(crate::ir::SemanticLeave {
                            site: None,
                            condition: None,
                            kind: SemanticLeaveKind::Return(None),
                            edge: None,
                            origin: None,
                            source: region,
                            destination: region,
                            target: region,
                            cleanup: Vec::new(),
                        }),
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 3,
            continues: BTreeMap::new(),
            exits: BTreeSet::from([exit]),
        };

        let body = AcyclicLabelLowering::new(&graph)
            .expect("label allocation")
            .lower()
            .expect("acyclic label lowering");
        let SemanticNode::Label {
            label: boundary, ..
        } = &body
        else {
            panic!("declared exit must own one lexical label");
        };
        let mut summary = LeaveSummary {
            boundary: *boundary,
            boundary_exits: 0,
            returns: 0,
        };
        summary.visit_node(&body);
        assert_eq!(summary.boundary_exits, 1);
        assert_eq!(summary.returns, 1);
    }

    #[test]
    fn branch_region_closes_a_linear_loop_continuation_tail() {
        let source = BlockId::new(0);
        let join = BlockId::new(1);
        let tail_entry = BlockId::new(2);
        let update = BlockId::new(3);
        let continuation = BlockId::new(4);
        let region = RegionId::new(5);
        let graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Branch {
                            condition: SemanticPredicate::True,
                            when_true: join,
                            when_false: tail_entry,
                        },
                    },
                ),
                (
                    join,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Stop,
                    },
                ),
                (
                    tail_entry,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(update),
                    },
                ),
                (
                    update,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(continuation),
                    },
                ),
                (
                    continuation,
                    FlowNode {
                        body: SemanticNode::Leave(crate::ir::SemanticLeave {
                            site: None,
                            condition: None,
                            kind: SemanticLeaveKind::Continue,
                            edge: None,
                            origin: None,
                            source: region,
                            destination: region,
                            target: region,
                            cleanup: Vec::new(),
                        }),
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 6,
            continues: BTreeMap::new(),
            exits: BTreeSet::new(),
        };

        let branch = BranchRegion::analyze(&graph)
            .expect("branch analysis")
            .expect("branch with loop continuation tail");

        assert_eq!(branch.join, join);
        assert!(branch.true_arm.is_empty());
        let tail = branch
            .false_arm
            .continuation
            .expect("closed continuation tail");
        assert_eq!(tail.entry, tail_entry);
        assert_eq!(tail.blocks, vec![tail_entry, update, continuation]);
    }

    #[test]
    fn branch_region_joins_at_shared_continuation_boundary() {
        let source = BlockId::new(0);
        let when_true = BlockId::new(1);
        let when_false = BlockId::new(2);
        let continuation = BlockId::new(9);
        let region = RegionId::new(0);
        let graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Branch {
                            condition: SemanticPredicate::True,
                            when_true,
                            when_false,
                        },
                    },
                ),
                (
                    when_true,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(continuation),
                    },
                ),
                (
                    when_false,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(continuation),
                    },
                ),
            ]),
            next_id: 10,
            continues: BTreeMap::from([(
                continuation,
                LoopContinuation::unscoped(SemanticLabel::loop_(region, continuation)),
            )]),
            exits: BTreeSet::new(),
        };

        let branch = BranchRegion::analyze(&graph)
            .expect("branch analysis")
            .expect("shared continuation branch");

        assert_eq!(branch.source, source);
        assert_eq!(branch.join, continuation);
        assert_eq!(branch.true_arm.nodes, BTreeSet::from([when_true]));
        assert_eq!(branch.false_arm.nodes, BTreeSet::from([when_false]));
    }

    #[test]
    fn branch_region_keeps_shared_terminal_tail_outside_arms() {
        let source = BlockId::new(0);
        let when_true = BlockId::new(1);
        let when_false = BlockId::new(2);
        let join = BlockId::new(3);
        let terminal = BlockId::new(4);
        let region = RegionId::new(0);
        let graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Branch {
                            condition: SemanticPredicate::True,
                            when_true,
                            when_false,
                        },
                    },
                ),
                (
                    when_true,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(join),
                    },
                ),
                (
                    when_false,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(join),
                    },
                ),
                (
                    join,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(terminal),
                    },
                ),
                (
                    terminal,
                    FlowNode {
                        body: SemanticNode::Leave(crate::ir::SemanticLeave {
                            site: None,
                            condition: None,
                            kind: SemanticLeaveKind::Return(None),
                            edge: None,
                            origin: None,
                            source: region,
                            destination: region,
                            target: region,
                            cleanup: Vec::new(),
                        }),
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 5,
            continues: BTreeMap::new(),
            exits: BTreeSet::new(),
        };

        let branch = BranchRegion::analyze(&graph)
            .expect("branch analysis")
            .expect("shared terminal tail branch");

        assert_eq!(branch.join, join);
        assert_eq!(branch.true_arm.nodes, BTreeSet::from([when_true]));
        assert_eq!(branch.false_arm.nodes, BTreeSet::from([when_false]));
    }

    #[test]
    fn fragment_normalization_preserves_shared_terminal_tail() {
        let source = BlockId::new(0);
        let arm = BlockId::new(1);
        let join = BlockId::new(2);
        let terminal = BlockId::new(3);
        let region = RegionId::new(0);
        let condition = SemanticPredicate::Test(
            crate::ir::SemanticOperation::from_instruction(crate::ir::InsnNode::new(
                crate::ir::InsnType::If,
                0,
            ))
            .expect("semantic predicate"),
        );
        let jump = |target| {
            SemanticNode::Leave(crate::ir::SemanticLeave {
                site: None,
                condition: None,
                kind: SemanticLeaveKind::Jump(target),
                edge: None,
                origin: None,
                source: region,
                destination: region,
                target: region,
                cleanup: Vec::new(),
            })
        };
        let mut graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::If {
                            condition: crate::ir::SemanticOperand::new(condition),
                            then_node: Box::new(jump(arm)),
                            else_node: Some(Box::new(jump(join))),
                        },
                        transfer: FlowTransfer::Fragment {
                            normal: None,
                            open: BTreeSet::from([arm, join]),
                        },
                    },
                ),
                (
                    arm,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(join),
                    },
                ),
                (
                    join,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(terminal),
                    },
                ),
                (
                    terminal,
                    FlowNode {
                        body: SemanticNode::Leave(crate::ir::SemanticLeave {
                            site: None,
                            condition: None,
                            kind: SemanticLeaveKind::Return(None),
                            edge: None,
                            origin: None,
                            source: region,
                            destination: region,
                            target: region,
                            cleanup: Vec::new(),
                        }),
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 4,
            continues: BTreeMap::new(),
            exits: BTreeSet::new(),
        };

        FragmentNormalizer::apply(&mut graph).expect("fragment normalization");

        assert!(graph.nodes.contains_key(&join));
        assert!(matches!(
            graph.nodes.get(&source).map(|node| &node.transfer),
            Some(FlowTransfer::Jump(target)) if *target == join
        ));
    }

    #[test]
    fn terminal_continuation_duplicates_shared_pure_control() {
        let source = BlockId::new(0);
        let other = BlockId::new(1);
        let terminal = BlockId::new(2);
        let region = RegionId::new(0);
        let jump = |target| {
            SemanticNode::Leave(crate::ir::SemanticLeave {
                site: None,
                condition: None,
                kind: SemanticLeaveKind::Jump(target),
                edge: None,
                origin: None,
                source: region,
                destination: region,
                target: region,
                cleanup: Vec::new(),
            })
        };
        let mut graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: jump(terminal),
                        transfer: FlowTransfer::Fragment {
                            normal: None,
                            open: BTreeSet::from([terminal]),
                        },
                    },
                ),
                (
                    other,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(terminal),
                    },
                ),
                (
                    terminal,
                    FlowNode {
                        body: SemanticNode::Leave(crate::ir::SemanticLeave {
                            site: None,
                            condition: None,
                            kind: SemanticLeaveKind::Continue,
                            edge: None,
                            origin: None,
                            source: region,
                            destination: region,
                            target: region,
                            cleanup: Vec::new(),
                        }),
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 3,
            continues: BTreeMap::new(),
            exits: BTreeSet::new(),
        };

        let continuation = TerminalContinuation::analyze(&graph)
            .expect("terminal continuation analysis")
            .expect("shared pure control continuation");
        continuation
            .apply(&mut graph)
            .expect("terminal continuation application");

        assert!(matches!(
            graph.nodes.get(&source).map(|node| &node.body),
            Some(SemanticNode::Leave(crate::ir::SemanticLeave {
                kind: SemanticLeaveKind::Continue,
                ..
            }))
        ));
        assert!(matches!(
            graph.nodes.get(&source).map(|node| &node.transfer),
            Some(FlowTransfer::Fragment { open, .. }) if open.is_empty()
        ));
        assert!(graph.nodes.contains_key(&terminal));
    }

    #[test]
    fn terminal_continuation_does_not_escape_loop_domain() {
        let outside = BlockId::new(0);
        let other = BlockId::new(1);
        let terminal = BlockId::new(2);
        let loop_member = BlockId::new(3);
        let header = BlockId::new(9);
        let region = RegionId::new(0);
        let label = SemanticLabel::loop_(region, header);
        let jump = |target| {
            SemanticNode::Leave(crate::ir::SemanticLeave {
                site: None,
                condition: None,
                kind: SemanticLeaveKind::Jump(target),
                edge: None,
                origin: None,
                source: region,
                destination: region,
                target: region,
                cleanup: Vec::new(),
            })
        };
        let graph = SemanticFlowGraph {
            region,
            entry: outside,
            nodes: BTreeMap::from([
                (
                    outside,
                    FlowNode {
                        body: jump(terminal),
                        transfer: FlowTransfer::Fragment {
                            normal: None,
                            open: BTreeSet::from([terminal]),
                        },
                    },
                ),
                (
                    other,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(terminal),
                    },
                ),
                (
                    terminal,
                    FlowNode {
                        body: SemanticNode::Leave(crate::ir::SemanticLeave {
                            site: None,
                            condition: None,
                            kind: SemanticLeaveKind::ContinueLabel(label),
                            edge: None,
                            origin: Some(loop_member),
                            source: region,
                            destination: region,
                            target: region,
                            cleanup: Vec::new(),
                        }),
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 10,
            continues: BTreeMap::from([(
                header,
                LoopContinuation::scoped(label, BTreeSet::from([loop_member, terminal, header])),
            )]),
            exits: BTreeSet::new(),
        };

        assert!(TerminalContinuation::analyze(&graph)
            .expect("terminal continuation analysis")
            .is_none());
    }

    #[test]
    fn branch_region_accepts_an_abrupt_continue_arm() {
        let source = BlockId::new(0);
        let test = BlockId::new(1);
        let abrupt = BlockId::new(2);
        let join = BlockId::new(5);
        let continuation = BlockId::new(9);
        let region = RegionId::new(0);
        let graph = SemanticFlowGraph {
            region,
            entry: source,
            nodes: BTreeMap::from([
                (
                    source,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(test),
                    },
                ),
                (
                    test,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Branch {
                            condition: SemanticPredicate::True,
                            when_true: join,
                            when_false: abrupt,
                        },
                    },
                ),
                (
                    abrupt,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(continuation),
                    },
                ),
                (
                    join,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Stop,
                    },
                ),
            ]),
            next_id: 10,
            continues: BTreeMap::from([(
                continuation,
                LoopContinuation::unscoped(SemanticLabel::loop_(region, continuation)),
            )]),
            exits: BTreeSet::new(),
        };

        let branch = BranchRegion::analyze(&graph)
            .expect("branch analysis")
            .expect("branch with abrupt continuation");

        assert_eq!(branch.source, test);
        assert_eq!(branch.join, join);
        assert!(branch.true_arm.nodes.is_empty());
        assert_eq!(branch.false_arm.nodes, BTreeSet::from([abrupt]));
    }

    #[test]
    fn embedded_leave_preserves_loop_continuation_at_arm_exit() {
        let continuation = BlockId::new(9);
        let region = RegionId::new(0);
        let label = SemanticLabel::loop_(region, continuation);
        let graph = SemanticFlowGraph {
            region,
            entry: BlockId::new(0),
            nodes: BTreeMap::new(),
            next_id: 10,
            continues: BTreeMap::from([(continuation, LoopContinuation::unscoped(label))]),
            exits: BTreeSet::from([continuation]),
        };

        let action = AcyclicLabelLowering::new(&graph)
            .expect("label allocation")
            .embedded_action(continuation);

        assert!(matches!(
            action,
            SemanticNode::Leave(crate::ir::SemanticLeave {
                kind: SemanticLeaveKind::ContinueLabel(target),
                ..
            }) if target == label
        ));
    }

    #[test]
    fn embedded_continuation_is_bound_before_acyclic_structuring() {
        let entry = BlockId::new(0);
        let continuation = BlockId::new(9);
        let region = RegionId::new(0);
        let label = SemanticLabel::loop_(region, continuation);
        let mut graph = SemanticFlowGraph {
            region,
            entry,
            nodes: BTreeMap::from([(
                entry,
                FlowNode {
                    body: SemanticNode::Leave(crate::ir::SemanticLeave {
                        site: None,
                        condition: None,
                        kind: SemanticLeaveKind::Jump(continuation),
                        edge: None,
                        origin: None,
                        source: region,
                        destination: region,
                        target: region,
                        cleanup: Vec::new(),
                    }),
                    transfer: FlowTransfer::Stop,
                },
            )]),
            next_id: 10,
            continues: BTreeMap::from([(continuation, LoopContinuation::unscoped(label))]),
            exits: BTreeSet::new(),
        };

        graph
            .bind_embedded_continuations()
            .expect("continuation binding");

        assert!(matches!(
            &graph.nodes[&entry].body,
            SemanticNode::Leave(crate::ir::SemanticLeave {
                kind: SemanticLeaveKind::ContinueLabel(target),
                ..
            }) if *target == label
        ));
        assert!(graph.targets(entry).is_empty());
    }

    #[test]
    fn embedded_continuation_respects_lexical_graph_domain() {
        let outside = BlockId::new(0);
        let member = BlockId::new(4);
        let continuation = BlockId::new(9);
        let region = RegionId::new(0);
        let label = SemanticLabel::loop_(region, continuation);
        let mut graph = SemanticFlowGraph {
            region,
            entry: outside,
            nodes: BTreeMap::from([(
                outside,
                FlowNode {
                    body: SemanticNode::Leave(crate::ir::SemanticLeave {
                        site: None,
                        condition: None,
                        kind: SemanticLeaveKind::Jump(continuation),
                        edge: Some(crate::ir::RegionEdge {
                            source: member,
                            target: continuation,
                            kind: EdgeKind::Normal,
                        }),
                        origin: Some(member),
                        source: region,
                        destination: region,
                        target: region,
                        cleanup: Vec::new(),
                    }),
                    transfer: FlowTransfer::Stop,
                },
            )]),
            next_id: 10,
            continues: BTreeMap::from([(
                continuation,
                LoopContinuation::scoped(label, BTreeSet::from([member, continuation])),
            )]),
            exits: BTreeSet::new(),
        };

        graph
            .bind_embedded_continuations()
            .expect("continuation binding");

        assert!(matches!(
            &graph.nodes[&outside].body,
            SemanticNode::Leave(crate::ir::SemanticLeave {
                kind: SemanticLeaveKind::Jump(target),
                ..
            }) if *target == continuation
        ));
    }

    #[test]
    fn embedded_block_label_to_loop_header_is_rebound_as_continue() {
        let entry = BlockId::new(0);
        let continuation = BlockId::new(9);
        let region = RegionId::new(0);
        let label = SemanticLabel::loop_(region, continuation);
        let mut graph = SemanticFlowGraph {
            region,
            entry,
            nodes: BTreeMap::from([(
                entry,
                FlowNode {
                    body: SemanticNode::Leave(crate::ir::SemanticLeave {
                        site: None,
                        condition: None,
                        kind: SemanticLeaveKind::BreakLabel(SemanticLabel::block(
                            region,
                            continuation,
                        )),
                        edge: None,
                        origin: None,
                        source: region,
                        destination: region,
                        target: region,
                        cleanup: Vec::new(),
                    }),
                    transfer: FlowTransfer::Stop,
                },
            )]),
            next_id: 10,
            continues: BTreeMap::from([(continuation, LoopContinuation::unscoped(label))]),
            exits: BTreeSet::new(),
        };

        graph
            .bind_embedded_continuations()
            .expect("continuation binding");

        assert!(matches!(
            &graph.nodes[&entry].body,
            SemanticNode::Leave(crate::ir::SemanticLeave {
                kind: SemanticLeaveKind::ContinueLabel(target),
                ..
            }) if *target == label
        ));
    }

    #[test]
    fn irreducible_entry_analysis_avoids_copying_the_heavy_loop_body() {
        let region = RegionId::new(0);
        let first = BlockId::new(1);
        let second = BlockId::new(2);
        let heavy = BlockId::new(3);
        let mut heavy_body = SemanticNode::Empty;
        for block in 20..40 {
            heavy_body = SemanticNode::Label {
                label: SemanticLabel::block(region, BlockId::new(block)),
                body: Box::new(heavy_body),
            };
        }
        let graph = SemanticFlowGraph {
            region,
            entry: first,
            nodes: BTreeMap::from([
                (
                    first,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(second),
                    },
                ),
                (
                    second,
                    FlowNode {
                        body: SemanticNode::Empty,
                        transfer: FlowTransfer::Jump(heavy),
                    },
                ),
                (
                    heavy,
                    FlowNode {
                        body: heavy_body,
                        transfer: FlowTransfer::Jump(first),
                    },
                ),
            ]),
            next_id: 40,
            continues: BTreeMap::new(),
            exits: BTreeSet::new(),
        };
        let component = BTreeSet::from([first, second, heavy]);
        let plan = IrreducibleEntryAnalysis::new(&graph, &component, &component)
            .analyze()
            .expect("entry split analysis");

        assert_eq!(plan.primary, heavy);
        assert_eq!(
            plan.copies,
            vec![
                (first, BTreeSet::from([first, second])),
                (second, BTreeSet::from([second])),
            ]
        );
    }
}
