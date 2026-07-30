use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::analysis::{SemanticFlowGraph, SemanticFlowPoint};
use crate::ir::{
    BlockId, InsnArg, InsnNode, InsnType, InstructionTree, InstructionVisitor, RegisterArg, CFG,
};
use crate::ir::{
    SemanticExpression, SemanticExpressionFacts, SemanticNode, SemanticPredicate, SemanticSiteId,
    SemanticStatement, SemanticStatementKind,
};

use super::{edge_arguments::ContractedEdgeArguments, SourceVariableError, SsaClasses, SsaVar};

#[derive(Default)]
struct BlockLiveness {
    definitions: BTreeSet<SsaVar>,
    upward_uses: BTreeSet<SsaVar>,
    phi_definitions: BTreeSet<SsaVar>,
}

pub(super) struct SsaLiveness {
    retained: BTreeSet<SsaVar>,
    live_in: BTreeMap<BlockId, BTreeSet<SsaVar>>,
    live_out: BTreeMap<BlockId, BTreeSet<SsaVar>>,
    edge_live: BTreeMap<(BlockId, BlockId, crate::ir::EdgeKind), BTreeSet<SsaVar>>,
}

impl SsaLiveness {
    pub(super) fn analyze(
        cfg: &CFG,
        retained: &BTreeSet<SsaVar>,
    ) -> Result<Self, SourceVariableError> {
        let mut blocks = BTreeMap::new();
        let mut phi_uses =
            BTreeMap::<(BlockId, BlockId, crate::ir::EdgeKind), BTreeSet<SsaVar>>::new();
        for (&block, body) in &cfg.blocks {
            let mut facts = BlockLiveness::default();
            for instruction in &body.insns {
                if instruction.insn_type == InsnType::Phi {
                    if let Some(result) = instruction.result.as_ref().and_then(SsaVar::from_reg) {
                        if retained.contains(&result) {
                            facts.definitions.insert(result);
                            facts.phi_definitions.insert(result);
                        }
                    }
                    for (&(predecessor, edge_kind), argument) in
                        instruction.payload.phi_edges.iter().zip(&instruction.args)
                    {
                        if let Some(value) = argument.as_register().and_then(SsaVar::from_reg) {
                            if retained.contains(&value) {
                                phi_uses
                                    .entry((predecessor, block, edge_kind))
                                    .or_default()
                                    .insert(value);
                            }
                        }
                    }
                    continue;
                }
                for usage in InstructionUses::collect(instruction)
                    .into_iter()
                    .filter(|usage| retained.contains(usage))
                {
                    if !facts.definitions.contains(&usage) {
                        facts.upward_uses.insert(usage);
                    }
                }
                if let Some(result) = instruction.result.as_ref().and_then(SsaVar::from_reg) {
                    if retained.contains(&result) {
                        facts.definitions.insert(result);
                    }
                }
            }
            blocks.insert(block, facts);
        }

        let mut live_in = cfg
            .block_ids()
            .into_iter()
            .map(|block| (block, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let mut live_out = live_in.clone();
        let mut changed = true;
        while changed {
            changed = false;
            for block in cfg.block_ids().into_iter().rev() {
                let mut out = BTreeSet::new();
                for &(successor, edge_kind) in cfg.successors_with_kind(block) {
                    out.extend(Self::edge_values(
                        block, successor, edge_kind, &live_in, &blocks, &phi_uses,
                    )?);
                }
                let facts = blocks
                    .get(&block)
                    .ok_or(SourceVariableError::MissingBlock(block))?;
                let mut input = facts.upward_uses.clone();
                input.extend(out.difference(&facts.definitions).copied());
                if live_out.get(&block) != Some(&out) {
                    live_out.insert(block, out);
                    changed = true;
                }
                if live_in.get(&block) != Some(&input) {
                    live_in.insert(block, input);
                    changed = true;
                }
            }
        }
        let mut edge_live = BTreeMap::new();
        for source in cfg.block_ids() {
            for &(target, kind) in cfg.successors_with_kind(source) {
                edge_live.insert(
                    (source, target, kind),
                    Self::edge_values(source, target, kind, &live_in, &blocks, &phi_uses)?,
                );
            }
        }
        Ok(Self {
            retained: retained.clone(),
            live_in,
            live_out,
            edge_live,
        })
    }

    fn edge_values(
        source: BlockId,
        target: BlockId,
        kind: crate::ir::EdgeKind,
        live_in: &BTreeMap<BlockId, BTreeSet<SsaVar>>,
        blocks: &BTreeMap<BlockId, BlockLiveness>,
        phi_uses: &BTreeMap<(BlockId, BlockId, crate::ir::EdgeKind), BTreeSet<SsaVar>>,
    ) -> Result<BTreeSet<SsaVar>, SourceVariableError> {
        let successor_live = live_in
            .get(&target)
            .ok_or(SourceVariableError::MissingBlock(target))?;
        let successor_facts = blocks
            .get(&target)
            .ok_or(SourceVariableError::MissingBlock(target))?;
        let mut values = successor_live
            .difference(&successor_facts.phi_definitions)
            .copied()
            .collect::<BTreeSet<_>>();
        values.extend(
            phi_uses
                .get(&(source, target, kind))
                .into_iter()
                .flatten()
                .copied(),
        );
        Ok(values)
    }

    pub(super) fn edge_live(
        &self,
        source: BlockId,
        target: BlockId,
        kind: crate::ir::EdgeKind,
    ) -> Result<&BTreeSet<SsaVar>, SourceVariableError> {
        self.edge_live
            .get(&(source, target, kind))
            .ok_or(SourceVariableError::MissingBlock(target))
    }

    pub(super) fn normal_continuation_live(
        &self,
        cfg: &CFG,
        predecessor: BlockId,
    ) -> Result<BTreeSet<SsaVar>, SourceVariableError> {
        let mut live = BTreeSet::new();
        for &(successor, kind) in cfg.successors_with_kind(predecessor) {
            if kind == crate::ir::EdgeKind::Exception {
                continue;
            }
            live.extend(
                self.edge_live(predecessor, successor, kind)?
                    .iter()
                    .copied(),
            );
        }
        if let Some(result) = cfg.block(predecessor).and_then(|body| {
            body.insns.last().and_then(|instruction| {
                instruction
                    .can_throw()
                    .then(|| instruction.result.as_ref().and_then(SsaVar::from_reg))
                    .flatten()
            })
        }) {
            live.remove(&result);
        }
        Ok(live)
    }
}

#[derive(Default)]
pub(super) struct InterferenceGraph {
    hard_edges: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
    semantic_edges: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
}

impl InterferenceGraph {
    pub(super) fn build(
        cfg: &CFG,
        semantic: &SemanticNode,
        liveness: &SsaLiveness,
    ) -> Result<Self, SourceVariableError> {
        let mut graph = Self::default();
        if let Some(inputs) = liveness.live_in.get(&cfg.entry) {
            graph.add_clique(inputs);
        }
        for (&block, body) in &cfg.blocks {
            let mut live = liveness
                .live_out
                .get(&block)
                .cloned()
                .ok_or(SourceVariableError::MissingBlock(block))?;
            for instruction in body.insns.iter().rev() {
                let definition = instruction
                    .result
                    .as_ref()
                    .and_then(SsaVar::from_reg)
                    .filter(|value| liveness.retained.contains(value));
                let uses = if instruction.insn_type == InsnType::Phi {
                    BTreeSet::new()
                } else {
                    InstructionUses::collect(instruction)
                        .into_iter()
                        .filter(|value| liveness.retained.contains(value))
                        .collect()
                };
                graph.add_clique(&uses);
                if let Some(definition) = definition {
                    let move_source = (instruction.insn_type == InsnType::Move)
                        .then(|| instruction.args.first())
                        .flatten()
                        .and_then(InsnArg::as_register)
                        .and_then(SsaVar::from_reg);
                    for other in live
                        .iter()
                        .copied()
                        .filter(|value| *value != definition && Some(*value) != move_source)
                    {
                        graph.add(definition, other);
                    }
                    live.remove(&definition);
                }
                live.extend(uses);
            }
            if liveness.live_in.get(&block) != Some(&live) {
                return Err(SourceVariableError::LivenessMismatch(block));
            }
        }
        SemanticLiveness::analyze(semantic, &liveness.retained)?.add_interference(&mut graph);
        Ok(graph)
    }

    pub(super) fn add_exceptional_edge_interference(
        &mut self,
        cfg: &CFG,
        liveness: &SsaLiveness,
        arguments: &ContractedEdgeArguments<'_>,
    ) -> Result<(), SourceVariableError> {
        for (&successor, block) in &cfg.blocks {
            for phi in block
                .insns
                .iter()
                .filter(|instruction| instruction.insn_type == InsnType::Phi)
            {
                let Some(destination) = phi
                    .result
                    .as_ref()
                    .and_then(SsaVar::from_reg)
                    .filter(|value| liveness.retained.contains(value))
                else {
                    continue;
                };
                for argument in arguments.resolve_all(successor, phi)? {
                    if argument.edge_kind != crate::ir::EdgeKind::Exception {
                        continue;
                    }
                    let source = argument
                        .value
                        .explicit()
                        .and_then(InsnArg::as_register)
                        .and_then(SsaVar::from_reg);
                    for live in liveness.normal_continuation_live(cfg, argument.predecessor)? {
                        if live != destination && Some(live) != source {
                            self.add(destination, live);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn add(&mut self, left: SsaVar, right: SsaVar) {
        self.hard_edges.entry(left).or_default().insert(right);
        self.hard_edges.entry(right).or_default().insert(left);
    }

    fn add_semantic(&mut self, left: SsaVar, right: SsaVar) {
        self.semantic_edges.entry(left).or_default().insert(right);
        self.semantic_edges.entry(right).or_default().insert(left);
    }

    fn add_clique(&mut self, values: &BTreeSet<SsaVar>) {
        for (index, left) in values.iter().copied().enumerate() {
            for right in values.iter().copied().skip(index + 1) {
                self.add(left, right);
            }
        }
    }

    fn add_semantic_clique(&mut self, values: &BTreeSet<SsaVar>) {
        for (index, left) in values.iter().copied().enumerate() {
            for right in values.iter().copied().skip(index + 1) {
                self.add_semantic(left, right);
            }
        }
    }
}

#[derive(Default)]
struct SemanticSiteFacts {
    uses: BTreeSet<SsaVar>,
    definitions: BTreeSet<SsaVar>,
}

struct SemanticLiveness {
    sites: BTreeMap<SemanticSiteId, SemanticSiteFacts>,
    live_after: BTreeMap<SemanticSiteId, BTreeSet<SsaVar>>,
}

impl SemanticLiveness {
    fn analyze(
        root: &SemanticNode,
        retained: &BTreeSet<SsaVar>,
    ) -> Result<Self, SourceVariableError> {
        let sites = SemanticSiteCollector::new(retained).collect(root)?;
        let flow = SemanticFlowGraph::analyze(root);
        if !flow.is_complete() {
            return Err(SourceVariableError::IncompleteSemanticFlow);
        }
        let points = flow.points();
        let mut live = points
            .iter()
            .copied()
            .map(|point| (point, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let mut pending = points.iter().rev().copied().collect::<VecDeque<_>>();
        let mut queued = points;
        while let Some(point) = pending.pop_front() {
            queued.remove(&point);
            let mut input = flow
                .successors(point)
                .iter()
                .filter_map(|successor| live.get(successor))
                .flatten()
                .copied()
                .collect::<BTreeSet<_>>();
            if let SemanticFlowPoint::Before(site) = point {
                let facts = sites
                    .get(&site)
                    .ok_or(SourceVariableError::MissingSemanticSite("flow point"))?;
                input.retain(|value| !facts.definitions.contains(value));
                input.extend(facts.uses.iter().copied());
            }
            if live.get(&point) == Some(&input) {
                continue;
            }
            live.insert(point, input);
            for predecessor in flow.predecessors(point) {
                if queued.insert(predecessor) {
                    pending.push_back(predecessor);
                }
            }
        }
        let live_after = sites
            .keys()
            .copied()
            .map(|site| {
                let values = live
                    .get(&SemanticFlowPoint::After(site))
                    .cloned()
                    .unwrap_or_default();
                (site, values)
            })
            .collect();
        Ok(Self { sites, live_after })
    }

    fn add_interference(self, graph: &mut InterferenceGraph) {
        for (site, facts) in self.sites {
            graph.add_semantic_clique(&facts.uses);
            let live = self.live_after.get(&site).cloned().unwrap_or_default();
            for definition in &facts.definitions {
                for other in live.iter().copied().filter(|other| other != definition) {
                    graph.add_semantic(*definition, other);
                }
            }
        }
    }
}

struct SemanticSiteCollector<'a> {
    retained: &'a BTreeSet<SsaVar>,
    sites: BTreeMap<SemanticSiteId, SemanticSiteFacts>,
}

impl<'a> SemanticSiteCollector<'a> {
    fn new(retained: &'a BTreeSet<SsaVar>) -> Self {
        Self {
            retained,
            sites: BTreeMap::new(),
        }
    }

    fn collect(
        mut self,
        root: &SemanticNode,
    ) -> Result<BTreeMap<SemanticSiteId, SemanticSiteFacts>, SourceVariableError> {
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Empty => {}
                SemanticNode::BasicBlock(block) => {
                    for statement in &block.statements {
                        self.record_statement(statement)?;
                    }
                }
                SemanticNode::Sequence(children) => pending.extend(children),
                SemanticNode::If {
                    condition,
                    then_node,
                    else_node,
                } => {
                    self.record_predicate(condition.site, condition)?;
                    pending.push(then_node);
                    pending.extend(else_node.as_deref());
                }
                SemanticNode::Loop { test, body, .. } => {
                    self.record_predicate(test.condition.site, &test.condition)?;
                    pending.push(&test.setup);
                    pending.push(body);
                }
                SemanticNode::For {
                    init,
                    condition,
                    update,
                    body,
                    ..
                } => {
                    self.record_statement(init)?;
                    self.record_predicate(condition.site, condition)?;
                    self.record_statement(update)?;
                    pending.push(body);
                }
                SemanticNode::ForEach {
                    variable,
                    iterable,
                    body,
                    ..
                } => {
                    self.record_expression(iterable.site, iterable)?;
                    if let (Some(site), Some(variable)) =
                        (iterable.site, SsaVar::from_reg(variable))
                    {
                        self.site(site).definitions.insert(variable);
                    }
                    pending.push(body);
                }
                SemanticNode::Switch {
                    selector, cases, ..
                } => {
                    self.record_expression(selector.site, selector)?;
                    pending.extend(cases.iter().map(|case| &case.body));
                }
                SemanticNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    pending.push(body);
                    pending.extend(catches.iter().map(|catch| &catch.body));
                    if let Some(finally) = finally {
                        pending.push(&finally.body);
                    }
                }
                SemanticNode::Synchronized { lock, body, .. } => {
                    self.record_expression(lock.site, lock)?;
                    pending.push(body);
                }
                SemanticNode::Label { body, .. } => pending.push(body),
                SemanticNode::Leave(leave) => {
                    let site = leave
                        .site
                        .ok_or(SourceVariableError::MissingSemanticSite("leave"))?;
                    self.site(site);
                    if let Some(condition) = &leave.condition {
                        self.add_uses(site, Self::predicate_uses(condition));
                    }
                    if let Some(value) = leave.value() {
                        self.add_uses(site, Self::expression_uses(value));
                    }
                }
            }
        }
        Ok(self.sites)
    }

    fn record_statement(
        &mut self,
        statement: &SemanticStatement,
    ) -> Result<(), SourceVariableError> {
        let site = statement
            .site
            .ok_or(SourceVariableError::MissingSemanticSite("statement"))?;
        self.site(site);
        match &statement.kind {
            SemanticStatementKind::Instruction(operation) => {
                self.add_uses(
                    site,
                    SemanticExpressionFacts::of_operation(operation).used_ssa_variables(),
                );
                if let Some(result) = operation.result.as_ref().and_then(SsaVar::from_reg) {
                    self.site(site).definitions.insert(result);
                }
            }
            SemanticStatementKind::Definition { result, value, .. } => {
                self.add_uses(site, Self::expression_uses(value));
                if let Some(result) = SsaVar::from_reg(result) {
                    self.site(site).definitions.insert(result);
                }
            }
        }
        Ok(())
    }

    fn record_predicate(
        &mut self,
        site: Option<SemanticSiteId>,
        predicate: &SemanticPredicate,
    ) -> Result<(), SourceVariableError> {
        let site = site.ok_or(SourceVariableError::MissingSemanticSite("predicate"))?;
        self.site(site);
        self.add_uses(site, Self::predicate_uses(predicate));
        Ok(())
    }

    fn record_expression(
        &mut self,
        site: Option<SemanticSiteId>,
        expression: &SemanticExpression,
    ) -> Result<(), SourceVariableError> {
        let site = site.ok_or(SourceVariableError::MissingSemanticSite("expression"))?;
        self.site(site);
        self.add_uses(site, Self::expression_uses(expression));
        Ok(())
    }

    fn predicate_uses(predicate: &SemanticPredicate) -> BTreeSet<SsaVar> {
        SemanticExpressionFacts::of_predicate(predicate)
            .used_ssa_variables()
            .collect()
    }

    fn expression_uses(expression: &SemanticExpression) -> BTreeSet<SsaVar> {
        SemanticExpressionFacts::of_expression(expression)
            .used_ssa_variables()
            .collect()
    }

    fn add_uses(&mut self, site: SemanticSiteId, uses: impl IntoIterator<Item = SsaVar>) {
        let retained = self.retained;
        self.site(site)
            .uses
            .extend(uses.into_iter().filter(|value| retained.contains(value)));
    }

    fn site(&mut self, site: SemanticSiteId) -> &mut SemanticSiteFacts {
        self.sites.entry(site).or_default()
    }
}

pub(super) struct ClassInterference {
    hard_edges: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
    semantic_edges: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
}

impl ClassInterference {
    pub(super) fn new(interference: InterferenceGraph, classes: &mut SsaClasses) -> Self {
        Self {
            hard_edges: Self::classes(interference.hard_edges, classes),
            semantic_edges: Self::classes(interference.semantic_edges, classes),
        }
    }

    fn classes(
        edges: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
        classes: &mut SsaClasses,
    ) -> BTreeMap<SsaVar, BTreeSet<SsaVar>> {
        let mut graph = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        for (left, neighbors) in edges {
            let left = classes.root(left);
            for right in neighbors {
                let right = classes.root(right);
                if left != right {
                    graph.entry(left).or_default().insert(right);
                    graph.entry(right).or_default().insert(left);
                }
            }
        }
        graph
    }

    pub(super) fn interferes(&self, left: SsaVar, right: SsaVar) -> bool {
        self.hard_interferes(left, right)
            || self
                .semantic_edges
                .get(&left)
                .is_some_and(|neighbors| neighbors.contains(&right))
    }

    pub(super) fn hard_interferes(&self, left: SsaVar, right: SsaVar) -> bool {
        self.hard_edges
            .get(&left)
            .is_some_and(|neighbors| neighbors.contains(&right))
    }

    pub(super) fn merge(&mut self, root: SsaVar, absorbed: SsaVar) {
        Self::merge_edges(&mut self.hard_edges, root, absorbed);
        Self::merge_edges(&mut self.semantic_edges, root, absorbed);
    }

    fn merge_edges(edges: &mut BTreeMap<SsaVar, BTreeSet<SsaVar>>, root: SsaVar, absorbed: SsaVar) {
        let mut neighbors = edges.remove(&root).unwrap_or_default();
        neighbors.extend(edges.remove(&absorbed).unwrap_or_default());
        neighbors.remove(&root);
        neighbors.remove(&absorbed);
        for neighbor in &neighbors {
            let adjacent = edges.entry(*neighbor).or_default();
            adjacent.remove(&root);
            adjacent.remove(&absorbed);
            adjacent.insert(root);
        }
        edges.insert(root, neighbors);
    }
}

#[derive(Default)]
pub(super) struct InstructionUses {
    values: BTreeSet<SsaVar>,
}

impl InstructionUses {
    pub(super) fn collect(instruction: &InsnNode) -> BTreeSet<SsaVar> {
        let mut uses = Self::default();
        if instruction.insn_type == InsnType::Constructor {
            for argument in instruction.args.get(1..).unwrap_or_default() {
                InstructionTree::visit_arg(argument, &mut uses);
            }
            if let Some(target) = &instruction.payload.compound_target {
                InstructionTree::visit_arg(target, &mut uses);
            }
        } else {
            InstructionTree::visit_args(instruction, &mut uses);
        }
        uses.values
    }
}

impl InstructionVisitor for InstructionUses {
    fn visit_register(&mut self, register: &RegisterArg) {
        self.values.extend(SsaVar::from_reg(register));
    }
}

#[cfg(test)]
mod tests {
    use super::{InterferenceGraph, SsaLiveness};
    use crate::ir::{analysis::SsaVar, ArgType, Block, IfOp, InsnArg, InsnNode, CFG};
    use std::collections::BTreeSet;

    #[test]
    fn simultaneous_operands_interfere_without_local_definitions() {
        let left = SsaVar::new(0, 0);
        let right = SsaVar::new(1, 0);
        let mut block = Block::new(0u32);
        block.push(InsnNode::if_cmp(
            IfOp::Ne,
            InsnArg::reg_ssa(0, 0, ArgType::INT),
            InsnArg::reg_ssa(1, 0, ArgType::INT),
            0,
        ));
        let mut cfg = CFG::new("simultaneous-inputs");
        cfg.add_block(block);

        let retained = BTreeSet::from([left, right]);
        let liveness = SsaLiveness::analyze(&cfg, &retained).unwrap();
        let interference =
            InterferenceGraph::build(&cfg, &crate::ir::SemanticNode::Empty, &liveness).unwrap();

        assert!(interference
            .hard_edges
            .get(&left)
            .is_some_and(|neighbors| neighbors.contains(&right)));
    }
}
