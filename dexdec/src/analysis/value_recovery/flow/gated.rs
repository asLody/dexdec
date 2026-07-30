//! Gated-SSA recovery for values selected by acyclic control flow.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::{
        DominanceError, DominatorTree, InstructionEffects, PhiInput, ReachingConditions,
        SsaValueGraph, SsaVar,
    },
    BlockId, BoolExpr, BoolVariable, EdgeKind, GatedPhiDiagnostic, GatedPhiRejection, InsnArg,
    InsnNode, InsnType, SemanticExpression, SemanticExpressionFacts, SemanticFolder, SemanticNode,
    SemanticOperation, SemanticPredicate, SemanticStatement, StatementOrigin, Utf16String,
    ValueRecoveryDiagnostics, CFG,
};

use super::{UseSite, ValueFlowGraph};
use crate::analysis::value_recovery::{
    domain::{ControlDomain, DomainLogic},
    ValueRecoveryError,
};

#[derive(Debug)]
pub(in crate::analysis::value_recovery) struct GatedControlFlow {
    regions: BTreeMap<BlockId, SelectionRegion>,
    tests: BTreeMap<BlockId, InsnNode>,
    loop_headers: BTreeSet<BlockId>,
    dominators: DominatorTree,
}

impl GatedControlFlow {
    const EXPRESSION_NODE_LIMIT: usize = 64;

    pub(in crate::analysis::value_recovery) fn analyze(cfg: &CFG) -> Result<Self, DominanceError> {
        let predecessors = cfg.normal_predecessor_snapshot();
        let dominators = DominatorTree::compute_normal(cfg, cfg.block_ids(), &predecessors)?;
        let phi_blocks = cfg
            .blocks_iter()
            .filter(|block| {
                block
                    .insns
                    .iter()
                    .any(|instruction| instruction.insn_type == InsnType::Phi)
            })
            .map(|block| block.id)
            .collect::<BTreeSet<_>>();
        let loop_headers = phi_blocks
            .iter()
            .copied()
            .filter(|join| {
                cfg.incoming_edges(*join).into_iter().any(|(source, edge)| {
                    edge != EdgeKind::Exception && dominators.dominates(*join, source)
                })
            })
            .collect::<BTreeSet<_>>();
        let regions = phi_blocks
            .into_iter()
            .filter(|join| !loop_headers.contains(join))
            .filter_map(|join| {
                SelectionRegion::analyze(cfg, &predecessors, &dominators, join)
                    .map(|region| (join, region))
            })
            .collect();
        let tests = cfg
            .blocks_iter()
            .filter_map(|block| {
                block
                    .terminator()
                    .filter(|instruction| instruction.insn_type == InsnType::If)
                    .cloned()
                    .map(|instruction| (block.id, instruction))
            })
            .collect();
        Ok(Self {
            regions,
            tests,
            loop_headers,
            dominators,
        })
    }

    fn region(&self, join: BlockId) -> Option<&SelectionRegion> {
        self.regions.get(&join)
    }

    fn test(&self, block: BlockId) -> Option<&InsnNode> {
        self.tests.get(&block)
    }

    fn is_loop_header(&self, block: BlockId) -> bool {
        self.loop_headers.contains(&block)
    }
}

#[derive(Debug)]
struct SelectionRegion {
    care: BoolExpr,
    gates: BTreeMap<(BlockId, EdgeKind), BoolExpr>,
}

impl SelectionRegion {
    fn analyze(
        cfg: &CFG,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
        dominators: &DominatorTree,
        join: BlockId,
    ) -> Option<Self> {
        let entry = dominators.idom(join)?;
        if entry == BlockId::INVALID {
            return None;
        }
        let nodes = Self::backward_slice(predecessors, dominators, entry, join)?;
        let facts = ReachingConditions::analyze_slice(cfg, entry, &nodes).ok()?;
        let care = facts
            .expression(
                facts.condition(join)?.domain(),
                GatedControlFlow::EXPRESSION_NODE_LIMIT,
            )
            .ok()??
            .0;
        let mut gates = BTreeMap::new();
        for (source, edge) in cfg.incoming_edges(join) {
            if edge == EdgeKind::Exception || !nodes.contains(&source) {
                continue;
            }
            let reaching = facts.condition(source)?.domain();
            let edge_condition = facts.edge_condition(cfg, source, join, edge).ok()?;
            let gate = facts.and(reaching, edge_condition).ok()?;
            let expression = facts
                .expression(gate, GatedControlFlow::EXPRESSION_NODE_LIMIT)
                .ok()??
                .0;
            gates.insert((source, edge), expression);
        }
        (!gates.is_empty()).then_some(Self { care, gates })
    }

    fn backward_slice(
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
        dominators: &DominatorTree,
        entry: BlockId,
        join: BlockId,
    ) -> Option<BTreeSet<BlockId>> {
        let mut nodes = BTreeSet::new();
        let mut pending = vec![join];
        while let Some(block) = pending.pop() {
            if !dominators.dominates(entry, block) || !nodes.insert(block) {
                continue;
            }
            if block == entry {
                continue;
            }
            pending.extend(
                predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .copied()
                    .filter(|predecessor| dominators.dominates(entry, *predecessor)),
            );
        }
        nodes.contains(&entry).then_some(nodes)
    }

    fn gate(&self, input: &PhiInput) -> Option<&BoolExpr> {
        self.gates.get(&(input.predecessor, input.edge_kind))
    }
}

#[derive(Debug, Clone)]
pub(in crate::analysis::value_recovery) struct PhiExpression {
    block: BlockId,
    result: SsaVar,
    statement: SemanticStatement,
}

pub(in crate::analysis::value_recovery) struct GatedPhiRecovery {
    pub(in crate::analysis::value_recovery) expressions: Vec<PhiExpression>,
    pub(in crate::analysis::value_recovery) specializations: Vec<PhiUseSpecialization>,
    pub(in crate::analysis::value_recovery) eliminated: BTreeSet<SsaVar>,
    pub(in crate::analysis::value_recovery) diagnostics: ValueRecoveryDiagnostics,
}

enum PhiDecision {
    Recovered(PhiExpression),
    Specialized(PhiUseSpecialization),
    Rejected(GatedPhiRejection),
}

pub(in crate::analysis::value_recovery) struct PhiUseSpecialization {
    pub(in crate::analysis::value_recovery) result: SsaVar,
    pub(in crate::analysis::value_recovery) replacements: Vec<(UseSite, InsnArg)>,
}

#[derive(Clone)]
struct SelectedGroup {
    key: SelectedValue,
    value: SemanticExpression,
    gate: ControlDomain,
}

struct SelectionCost;

impl SelectionCost {
    fn of(value: &SemanticExpression) -> usize {
        let mut cost = 0usize;
        let mut pending = vec![CostNode::Expression(value)];
        while let Some(node) = pending.pop() {
            match node {
                CostNode::Expression(SemanticExpression::Operation(operation)) => {
                    if !matches!(
                        operation.insn_type,
                        InsnType::Move | InsnType::Const | InsnType::ConstStr
                    ) {
                        cost = cost.saturating_add(1);
                    }
                    pending.extend(operation.operands().iter().map(CostNode::Expression));
                    pending.extend(operation.compound_target().map(CostNode::Expression));
                }
                CostNode::Expression(SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                }) => {
                    cost = cost.saturating_add(1);
                    pending.push(CostNode::Predicate(condition));
                    pending.push(CostNode::Expression(when_false));
                    pending.push(CostNode::Expression(when_true));
                }
                CostNode::Predicate(SemanticPredicate::Test(operation)) => {
                    cost = cost.saturating_add(1);
                    pending.extend(operation.operands().iter().map(CostNode::Expression));
                    pending.extend(operation.compound_target().map(CostNode::Expression));
                }
                CostNode::Predicate(SemanticPredicate::Not(inner)) => {
                    pending.push(CostNode::Predicate(inner));
                }
                CostNode::Predicate(SemanticPredicate::And(terms))
                | CostNode::Predicate(SemanticPredicate::Or(terms)) => {
                    pending.extend(terms.iter().map(CostNode::Predicate));
                }
                CostNode::Expression(SemanticExpression::Register(_))
                | CostNode::Expression(SemanticExpression::Literal(_))
                | CostNode::Predicate(SemanticPredicate::True)
                | CostNode::Predicate(SemanticPredicate::False) => {}
            }
        }
        cost
    }

    fn expanded(graph: &ValueFlowGraph<'_>, value: &SemanticExpression) -> usize {
        let mut cost = 0usize;
        let mut expanded = BTreeSet::<SsaVar>::new();
        let mut pending = vec![CostNode::Expression(value)];
        while let Some(node) = pending.pop() {
            match node {
                CostNode::Expression(SemanticExpression::Register(register)) => {
                    let Some(key) = graph.key(register) else {
                        continue;
                    };
                    let Some([definition]) = graph.definitions.get(&key).map(Vec::as_slice) else {
                        continue;
                    };
                    let single_use = graph.uses.get(&key).is_some_and(|uses| uses.len() == 1);
                    if single_use && !definition.repetitive && expanded.insert(key) {
                        pending.push(CostNode::Expression(definition.expression()));
                    }
                }
                CostNode::Expression(SemanticExpression::Operation(operation)) => {
                    if !matches!(
                        operation.insn_type,
                        InsnType::Move | InsnType::Const | InsnType::ConstStr
                    ) {
                        cost = cost.saturating_add(1);
                    }
                    pending.extend(operation.operands().iter().map(CostNode::Expression));
                    pending.extend(operation.compound_target().map(CostNode::Expression));
                }
                CostNode::Expression(SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                }) => {
                    cost = cost.saturating_add(1);
                    pending.push(CostNode::Predicate(condition));
                    pending.push(CostNode::Expression(when_false));
                    pending.push(CostNode::Expression(when_true));
                }
                CostNode::Predicate(SemanticPredicate::Test(operation)) => {
                    cost = cost.saturating_add(1);
                    pending.extend(operation.operands().iter().map(CostNode::Expression));
                    pending.extend(operation.compound_target().map(CostNode::Expression));
                }
                CostNode::Predicate(SemanticPredicate::Not(inner)) => {
                    pending.push(CostNode::Predicate(inner));
                }
                CostNode::Predicate(SemanticPredicate::And(terms))
                | CostNode::Predicate(SemanticPredicate::Or(terms)) => {
                    pending.extend(terms.iter().map(CostNode::Predicate));
                }
                CostNode::Expression(SemanticExpression::Literal(_))
                | CostNode::Predicate(SemanticPredicate::True)
                | CostNode::Predicate(SemanticPredicate::False) => {}
            }
        }
        cost
    }
}

enum CostNode<'a> {
    Expression(&'a SemanticExpression),
    Predicate(&'a SemanticPredicate),
}

struct SelectionMaterialization<'a> {
    graph: &'a ValueFlowGraph<'a>,
}

impl<'a> SelectionMaterialization<'a> {
    fn new(graph: &'a ValueFlowGraph<'a>) -> Self {
        Self { graph }
    }

    fn accepts_root(
        &self,
        phi: &crate::ir::analysis::PhiMerge,
        value: &SemanticExpression,
    ) -> bool {
        let cost = SelectionCost::expanded(self.graph, value);
        let budget = phi.inputs.len().saturating_add(2).max(4);
        cost <= budget
    }

    fn accepts_cut(&self, phi: &crate::ir::analysis::PhiMerge, value: &SemanticExpression) -> bool {
        if !super::effects::EffectSummary::expression(value)
            .without_control()
            .is_pure()
        {
            return false;
        }
        let cost = SelectionCost::of(value);
        let budget = phi.inputs.len().saturating_add(2).max(4);
        cost <= budget
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum SelectedValue {
    Variable(SsaVar),
    Literal(i64),
    String(Utf16String),
    Expression(u32),
}

pub(super) struct SourceSelectionInput {
    pub(super) key: SelectedValue,
    pub(super) value: SemanticExpression,
    pub(super) gate: BoolExpr,
}

pub(super) enum SourceSelection {
    Recovered(SemanticExpression),
    Rejected(SourceSelectionRejection),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SourceSelectionRejection {
    InsufficientInputs,
    TrivialValues,
    OverlappingGates,
    IncompleteCoverage,
    PredicateNotRecoverable,
}

pub(super) fn equivalent(left: &BoolExpr, right: &BoolExpr) -> Result<bool, ValueRecoveryError> {
    let mut variables = left.symbols();
    variables.extend(right.symbols());
    let mut logic = DomainLogic::new(&variables);
    let left = logic.compile(left)?;
    let right = logic.compile(right)?;
    logic.equivalent(left, right).map_err(Into::into)
}

pub(super) fn build_source_selection(
    graph: &ValueFlowGraph<'_>,
    movable_predicates: &BTreeSet<crate::ir::InstructionId>,
    care_expression: BoolExpr,
    inputs: Vec<SourceSelectionInput>,
) -> Result<SourceSelection, ValueRecoveryError> {
    if inputs.len() < 2 {
        return Ok(SourceSelection::Rejected(
            SourceSelectionRejection::InsufficientInputs,
        ));
    }
    let mut variables = care_expression.symbols();
    for input in &inputs {
        variables.extend(input.gate.symbols());
    }

    let mut logic = DomainLogic::new(&variables);
    let care = logic.compile(&care_expression)?;
    let mut groups = BTreeMap::<SelectedValue, SelectedGroup>::new();
    for input in inputs {
        let gate = logic.compile(&input.gate)?;
        match groups.get_mut(&input.key) {
            Some(group) => group.gate = logic.or(group.gate, gate)?,
            None => {
                groups.insert(
                    input.key.clone(),
                    SelectedGroup {
                        key: input.key,
                        value: input.value,
                        gate,
                    },
                );
            }
        }
    }
    if groups.len() < 2 {
        return Ok(SourceSelection::Rejected(
            SourceSelectionRejection::TrivialValues,
        ));
    }
    let groups = groups.into_values().collect::<Vec<_>>();
    let mut coverage = None;
    for (index, left) in groups.iter().enumerate() {
        coverage = Some(match coverage {
            Some(coverage) => logic.or(coverage, left.gate)?,
            None => left.gate,
        });
        for right in &groups[index + 1..] {
            if !logic.disjoint(left.gate, right.gate)? {
                return Ok(SourceSelection::Rejected(
                    SourceSelectionRejection::OverlappingGates,
                ));
            }
        }
    }
    let Some(coverage) = coverage else {
        return Ok(SourceSelection::Rejected(
            SourceSelectionRejection::InsufficientInputs,
        ));
    };
    if !logic.equivalent(coverage, care)? {
        return Ok(SourceSelection::Rejected(
            SourceSelectionRejection::IncompleteCoverage,
        ));
    }
    let mut diagnostics = ValueRecoveryDiagnostics::default();
    let predicates = SourcePredicateLookup {
        graph,
        movable: movable_predicates,
    };
    Ok(
        match SelectionTreeBuilder::new(&mut logic, &predicates, &mut diagnostics)
            .build(care, groups)?
        {
            Some(expression) => SourceSelection::Recovered(expression),
            None => SourceSelection::Rejected(SourceSelectionRejection::PredicateNotRecoverable),
        },
    )
}

pub(super) struct GatedPhiAnalysis<'a> {
    graph: &'a ValueFlowGraph<'a>,
    values: &'a SsaValueGraph,
    control: &'a GatedControlFlow,
}

impl<'a> GatedPhiAnalysis<'a> {
    pub(super) fn new(
        graph: &'a ValueFlowGraph<'a>,
        values: &'a SsaValueGraph,
        control: &'a GatedControlFlow,
    ) -> Self {
        Self {
            graph,
            values,
            control,
        }
    }

    pub(super) fn analyze(self) -> Result<GatedPhiRecovery, ValueRecoveryError> {
        let canonical = self.graph.canonical_values();
        let live = self.live_phis();
        let roots = self.graph.semantic_use_roots();
        let phis = self
            .graph
            .phis
            .iter()
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let mut expressions = Vec::new();
        let mut specializations = Vec::new();
        let mut eliminated = BTreeSet::new();
        let mut recovered_values = BTreeMap::<SsaVar, SemanticExpression>::new();
        let mut recovered_results = BTreeSet::new();
        let mut pending_materializations = BTreeMap::<SsaVar, PhiExpression>::new();
        let mut committed_materializations = BTreeSet::new();
        let mut diagnostics = ValueRecoveryDiagnostics::default();
        for phi in self.phi_order(&live) {
            diagnostics.gated_candidates += 1;
            if !live.contains(&phi.result) {
                eliminated.insert(phi.result);
                diagnostics.rejected.push(GatedPhiDiagnostic {
                    block: phi.block,
                    register: phi.result.reg_num,
                    version: phi.result.version,
                    reason: GatedPhiRejection::UnusedResult,
                });
                continue;
            }
            match self.expression(
                phi,
                &canonical,
                &recovered_values,
                !roots.contains(&phi.result),
                &mut diagnostics,
            )? {
                PhiDecision::Recovered(expression) => {
                    let value = expression.statement.value().cloned();
                    let Some(value) = value else {
                        diagnostics.rejected.push(GatedPhiDiagnostic {
                            block: phi.block,
                            register: phi.result.reg_num,
                            version: phi.result.version,
                            reason: GatedPhiRejection::CompositionCost,
                        });
                        continue;
                    };
                    if roots.contains(&expression.result) {
                        if !SelectionMaterialization::new(self.graph).accepts_root(phi, &value) {
                            diagnostics.rejected.push(GatedPhiDiagnostic {
                                block: phi.block,
                                register: phi.result.reg_num,
                                version: phi.result.version,
                                reason: GatedPhiRejection::CompositionCost,
                            });
                            continue;
                        }
                        diagnostics.gated_recovered += 1;
                        recovered_results.insert(expression.result);
                        expressions.push(expression);
                        for result in
                            self.materialization_cut(phi, &phis, &pending_materializations)
                        {
                            if !committed_materializations.insert(result) {
                                continue;
                            }
                            let Some(candidate) = pending_materializations.get(&result) else {
                                continue;
                            };
                            diagnostics.gated_recovered += 1;
                            recovered_results.insert(result);
                            expressions.push(candidate.clone());
                        }
                    } else if self.can_compose(phi, &value) {
                        diagnostics.gated_recovered += 1;
                        recovered_results.insert(expression.result);
                        recovered_values.insert(expression.result, value);
                    } else if SelectionMaterialization::new(self.graph).accepts_cut(phi, &value) {
                        pending_materializations.insert(expression.result, expression);
                    } else {
                        diagnostics.rejected.push(GatedPhiDiagnostic {
                            block: phi.block,
                            register: phi.result.reg_num,
                            version: phi.result.version,
                            reason: GatedPhiRejection::CompositionCost,
                        });
                    }
                }
                PhiDecision::Specialized(specialization) => {
                    diagnostics.gated_recovered += 1;
                    diagnostics.gated_specialized += 1;
                    recovered_results.insert(specialization.result);
                    specializations.push(specialization);
                }
                PhiDecision::Rejected(reason) => diagnostics.rejected.push(GatedPhiDiagnostic {
                    block: phi.block,
                    register: phi.result.reg_num,
                    version: phi.result.version,
                    reason,
                }),
            }
        }
        for (result, expression) in &pending_materializations {
            if committed_materializations.contains(result) {
                continue;
            }
            diagnostics.rejected.push(GatedPhiDiagnostic {
                block: expression.block,
                register: result.reg_num,
                version: result.version,
                reason: GatedPhiRejection::CompositionCost,
            });
        }
        let required = self.required_by_unrecovered(&live, &recovered_results);
        eliminated.extend(
            recovered_results
                .into_iter()
                .filter(|result| !roots.contains(result) && !required.contains(result)),
        );
        let ordinal = self
            .graph
            .phis
            .iter()
            .enumerate()
            .map(|(index, phi)| (phi.result, index))
            .collect::<BTreeMap<_, _>>();
        expressions.sort_by_key(|expression| ordinal.get(&expression.result).copied());
        specializations.sort_by_key(|specialization| ordinal.get(&specialization.result).copied());
        Ok(GatedPhiRecovery {
            expressions,
            specializations,
            eliminated,
            diagnostics,
        })
    }

    fn live_phis(&self) -> BTreeSet<SsaVar> {
        let phis = self
            .graph
            .phis
            .iter()
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let semantic_roots = self.graph.semantic_use_roots();
        let mut live = BTreeSet::new();
        let mut pending = phis
            .keys()
            .filter(|result| {
                semantic_roots.contains(result) || self.graph.has_reaching_use(**result)
            })
            .copied()
            .collect::<Vec<_>>();
        while let Some(result) = pending.pop() {
            if !live.insert(result) {
                continue;
            }
            let Some(phi) = phis.get(&result) else {
                continue;
            };
            pending.extend(
                phi.inputs
                    .iter()
                    .map(|input| self.graph.copy_source(input.value))
                    .filter(|input| phis.contains_key(input)),
            );
        }
        live
    }

    fn can_compose(&self, phi: &crate::ir::analysis::PhiMerge, value: &SemanticExpression) -> bool {
        super::effects::EffectSummary::expression(value)
            .without_control()
            .is_pure()
            && SelectionCost::of(value) <= phi.inputs.len()
            && self.expression_available_at(value, phi.block)
    }

    fn materialization_cut(
        &self,
        root: &crate::ir::analysis::PhiMerge,
        phis: &BTreeMap<SsaVar, &crate::ir::analysis::PhiMerge>,
        candidates: &BTreeMap<SsaVar, PhiExpression>,
    ) -> BTreeSet<SsaVar> {
        let mut cut = BTreeSet::new();
        let mut pending = root
            .inputs
            .iter()
            .map(|input| self.graph.copy_source(input.value))
            .collect::<Vec<_>>();
        while let Some(result) = pending.pop() {
            if !candidates.contains_key(&result) || !cut.insert(result) {
                continue;
            }
            pending.extend(
                phis.get(&result)
                    .into_iter()
                    .flat_map(|phi| &phi.inputs)
                    .map(|input| self.graph.copy_source(input.value)),
            );
        }
        cut
    }

    fn expression_available_at(&self, value: &SemanticExpression, block: BlockId) -> bool {
        SemanticExpressionFacts::of_expression(value)
            .used_ssa_variables()
            .all(|value| {
                self.values
                    .value(value)
                    .and_then(|value| value.definition)
                    .is_none_or(|definition| {
                        self.control.dominators.dominates(definition.block, block)
                    })
            })
    }

    fn phi_order(&self, live: &BTreeSet<SsaVar>) -> Vec<&crate::ir::analysis::PhiMerge> {
        let phis = self
            .graph
            .phis
            .iter()
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let mut indegree = live
            .iter()
            .map(|result| {
                let dependencies = phis
                    .get(result)
                    .into_iter()
                    .flat_map(|phi| &phi.inputs)
                    .map(|input| self.graph.copy_source(input.value))
                    .filter(|input| live.contains(input))
                    .count();
                (*result, dependencies)
            })
            .collect::<BTreeMap<_, _>>();
        let mut successors = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        for result in live {
            for input in phis
                .get(result)
                .into_iter()
                .flat_map(|phi| &phi.inputs)
                .map(|input| self.graph.copy_source(input.value))
                .filter(|input| live.contains(input))
            {
                successors.entry(input).or_default().insert(*result);
            }
        }
        let mut ready = indegree
            .iter()
            .filter_map(|(result, degree)| (*degree == 0).then_some(*result))
            .collect::<BTreeSet<_>>();
        let mut order = Vec::with_capacity(self.graph.phis.len());
        while let Some(result) = ready.pop_first() {
            if let Some(phi) = phis.get(&result) {
                order.push(*phi);
            }
            for successor in successors.get(&result).into_iter().flatten() {
                let Some(degree) = indegree.get_mut(successor) else {
                    continue;
                };
                *degree -= 1;
                if *degree == 0 {
                    ready.insert(*successor);
                }
            }
        }
        let ordered = order.iter().map(|phi| phi.result).collect::<BTreeSet<_>>();
        order.extend(
            self.graph
                .phis
                .iter()
                .filter(|phi| !live.contains(&phi.result) || !ordered.contains(&phi.result)),
        );
        order
    }

    fn required_by_unrecovered(
        &self,
        live: &BTreeSet<SsaVar>,
        recovered: &BTreeSet<SsaVar>,
    ) -> BTreeSet<SsaVar> {
        let phis = self
            .graph
            .phis
            .iter()
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let mut required = BTreeSet::new();
        let mut pending = live
            .iter()
            .filter(|result| !recovered.contains(result))
            .copied()
            .collect::<Vec<_>>();
        while let Some(result) = pending.pop() {
            let Some(phi) = phis.get(&result) else {
                continue;
            };
            for input in &phi.inputs {
                let input = self.graph.copy_source(input.value);
                if live.contains(&input) && required.insert(input) {
                    pending.push(input);
                }
            }
        }
        required
    }

    fn expression(
        &self,
        phi: &crate::ir::analysis::PhiMerge,
        canonical: &BTreeMap<SsaVar, InsnArg>,
        recovered: &BTreeMap<SsaVar, SemanticExpression>,
        semantic_predicates: bool,
        diagnostics: &mut ValueRecoveryDiagnostics,
    ) -> Result<PhiDecision, ValueRecoveryError> {
        if self.graph.definitions.contains_key(&phi.result) {
            return Ok(PhiDecision::Rejected(GatedPhiRejection::ExistingDefinition));
        }
        if phi.inputs.len() < 2 {
            return Ok(PhiDecision::Rejected(GatedPhiRejection::InsufficientInputs));
        }
        if self.control.is_loop_header(phi.block) {
            return Ok(PhiDecision::Rejected(GatedPhiRejection::LoopCarried));
        }
        if phi
            .inputs
            .iter()
            .any(|input| self.graph.copy_source(input.value) == phi.result)
        {
            return Ok(PhiDecision::Rejected(GatedPhiRejection::CyclicInput));
        }
        if phi.inputs.iter().any(|input| {
            let input = self.graph.copy_source(input.value);
            self.graph
                .definitions
                .get(&input)
                .is_some_and(|definitions| {
                    definitions.len() != 1 && !ValueFlowGraph::are_structural_replicas(definitions)
                })
        }) {
            return Ok(PhiDecision::Rejected(
                GatedPhiRejection::AmbiguousInputDefinition,
            ));
        }
        let Some(selection) = self.control.region(phi.block) else {
            return Ok(PhiDecision::Rejected(
                GatedPhiRejection::MissingSelectionRegion,
            ));
        };
        let specialization_rejection =
            match PhiUseSpecializer::new(self.graph, self.control).specialize(phi, selection)? {
                Ok(specialization) => return Ok(PhiDecision::Specialized(specialization)),
                Err(reason) => reason,
            };
        if !self.graph.block_domains.contains_key(&phi.block) {
            return Ok(PhiDecision::Rejected(specialization_rejection));
        }
        let mut variables = selection.care.symbols();
        for input in &phi.inputs {
            let Some(gate) = selection.gate(input) else {
                return Ok(PhiDecision::Rejected(GatedPhiRejection::MissingInputGate));
            };
            variables.extend(gate.symbols());
        }
        let mut logic = DomainLogic::new(&variables);
        let care_domain = logic.compile(&selection.care)?;
        let mut groups = BTreeMap::<SelectedValue, SelectedGroup>::new();
        let mut care = None;
        for input in &phi.inputs {
            let Some((key, value)) = self.value(input, canonical, recovered) else {
                return Ok(PhiDecision::Rejected(
                    GatedPhiRejection::UnsupportedInputValue,
                ));
            };
            let Some(gate) = selection.gate(input) else {
                return Ok(PhiDecision::Rejected(GatedPhiRejection::MissingInputGate));
            };
            let gate = logic.compile(gate)?;
            care = Some(match care {
                Some(care) => logic.or(care, gate)?,
                None => gate,
            });
            match groups.get_mut(&key) {
                Some(group) => group.gate = logic.or(group.gate, gate)?,
                None => {
                    groups.insert(key.clone(), SelectedGroup { key, value, gate });
                }
            }
        }
        let Some(care) = care else {
            return Ok(PhiDecision::Rejected(GatedPhiRejection::MissingInputGate));
        };
        if !logic.equivalent(care, care_domain)? {
            return Ok(PhiDecision::Rejected(GatedPhiRejection::IncompleteCoverage));
        }
        if groups.len() < 2 {
            return Ok(PhiDecision::Rejected(GatedPhiRejection::TrivialValueSet));
        }
        let groups = groups.into_values().collect::<Vec<_>>();
        for (index, left) in groups.iter().enumerate() {
            for right in &groups[index + 1..] {
                if !logic.disjoint(left.gate, right.gate)? {
                    return Ok(PhiDecision::Rejected(GatedPhiRejection::OverlappingGates));
                }
            }
        }
        let predicates = GatedPredicateLookup {
            graph: self.graph,
            control: self.control,
            semantic: semantic_predicates,
        };
        let Some(value) =
            SelectionTreeBuilder::new(&mut logic, &predicates, diagnostics).build(care, groups)?
        else {
            return Ok(PhiDecision::Rejected(
                GatedPhiRejection::PredicateNotRecoverable,
            ));
        };

        let result = crate::ir::RegisterArg::new_ssa(
            phi.result.reg_num,
            phi.result.version,
            self.value_type(phi.result),
        );
        Ok(PhiDecision::Recovered(PhiExpression {
            block: phi.block,
            result: phi.result,
            statement: SemanticStatement {
                site: None,
                origin: Some(StatementOrigin {
                    block: phi.block,
                    instruction: phi.instruction,
                }),
                kind: crate::ir::SemanticStatementKind::Definition {
                    id: phi.instruction,
                    result,
                    value,
                },
            },
        }))
    }

    fn value(
        &self,
        input: &PhiInput,
        canonical: &BTreeMap<SsaVar, InsnArg>,
        recovered: &BTreeMap<SsaVar, SemanticExpression>,
    ) -> Option<(SelectedValue, SemanticExpression)> {
        let source = self.graph.copy_source(input.value);
        if let Some(value) = recovered.get(&source) {
            return Some((SelectedValue::Variable(source), value.clone()));
        }
        let value = self.graph.resolve_canonical(
            InsnArg::reg_ssa(source.reg_num, source.version, self.value_type(source)),
            canonical,
        );
        let key = match &value {
            InsnArg::Lit(literal) => SelectedValue::Literal(literal.value),
            InsnArg::Reg(register) => SelectedValue::Variable(self.graph.key(register)?),
            InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::Const => {
                SelectedValue::Literal(instruction.args.first()?.as_literal()?.value)
            }
            InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::ConstStr => {
                SelectedValue::String(instruction.payload.string_value.clone()?)
            }
            InsnArg::Wrapped(_) => return None,
        };
        Some((key, SemanticExpression::from_argument(value).ok()?))
    }

    fn value_type(&self, value: SsaVar) -> crate::ir::ArgType {
        self.values
            .value(value)
            .and_then(|value| {
                value
                    .observed_types
                    .iter()
                    .find(|ty| ty.is_known())
                    .cloned()
            })
            .unwrap_or_else(crate::ir::ArgType::unknown)
    }
}

struct PhiUseSpecializer<'a> {
    graph: &'a ValueFlowGraph<'a>,
    control: &'a GatedControlFlow,
}

impl<'a> PhiUseSpecializer<'a> {
    const EXPRESSION_NODE_LIMIT: usize = 64;

    fn new(graph: &'a ValueFlowGraph<'a>, control: &'a GatedControlFlow) -> Self {
        Self { graph, control }
    }

    fn specialize(
        &self,
        phi: &crate::ir::analysis::PhiMerge,
        selection: &SelectionRegion,
    ) -> Result<Result<PhiUseSpecialization, GatedPhiRejection>, ValueRecoveryError> {
        let Some(uses) = self.graph.uses.get(&phi.result) else {
            return Ok(Err(GatedPhiRejection::UnusedResult));
        };
        let lowering = GateDomainLowering::new(self.control);
        let mut grouped = BTreeMap::<SsaVar, (InsnArg, Vec<BoolExpr>)>::new();
        for input in &phi.inputs {
            let Some(gate) = selection.gate(input).and_then(|gate| lowering.lower(gate)) else {
                return Ok(Err(GatedPhiRejection::UnmappedInputGate));
            };
            let source = self.graph.copy_source(input.value);
            let value = InsnArg::reg_ssa(source.reg_num, source.version, self.value_type(source));
            let group = grouped.entry(source).or_insert_with(|| (value, Vec::new()));
            group.1.push(gate);
        }

        let mut use_domains = Vec::with_capacity(uses.len());
        for usage in uses {
            let Some(site) = usage.site else {
                return Ok(Err(GatedPhiRejection::UnaddressableUse));
            };
            let Some(domain) = self.graph.logic.expression_under(
                usage.domain,
                self.graph.logic.truth(),
                Self::EXPRESSION_NODE_LIMIT,
            )?
            else {
                return Ok(Err(GatedPhiRejection::UnrecoverableUseDomain));
            };
            use_domains.push((site, domain));
        }

        let grouped = grouped
            .into_values()
            .map(|(value, gates)| (value, BoolExpr::or(gates)))
            .collect::<Vec<_>>();
        let mut variables = BTreeSet::new();
        for (_, gate) in &grouped {
            variables.extend(gate.symbols());
        }
        for (_, domain) in &use_domains {
            variables.extend(domain.symbols());
        }
        let mut logic = DomainLogic::new(&variables);
        let mut inputs = Vec::with_capacity(grouped.len());
        for (value, gate) in grouped {
            inputs.push((value, logic.compile(&gate)?));
        }

        let mut replacements = BTreeMap::<UseSite, InsnArg>::new();
        for (site, domain) in use_domains {
            let domain = logic.compile(&domain)?;
            let mut selected = None;
            for (value, gate) in &inputs {
                if logic.disjoint(domain, *gate)? {
                    continue;
                }
                if selected.is_some() {
                    return Ok(Err(GatedPhiRejection::AmbiguousUseDomain));
                }
                selected = Some((value, *gate));
            }
            let Some((value, gate)) = selected else {
                return Ok(Err(GatedPhiRejection::IncompleteUseDomain));
            };
            if !logic.implies(domain, gate)? {
                return Ok(Err(GatedPhiRejection::IncompleteUseDomain));
            }
            replacements.insert(site, value.clone());
        }

        if replacements.is_empty() {
            return Ok(Err(GatedPhiRejection::UnaddressableUse));
        }
        Ok(Ok(PhiUseSpecialization {
            result: phi.result,
            replacements: replacements.into_iter().collect(),
        }))
    }

    fn value_type(&self, value: SsaVar) -> crate::ir::ArgType {
        self.graph.phi_value_type(value)
    }
}

struct GateDomainLowering<'a> {
    control: &'a GatedControlFlow,
}

impl<'a> GateDomainLowering<'a> {
    fn new(control: &'a GatedControlFlow) -> Self {
        Self { control }
    }

    fn lower(&self, expression: &BoolExpr) -> Option<BoolExpr> {
        let mut pending = vec![GateDomainTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                GateDomainTask::Visit(expression) => match expression {
                    BoolExpr::True => results.push(BoolExpr::True),
                    BoolExpr::False => results.push(BoolExpr::False),
                    BoolExpr::Symbol(BoolVariable::Block(block)) => {
                        results.push(BoolExpr::instruction(self.control.test(*block)?.id));
                    }
                    BoolExpr::Symbol(symbol) => {
                        results.push(BoolExpr::Symbol(symbol.clone()));
                    }
                    BoolExpr::Not(inner) => {
                        pending.push(GateDomainTask::Not);
                        pending.push(GateDomainTask::Visit(inner));
                    }
                    BoolExpr::And(terms) => {
                        pending.push(GateDomainTask::Junction {
                            count: terms.len(),
                            conjunction: true,
                        });
                        pending.extend(terms.iter().rev().map(GateDomainTask::Visit));
                    }
                    BoolExpr::Or(terms) => {
                        pending.push(GateDomainTask::Junction {
                            count: terms.len(),
                            conjunction: false,
                        });
                        pending.extend(terms.iter().rev().map(GateDomainTask::Visit));
                    }
                },
                GateDomainTask::Not => {
                    let inner = results.pop()?;
                    results.push(BoolExpr::not(inner));
                }
                GateDomainTask::Junction { count, conjunction } => {
                    let start = results.len().checked_sub(count)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        BoolExpr::and(terms)
                    } else {
                        BoolExpr::or(terms)
                    });
                }
            }
        }
        (results.len() == 1).then(|| results.pop()).flatten()
    }
}

enum GateDomainTask<'a> {
    Visit(&'a BoolExpr),
    Not,
    Junction { count: usize, conjunction: bool },
}

trait PredicateLookup {
    fn predicate(&self, variable: &BoolVariable) -> Option<SemanticOperation>;
}

struct GatedPredicateLookup<'a> {
    graph: &'a ValueFlowGraph<'a>,
    control: &'a GatedControlFlow,
    semantic: bool,
}

impl PredicateLookup for GatedPredicateLookup<'_> {
    fn predicate(&self, variable: &BoolVariable) -> Option<SemanticOperation> {
        let BoolVariable::Block(block) = variable else {
            return None;
        };
        if !self.semantic {
            return self.control.predicate(variable);
        }
        let instruction = self.control.test(*block)?.id;
        let test = self.graph.predicate_tests.get(&instruction)?.clone();
        super::effects::EffectSummary::operation(&test)
            .without_control()
            .is_pure()
            .then_some(test)
    }
}

impl PredicateLookup for GatedControlFlow {
    fn predicate(&self, variable: &BoolVariable) -> Option<SemanticOperation> {
        let BoolVariable::Block(block) = variable else {
            return None;
        };
        let test = self.test(*block)?;
        InstructionEffects::of_tree(test)
            .without_control()
            .is_pure()
            .then(|| SemanticOperation::from_instruction(test.clone()).ok())
            .flatten()
    }
}

impl PredicateLookup for ValueFlowGraph<'_> {
    fn predicate(&self, variable: &BoolVariable) -> Option<SemanticOperation> {
        let BoolVariable::Instruction(instruction) = variable else {
            return None;
        };
        let test = self.predicate_tests.get(instruction)?.clone();
        super::effects::EffectSummary::operation(&test)
            .without_control()
            .is_pure()
            .then_some(test)
    }
}

struct SourcePredicateLookup<'a> {
    graph: &'a ValueFlowGraph<'a>,
    movable: &'a BTreeSet<crate::ir::InstructionId>,
}

impl PredicateLookup for SourcePredicateLookup<'_> {
    fn predicate(&self, variable: &BoolVariable) -> Option<SemanticOperation> {
        let BoolVariable::Instruction(instruction) = variable else {
            return None;
        };
        let test = self.graph.predicate_tests.get(instruction)?.clone();
        let effect = super::effects::EffectSummary::operation(&test).without_control();
        (effect.is_pure() || self.movable.contains(instruction)).then_some(test)
    }
}

struct SelectionTreeBuilder<'a, Lookup> {
    logic: &'a mut DomainLogic,
    predicates: &'a Lookup,
    diagnostics: &'a mut ValueRecoveryDiagnostics,
}

impl<'a, Lookup: PredicateLookup> SelectionTreeBuilder<'a, Lookup> {
    const EXACT_PARTITION_LIMIT: usize = 10;
    const EXPRESSION_NODE_LIMIT: usize = 64;

    fn new(
        logic: &'a mut DomainLogic,
        predicates: &'a Lookup,
        diagnostics: &'a mut ValueRecoveryDiagnostics,
    ) -> Self {
        Self {
            logic,
            predicates,
            diagnostics,
        }
    }

    fn build(
        &mut self,
        care: ControlDomain,
        mut groups: Vec<SelectedGroup>,
    ) -> Result<Option<SemanticExpression>, ValueRecoveryError> {
        groups.sort_by_key(|group| group.gate);
        self.build_node(care, groups)
    }

    fn build_node(
        &mut self,
        care: ControlDomain,
        groups: Vec<SelectedGroup>,
    ) -> Result<Option<SemanticExpression>, ValueRecoveryError> {
        if let [group] = groups.as_slice() {
            return Ok(Some(group.value.clone()));
        }
        self.diagnostics.decision_nodes += 1;
        let Some(split) = self.best_split(care, &groups)? else {
            return Ok(None);
        };
        let mut left = Vec::new();
        let mut right = Vec::new();
        for (index, group) in groups.into_iter().enumerate() {
            if split.left[index] {
                left.push(group);
            } else {
                right.push(group);
            }
        }
        let Some(left_value) = self.build_node(split.left_domain, left)? else {
            return Ok(None);
        };
        let Some(right_value) = self.build_node(split.right_domain, right)? else {
            return Ok(None);
        };
        let (when_true, when_false) = if split.true_is_left {
            (left_value, right_value)
        } else {
            (right_value, left_value)
        };
        Ok(Some(SemanticExpression::select(
            split.condition,
            when_true,
            when_false,
        )))
    }

    fn best_split(
        &mut self,
        care: ControlDomain,
        groups: &[SelectedGroup],
    ) -> Result<Option<DecisionSplit>, ValueRecoveryError> {
        if groups.len() <= Self::EXACT_PARTITION_LIMIT {
            self.diagnostics.exact_partition_searches += 1;
        } else {
            self.diagnostics.bounded_partition_searches += 1;
        }
        let mut best = None::<DecisionSplit>;
        for left in Self::partitions(groups.len()) {
            let Some(left_domain) = self.union(
                groups
                    .iter()
                    .zip(&left)
                    .filter_map(|(group, selected)| selected.then_some(group.gate)),
            )?
            else {
                continue;
            };
            let Some(right_domain) = self.union(
                groups
                    .iter()
                    .zip(&left)
                    .filter_map(|(group, selected)| (!selected).then_some(group.gate)),
            )?
            else {
                continue;
            };
            for (true_is_left, true_domain) in [(true, left_domain), (false, right_domain)] {
                let Some(expression) =
                    self.logic
                        .expression_under(true_domain, care, Self::EXPRESSION_NODE_LIMIT)?
                else {
                    continue;
                };
                let boolean_inversion = Self::is_boolean_inversion(groups, &left, true_is_left);
                let mut predicate_cost = PredicateCost::of(&expression);
                if boolean_inversion {
                    predicate_cost = predicate_cost.with_outer_negation();
                }
                let Some(condition) = PredicateLowering::new(self.predicates).lower(expression)
                else {
                    continue;
                };
                let left_count = left.iter().filter(|selected| **selected).count();
                let candidate = DecisionSplit {
                    cost: DecisionCost {
                        max_branch: left_count.max(groups.len() - left_count),
                        predicate: predicate_cost,
                    },
                    left: left.clone(),
                    left_domain,
                    right_domain,
                    true_is_left,
                    condition,
                };
                if best
                    .as_ref()
                    .is_none_or(|current| candidate.cost < current.cost)
                {
                    best = Some(candidate);
                }
            }
        }
        Ok(best)
    }

    fn union(
        &mut self,
        domains: impl IntoIterator<Item = ControlDomain>,
    ) -> Result<Option<ControlDomain>, ValueRecoveryError> {
        let mut union = None::<ControlDomain>;
        for domain in domains {
            union = Some(match union {
                Some(current) => self.logic.or(current, domain)?,
                None => domain,
            });
        }
        Ok(union)
    }

    fn partitions(count: usize) -> Vec<Vec<bool>> {
        if count <= Self::EXACT_PARTITION_LIMIT {
            let lower = count / 2;
            let upper = count - lower;
            return (1usize..(1usize << count) - 1)
                .filter(|mask| mask & 1 != 0)
                .filter(|mask| {
                    let selected = mask.count_ones() as usize;
                    selected == lower || selected == upper
                })
                .map(|mask| {
                    (0..count)
                        .map(|index| mask & (1usize << index) != 0)
                        .collect()
                })
                .collect();
        }

        let width = count / 2;
        let mut partitions = BTreeSet::new();
        for start in 0..count {
            let mut selected = vec![false; count];
            for offset in 0..width {
                selected[(start + offset) % count] = true;
            }
            if !selected[0] {
                selected.iter_mut().for_each(|value| *value = !*value);
            }
            partitions.insert(selected);
        }
        partitions.into_iter().collect()
    }

    fn is_boolean_inversion(groups: &[SelectedGroup], left: &[bool], true_is_left: bool) -> bool {
        if groups.len() != 2 {
            return false;
        }
        let true_value = groups
            .iter()
            .zip(left)
            .find(|(_, selected)| **selected == true_is_left)
            .map(|(group, _)| &group.key);
        let false_value = groups
            .iter()
            .zip(left)
            .find(|(_, selected)| **selected != true_is_left)
            .map(|(group, _)| &group.key);
        matches!(true_value, Some(SelectedValue::Literal(0)))
            && matches!(false_value, Some(SelectedValue::Literal(1)))
    }
}

struct DecisionSplit {
    cost: DecisionCost,
    left: Vec<bool>,
    left_domain: ControlDomain,
    right_domain: ControlDomain,
    true_is_left: bool,
    condition: SemanticPredicate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct DecisionCost {
    max_branch: usize,
    predicate: PredicateCost,
}

struct PredicateLowering<'a, Lookup> {
    predicates: &'a Lookup,
}

impl<'a, Lookup: PredicateLookup> PredicateLowering<'a, Lookup> {
    fn new(predicates: &'a Lookup) -> Self {
        Self { predicates }
    }

    fn lower(&self, expression: BoolExpr) -> Option<SemanticPredicate> {
        let mut pending = vec![PredicateTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                PredicateTask::Visit(expression) => match expression {
                    BoolExpr::True => results.push(SemanticPredicate::True),
                    BoolExpr::False => results.push(SemanticPredicate::False),
                    BoolExpr::Symbol(variable) => results.push(SemanticPredicate::Test(
                        self.predicates.predicate(&variable)?,
                    )),
                    BoolExpr::Not(inner) => {
                        pending.push(PredicateTask::Not);
                        pending.push(PredicateTask::Visit(*inner));
                    }
                    BoolExpr::And(terms) => {
                        pending.push(PredicateTask::Junction {
                            count: terms.len(),
                            conjunction: true,
                        });
                        pending.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                    }
                    BoolExpr::Or(terms) => {
                        pending.push(PredicateTask::Junction {
                            count: terms.len(),
                            conjunction: false,
                        });
                        pending.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                    }
                },
                PredicateTask::Not => {
                    let inner = results.pop()?;
                    results.push(SemanticPredicate::Not(Box::new(inner)));
                }
                PredicateTask::Junction { count, conjunction } => {
                    let start = results.len().checked_sub(count)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        SemanticPredicate::And(terms)
                    } else {
                        SemanticPredicate::Or(terms)
                    });
                }
            }
        }
        (results.len() == 1).then(|| results.pop()).flatten()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PredicateCost {
    nodes: usize,
    depth: usize,
    negations: usize,
}

impl PredicateCost {
    fn of(expression: &BoolExpr) -> Self {
        let mut nodes = 0;
        let mut depth = 0;
        let mut negations = 0;
        let mut pending = vec![(expression, 1usize)];
        while let Some((expression, current_depth)) = pending.pop() {
            nodes += 1;
            depth = depth.max(current_depth);
            match expression {
                BoolExpr::Not(inner) => {
                    negations += 1;
                    pending.push((inner, current_depth + 1));
                }
                BoolExpr::And(terms) | BoolExpr::Or(terms) => {
                    pending.extend(terms.iter().map(|term| (term, current_depth + 1)))
                }
                BoolExpr::True | BoolExpr::False | BoolExpr::Symbol(_) => {}
            }
        }
        Self {
            nodes,
            depth,
            negations,
        }
    }

    fn with_outer_negation(mut self) -> Self {
        self.nodes += 1;
        self.depth += 1;
        self.negations += 1;
        self
    }
}

enum PredicateTask {
    Visit(BoolExpr),
    Not,
    Junction { count: usize, conjunction: bool },
}

pub(in crate::analysis::value_recovery) struct PhiExpressionPlacement {
    statements: BTreeMap<BlockId, Vec<SemanticStatement>>,
    recovered: BTreeSet<SsaVar>,
    placed: BTreeSet<BlockId>,
}

impl PhiExpressionPlacement {
    pub(in crate::analysis::value_recovery) fn new(expressions: Vec<PhiExpression>) -> Self {
        let mut statements = BTreeMap::<BlockId, Vec<SemanticStatement>>::new();
        let mut recovered = BTreeSet::new();
        for expression in expressions {
            statements
                .entry(expression.block)
                .or_default()
                .push(expression.statement);
            recovered.insert(expression.result);
        }
        Self {
            statements,
            recovered,
            placed: BTreeSet::new(),
        }
    }

    pub(in crate::analysis::value_recovery) fn recovered(&self) -> &BTreeSet<SsaVar> {
        &self.recovered
    }

    pub(in crate::analysis::value_recovery) fn apply(
        mut self,
        root: &mut SemanticNode,
    ) -> Result<(), ValueRecoveryError> {
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = self.fold_node(body)?;
        if let Some(block) = self
            .statements
            .keys()
            .find(|block| !self.placed.contains(block))
            .copied()
        {
            return Err(ValueRecoveryError::MissingPhiPlacement(block));
        }
        Ok(())
    }
}

impl SemanticFolder for PhiExpressionPlacement {
    type Error = ValueRecoveryError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::BasicBlock(mut block) = node else {
            return Ok(node);
        };
        let Some(mut statements) = self.statements.get(&block.id).cloned() else {
            return Ok(SemanticNode::BasicBlock(block));
        };
        self.placed.insert(block.id);
        statements.append(&mut block.statements);
        block.statements = statements;
        Ok(SemanticNode::BasicBlock(block))
    }
}
