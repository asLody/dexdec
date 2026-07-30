//! SSA edge arguments preserved across control-graph contractions.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::{InstructionEffects, SsaValueGraph, SsaVar},
    BlockId, EdgeKind, InsnArg, InsnNode, InsnType, InstructionEquivalence, InstructionTransform,
    InstructionTree, RegisterArg, CFG,
};

use super::{ControlContractions, SourceVariableError};

#[derive(Clone)]
pub(super) struct ResolvedEdgeArgument {
    pub(super) predecessor: BlockId,
    pub(super) entry: BlockId,
    pub(super) edge_kind: EdgeKind,
    pub(super) value: EdgeArgumentValue,
}

#[derive(Clone)]
pub(super) enum EdgeArgumentValue {
    Explicit(InsnArg),
    DestinationBinding,
}

impl EdgeArgumentValue {
    pub(super) fn explicit(&self) -> Option<&InsnArg> {
        match self {
            Self::Explicit(value) => Some(value),
            Self::DestinationBinding => None,
        }
    }

    pub(super) fn into_explicit(self) -> Option<InsnArg> {
        match self {
            Self::Explicit(value) => Some(value),
            Self::DestinationBinding => None,
        }
    }
}

/// Computes the block arguments of a surviving CFG node after a subgraph has
/// been contracted. Each incoming boundary edge is evaluated independently,
/// so Phi values retain the path semantics of the original SSA graph.
pub(super) struct ContractedEdgeArguments<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    constants: &'a BTreeMap<SsaVar, InsnArg>,
    contractions: &'a ControlContractions,
}

impl<'a> ContractedEdgeArguments<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        values: &'a SsaValueGraph,
        constants: &'a BTreeMap<SsaVar, InsnArg>,
        contractions: &'a ControlContractions,
    ) -> Self {
        Self {
            cfg,
            values,
            constants,
            contractions,
        }
    }

    pub(super) fn resolve(
        &self,
        successor: BlockId,
        phi: &InsnNode,
    ) -> Result<Option<Vec<ResolvedEdgeArgument>>, SourceVariableError> {
        let mut component = self.contractions.component(successor);
        let direct_component = component.iter().any(|block| *block != successor);
        if direct_component {
            component.remove(&successor);
        } else if let Some(terminal) = self
            .contractions
            .terminal(successor)
            .filter(|terminal| *terminal != successor)
        {
            component = self.contractions.component(terminal);
            component.remove(&terminal);
        } else {
            component.remove(&successor);
        }
        if component.is_empty()
            || !phi
                .payload
                .phi_edges
                .iter()
                .any(|(predecessor, _)| component.contains(predecessor))
        {
            return Ok(None);
        }

        let boundaries = component
            .iter()
            .flat_map(|entry| {
                self.cfg
                    .incoming_edges(*entry)
                    .into_iter()
                    .filter(|(predecessor, _)| !component.contains(predecessor))
                    .map(|(predecessor, edge_kind)| (predecessor, *entry, edge_kind))
            })
            .collect::<BTreeSet<_>>();
        let mut resolved = Vec::new();
        for (predecessor, entry, edge_kind) in boundaries {
            let reachable = self.reachable(entry, &component);
            let mut evaluator = BoundaryEvaluator::new(
                self.cfg,
                self.values,
                self.constants,
                &component,
                &reachable,
                BoundaryEdge {
                    predecessor,
                    entry,
                    edge_kind,
                },
            );
            let Some(value) = evaluator.evaluate_phi(successor, phi).into_argument() else {
                // A quotient edge may summarize several dynamically selected
                // exceptional continuations. Such an edge has no single SSA
                // argument; retain the concrete Phi edges so copy placement
                // can attach each value to its actual leave or throw site.
                return Ok(None);
            };
            resolved.push(ResolvedEdgeArgument {
                predecessor,
                entry,
                edge_kind,
                value,
            });
        }
        Ok(Some(resolved))
    }

    pub(super) fn resolve_all(
        &self,
        successor: BlockId,
        phi: &InsnNode,
    ) -> Result<Vec<ResolvedEdgeArgument>, SourceVariableError> {
        let contracted = self.resolve(successor, phi)?;
        let preserve_contracted_edges = contracted.is_none();
        let mut resolved = contracted.unwrap_or_default();
        resolved.extend(
            phi.payload
                .phi_edges
                .iter()
                .zip(&phi.args)
                .filter(|((predecessor, _), _)| {
                    preserve_contracted_edges
                        || !self
                            .contractions
                            .shares_quotient_node(*predecessor, successor)
                })
                .map(|(&(predecessor, edge_kind), value)| ResolvedEdgeArgument {
                    predecessor,
                    entry: successor,
                    edge_kind,
                    value: EdgeArgumentValue::Explicit(value.clone()),
                }),
        );
        resolved.sort_by_key(|argument| (argument.predecessor, argument.entry, argument.edge_kind));
        Ok(resolved)
    }

    fn reachable(&self, entry: BlockId, component: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !component.contains(&block) || !reachable.insert(block) {
                continue;
            }
            // A quotient edge has one completion mode. Exceptional successors
            // are owned by handler regions and propagate abruptly in Semantic
            // IR; including them here would merge an abrupt cleanup completion
            // into the normal block arguments of the continuation.
            pending.extend(
                self.cfg
                    .normal_successors(block)
                    .filter(|target| component.contains(target)),
            );
        }
        reachable
    }
}

#[derive(Clone, Copy)]
struct BoundaryEdge {
    predecessor: BlockId,
    entry: BlockId,
    edge_kind: EdgeKind,
}

struct BoundaryEvaluator<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    constants: &'a BTreeMap<SsaVar, InsnArg>,
    component: &'a BTreeSet<BlockId>,
    reachable: &'a BTreeSet<BlockId>,
    boundary: BoundaryEdge,
    states: BTreeMap<SsaVar, SymbolicValue>,
    destination_variable: Option<u32>,
}

impl<'a> BoundaryEvaluator<'a> {
    fn new(
        cfg: &'a CFG,
        values: &'a SsaValueGraph,
        constants: &'a BTreeMap<SsaVar, InsnArg>,
        component: &'a BTreeSet<BlockId>,
        reachable: &'a BTreeSet<BlockId>,
        boundary: BoundaryEdge,
    ) -> Self {
        Self {
            cfg,
            values,
            constants,
            component,
            reachable,
            boundary,
            states: BTreeMap::new(),
            destination_variable: None,
        }
    }

    fn evaluate_phi(&mut self, block: BlockId, phi: &InsnNode) -> SymbolicValue {
        self.destination_variable = phi.result.as_ref().and_then(|result| result.code_var);
        self.solve();
        self.merge_phi_inputs(block, phi)
    }

    fn solve(&mut self) {
        loop {
            let mut changed = false;
            for block in self.reachable {
                let Some(body) = self.cfg.block(*block) else {
                    continue;
                };
                for instruction in &body.insns {
                    let Some(result) = instruction.result.as_ref().and_then(SsaVar::from_reg)
                    else {
                        continue;
                    };
                    let next = self.evaluate_instruction(*block, instruction);
                    changed |= self
                        .states
                        .entry(result)
                        .or_insert(SymbolicValue::Unknown)
                        .advance(next);
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn evaluate_instruction(&self, block: BlockId, instruction: &InsnNode) -> SymbolicValue {
        let Some(result) = instruction.result.as_ref().and_then(SsaVar::from_reg) else {
            return SymbolicValue::Conflict;
        };
        if let Some(constant) = self.constants.get(&result) {
            return SymbolicValue::Known(constant.clone());
        }
        match instruction.insn_type {
            InsnType::Const | InsnType::ConstStr => {
                SymbolicValue::Known(InsnArg::wrap(instruction.clone()))
            }
            InsnType::Move => instruction
                .args
                .first()
                .map(|argument| self.argument(argument))
                .unwrap_or(SymbolicValue::Conflict),
            InsnType::MoveException => SymbolicValue::DestinationBinding,
            InsnType::Phi => self.merge_phi_inputs(block, instruction),
            _ if InstructionEffects::of_tree(instruction).is_pure() => {
                self.evaluate_expression(instruction)
            }
            _ => SymbolicValue::Conflict,
        }
    }

    fn evaluate_expression(&self, instruction: &InsnNode) -> SymbolicValue {
        let mut substitution = BoundarySubstitution::new(self);
        let expression = match InstructionTree::transform(instruction.clone(), &mut substitution) {
            Ok(expression) => expression,
            Err(_) => return SymbolicValue::Conflict,
        };
        match substitution.failure {
            Some(SymbolicFailure::Unknown) => SymbolicValue::Unknown,
            Some(SymbolicFailure::Conflict) => SymbolicValue::Conflict,
            None => SymbolicValue::Known(InsnArg::wrap(expression)),
        }
    }

    fn merge_phi_inputs(&self, block: BlockId, phi: &InsnNode) -> SymbolicValue {
        let inputs = phi
            .payload
            .phi_edges
            .iter()
            .zip(&phi.args)
            .filter(|((predecessor, edge_kind), _)| {
                if block == self.boundary.entry {
                    *predecessor == self.boundary.predecessor
                        && *edge_kind == self.boundary.edge_kind
                } else {
                    self.reachable.contains(predecessor)
                }
            })
            .map(|(_, argument)| self.argument(argument));
        SymbolicValue::merge(inputs)
    }

    fn argument(&self, argument: &InsnArg) -> SymbolicValue {
        let Some(register) = argument.as_register() else {
            return SymbolicValue::Known(argument.clone());
        };
        let Some(value) = SsaVar::from_reg(register) else {
            return SymbolicValue::Conflict;
        };
        if register.code_var.is_some() && register.code_var == self.destination_variable {
            return SymbolicValue::Known(InsnArg::Reg(register.clone()));
        }
        if let Some(constant) = self.constants.get(&value) {
            return SymbolicValue::Known(constant.clone());
        }
        let definition = self.values.value(value).and_then(|value| value.definition);
        if definition.is_none_or(|position| !self.reachable.contains(&position.block)) {
            return SymbolicValue::Known(InsnArg::Reg(register.clone()));
        }
        self.states
            .get(&value)
            .cloned()
            .unwrap_or(SymbolicValue::Unknown)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SymbolicFailure {
    Unknown,
    Conflict,
}

struct BoundarySubstitution<'evaluator, 'cfg> {
    evaluator: &'evaluator BoundaryEvaluator<'cfg>,
    failure: Option<SymbolicFailure>,
}

impl<'evaluator, 'cfg> BoundarySubstitution<'evaluator, 'cfg> {
    fn new(evaluator: &'evaluator BoundaryEvaluator<'cfg>) -> Self {
        Self {
            evaluator,
            failure: None,
        }
    }

    fn record(&mut self, failure: SymbolicFailure) {
        if self.failure != Some(SymbolicFailure::Conflict) {
            self.failure = Some(failure);
        }
    }
}

impl InstructionTransform for BoundarySubstitution<'_, '_> {
    fn transform_register(&mut self, register: RegisterArg) -> InsnArg {
        match self.evaluator.argument(&InsnArg::Reg(register.clone())) {
            SymbolicValue::Known(argument) => argument,
            SymbolicValue::Unknown => {
                self.record(SymbolicFailure::Unknown);
                InsnArg::Reg(register)
            }
            SymbolicValue::DestinationBinding | SymbolicValue::Conflict => {
                self.record(SymbolicFailure::Conflict);
                InsnArg::Reg(register)
            }
        }
    }
}

#[derive(Debug, Clone)]
enum SymbolicValue {
    Unknown,
    Known(InsnArg),
    DestinationBinding,
    Conflict,
}

impl SymbolicValue {
    fn merge(values: impl Iterator<Item = Self>) -> Self {
        let mut merged: Option<MergedValue> = None;
        let mut has_input = false;
        for value in values {
            has_input = true;
            match value {
                // Unknown is the lattice bottom used while a cyclic SSA
                // component is converging. It contributes no information;
                // a later iteration can still refine it to a value or a
                // conflict.
                Self::Unknown => {}
                Self::Conflict => return Self::Conflict,
                Self::DestinationBinding => match &merged {
                    Some(MergedValue::DestinationBinding) => {}
                    Some(MergedValue::Known(_)) => return Self::Conflict,
                    None => merged = Some(MergedValue::DestinationBinding),
                },
                Self::Known(candidate) => match &merged {
                    Some(MergedValue::Known(existing)) if !same_value(existing, &candidate) => {
                        return Self::Conflict;
                    }
                    Some(MergedValue::Known(_)) => {}
                    Some(MergedValue::DestinationBinding) => return Self::Conflict,
                    None => merged = Some(MergedValue::Known(candidate)),
                },
            }
        }
        if !has_input {
            return Self::Conflict;
        }
        match merged {
            Some(MergedValue::Known(value)) => Self::Known(value),
            Some(MergedValue::DestinationBinding) => Self::DestinationBinding,
            None => Self::Unknown,
        }
    }

    fn advance(&mut self, next: Self) -> bool {
        let merged = match (&*self, next) {
            (Self::Conflict, _) => return false,
            (Self::Unknown, next) => next,
            (Self::Known(_), Self::Unknown) => return false,
            (Self::DestinationBinding, Self::Unknown | Self::DestinationBinding) => return false,
            (Self::Known(current), Self::Known(next)) if same_value(current, &next) => {
                return false;
            }
            (Self::Known(_), Self::Known(_) | Self::DestinationBinding | Self::Conflict)
            | (Self::DestinationBinding, Self::Known(_) | Self::Conflict) => Self::Conflict,
        };
        if matches!((&*self, &merged), (Self::Unknown, Self::Unknown)) {
            return false;
        }
        *self = merged;
        true
    }

    fn into_argument(self) -> Option<EdgeArgumentValue> {
        match self {
            Self::Known(argument) => Some(EdgeArgumentValue::Explicit(argument)),
            Self::DestinationBinding => Some(EdgeArgumentValue::DestinationBinding),
            Self::Unknown | Self::Conflict => None,
        }
    }
}

enum MergedValue {
    Known(InsnArg),
    DestinationBinding,
}

pub(super) fn same_value(left: &InsnArg, right: &InsnArg) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (InsnArg::Reg(left), InsnArg::Reg(right)) => {
                if !SsaVar::from_reg(left).is_some_and(|left| SsaVar::from_reg(right) == Some(left))
                {
                    return false;
                }
            }
            (InsnArg::Lit(left), InsnArg::Lit(right)) => {
                if left != right {
                    return false;
                }
            }
            (InsnArg::Wrapped(left), InsnArg::Wrapped(right)) => {
                if !left.operation_equivalent(right)
                    || left.result.as_ref().map(|result| &result.ty)
                        != right.result.as_ref().map(|result| &result.ty)
                    || left.args.len() != right.args.len()
                {
                    return false;
                }
                match (
                    left.payload.compound_target.as_ref(),
                    right.payload.compound_target.as_ref(),
                ) {
                    (Some(left), Some(right)) => pending.push((left, right)),
                    (None, None) => {}
                    _ => return false,
                }
                pending.extend(left.args.iter().zip(&right.args));
            }
            _ => return false,
        }
    }
    true
}
