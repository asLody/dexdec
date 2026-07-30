//! Reify verified DEX object initialization as one constructor value.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::analysis::{
    DominanceError, DominanceFrontier, DominatorTree, InsnPosition, ObjectInitialization,
    ObjectInitializationError, ObjectInitializations, SsaInvariantError, SsaValueGraph, SsaVar,
    TypeHierarchy,
};
use crate::ir::{
    ArgType, BlockId, EdgeKind, InsnArg, InsnNode, InsnType, InstructionTransform, InstructionTree,
    RegisterArg, CFG,
};

use super::{Pass, PassResult};

#[derive(Debug)]
pub enum ConstructorRecoveryError {
    Ssa(SsaInvariantError),
    Initialization(ObjectInitializationError),
    InstructionTree(crate::ir::InstructionTreeError),
    Dominance(DominanceError),
    MissingDefinition(InsnPosition),
    MissingHandler(crate::ir::BlockId),
    MalformedHandlerPhi(crate::ir::BlockId),
    MissingBlock(BlockId),
    MissingPhiDefinition(BlockId),
    AmbiguousObjectValue(BlockId),
    UninitializedUse {
        position: InsnPosition,
        argument: usize,
    },
    RepeatedInitialization(InsnPosition),
}

impl std::fmt::Display for ConstructorRecoveryError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ssa(error) => write!(formatter, "invalid SSA graph: {error}"),
            Self::Initialization(error) => error.fmt(formatter),
            Self::InstructionTree(error) => {
                write!(formatter, "instruction rewrite failed: {error}")
            }
            Self::Dominance(error) => write!(formatter, "object SSA dominance failed: {error}"),
            Self::MissingDefinition(position) => {
                write!(formatter, "missing SSA definition at {position:?}")
            }
            Self::MissingHandler(block) => write!(formatter, "missing constructor handler {block}"),
            Self::MalformedHandlerPhi(block) => {
                write!(
                    formatter,
                    "constructor handler {block} has malformed Phi inputs"
                )
            }
            Self::MissingBlock(block) => write!(formatter, "missing object SSA block {block}"),
            Self::MissingPhiDefinition(block) => {
                write!(formatter, "missing object Phi definition in {block}")
            }
            Self::AmbiguousObjectValue(block) => {
                write!(formatter, "object value reaching {block} is ambiguous")
            }
            Self::UninitializedUse { position, argument } => write!(
                formatter,
                "object use {argument} at {position:?} is not reached by an initialized value"
            ),
            Self::RepeatedInitialization(position) => {
                write!(
                    formatter,
                    "object is initialized more than once at {position:?}"
                )
            }
        }
    }
}

impl std::error::Error for ConstructorRecoveryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Ssa(source) => Some(source),
            Self::Initialization(source) => Some(source),
            Self::InstructionTree(source) => Some(source),
            Self::Dominance(source) => Some(source),
            Self::MissingDefinition(_)
            | Self::MissingHandler(_)
            | Self::MalformedHandlerPhi(_)
            | Self::MissingBlock(_)
            | Self::MissingPhiDefinition(_)
            | Self::AmbiguousObjectValue(_)
            | Self::UninitializedUse { .. }
            | Self::RepeatedInitialization(_) => None,
        }
    }
}

impl From<crate::ir::InstructionTreeError> for ConstructorRecoveryError {
    fn from(source: crate::ir::InstructionTreeError) -> Self {
        Self::InstructionTree(source)
    }
}

pub struct RecoverConstructors<'a> {
    hierarchy: &'a dyn TypeHierarchy,
}

impl<'a> RecoverConstructors<'a> {
    pub fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self { hierarchy }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ArgumentSite {
    position: InsnPosition,
    argument: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PhiUse {
    site: ArgumentSite,
    predecessor: BlockId,
    target: BlockId,
    kind: EdgeKind,
}

struct ObjectValuePlan {
    aliases: BTreeSet<SsaVar>,
    removals: BTreeSet<InsnPosition>,
    constructors: BTreeMap<InsnPosition, (SsaVar, ArgType)>,
    replacements: BTreeMap<ArgumentSite, SsaVar>,
    phis: BTreeMap<BlockId, InsnNode>,
}

struct SyntheticVersions {
    next: BTreeMap<u32, u32>,
}

impl SyntheticVersions {
    fn new(values: &SsaValueGraph) -> Self {
        let mut next = BTreeMap::<u32, u32>::new();
        for value in values.values() {
            next.entry(value.variable.reg_num)
                .and_modify(|version| {
                    *version = (*version).max(value.variable.version.saturating_add(1))
                })
                .or_insert(value.variable.version.saturating_add(1));
        }
        Self { next }
    }

    fn allocate(&mut self, register: u32) -> SsaVar {
        let version = self.next.entry(register).or_insert(0);
        let value = SsaVar::new(register, *version);
        *version = version.saturating_add(1);
        value
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FlowValue {
    Unknown,
    Absent,
    Value(SsaVar),
    Conflict,
}

impl FlowValue {
    fn merge(self, incoming: Self) -> Self {
        match (self, incoming) {
            (Self::Unknown, value) | (value, Self::Unknown) => value,
            (left, right) if left == right => left,
            _ => Self::Conflict,
        }
    }

    fn value(self) -> Option<SsaVar> {
        match self {
            Self::Value(value) => Some(value),
            _ => None,
        }
    }
}

struct ObjectValueSsa<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    initialization: &'a ObjectInitialization,
    dominators: DominatorTree,
    frontier: DominanceFrontier,
}

impl<'a> ObjectValueSsa<'a> {
    fn analyze(
        cfg: &'a CFG,
        values: &'a SsaValueGraph,
        initialization: &'a ObjectInitialization,
        versions: &mut SyntheticVersions,
    ) -> Result<ObjectValuePlan, ConstructorRecoveryError> {
        let dominators =
            DominatorTree::compute(cfg).map_err(ConstructorRecoveryError::Dominance)?;
        let frontier = DominanceFrontier::compute(cfg, &dominators)
            .map_err(ConstructorRecoveryError::Dominance)?;
        Self {
            cfg,
            values,
            initialization,
            dominators,
            frontier,
        }
        .build(versions)
    }

    fn build(
        &self,
        versions: &mut SyntheticVersions,
    ) -> Result<ObjectValuePlan, ConstructorRecoveryError> {
        self.verify_constructor_order()?;
        let removals = self.removals()?;
        let (instruction_uses, phi_uses) = self.uses(&removals)?;
        let live_in = self.live_in(&instruction_uses, &phi_uses);
        let phi_blocks = self.place_phis(&live_in);
        let register = self.initialization.value.reg_num;
        let mut constructors = BTreeMap::new();
        for position in &self.initialization.constructors {
            constructors.insert(
                *position,
                (versions.allocate(register), self.initialization.ty.clone()),
            );
        }
        let phi_values = phi_blocks
            .iter()
            .copied()
            .map(|block| (block, versions.allocate(register)))
            .collect::<BTreeMap<_, _>>();
        let (inputs, edges) = self.reaching_values(&constructors, &phi_values)?;
        let mut replacements = BTreeMap::new();
        for use_site in &instruction_uses {
            let value = self
                .value_before(use_site.position, &inputs, &constructors)?
                .value()
                .ok_or(ConstructorRecoveryError::UninitializedUse {
                    position: use_site.position,
                    argument: use_site.argument,
                })?;
            replacements.insert(*use_site, value);
        }
        for use_site in &phi_uses {
            let value = edges
                .get(&(use_site.predecessor, use_site.target, use_site.kind))
                .copied()
                .unwrap_or(FlowValue::Unknown)
                .value()
                .ok_or(ConstructorRecoveryError::UninitializedUse {
                    position: use_site.site.position,
                    argument: use_site.site.argument,
                })?;
            replacements.insert(use_site.site, value);
        }
        for (position, (value, _)) in &constructors {
            replacements.insert(
                ArgumentSite {
                    position: *position,
                    argument: 0,
                },
                *value,
            );
        }

        let mut phis = BTreeMap::new();
        for (block, value) in phi_values {
            let incoming = self.cfg.incoming_edges(block);
            let mut phi = InsnNode::new(InsnType::Phi, incoming.len());
            phi.set_result(Self::register(value, &self.initialization.ty));
            phi.payload.phi_edges = incoming.clone();
            for (predecessor, kind) in incoming {
                let argument = edges
                    .get(&(predecessor, block, kind))
                    .copied()
                    .unwrap_or(FlowValue::Unknown)
                    .value()
                    .ok_or(ConstructorRecoveryError::MissingPhiDefinition(block))?;
                phi.add_arg(InsnArg::Reg(Self::register(
                    argument,
                    &self.initialization.ty,
                )));
            }
            phis.insert(block, phi);
        }

        Ok(ObjectValuePlan {
            aliases: self.initialization.aliases.clone(),
            removals,
            constructors,
            replacements,
            phis,
        })
    }

    fn verify_constructor_order(&self) -> Result<(), ConstructorRecoveryError> {
        for (index, left) in self.initialization.constructors.iter().enumerate() {
            for right in self.initialization.constructors.iter().skip(index + 1) {
                let ordered = if left.block == right.block {
                    true
                } else {
                    self.dominators.dominates(left.block, right.block)
                        || self.dominators.dominates(right.block, left.block)
                };
                if ordered {
                    return Err(ConstructorRecoveryError::RepeatedInitialization(*right));
                }
            }
        }
        Ok(())
    }

    fn removals(&self) -> Result<BTreeSet<InsnPosition>, ConstructorRecoveryError> {
        let mut removals = BTreeSet::from([self.initialization.allocation]);
        for alias in &self.initialization.aliases {
            let Some(definition) = self.values.value(*alias).and_then(|value| value.definition)
            else {
                continue;
            };
            let instruction = self
                .cfg
                .block(definition.block)
                .and_then(|block| block.insns.get(definition.index))
                .ok_or(ConstructorRecoveryError::MissingDefinition(definition))?;
            if matches!(instruction.insn_type, InsnType::Move | InsnType::Phi) {
                removals.insert(definition);
            }
        }
        Ok(removals)
    }

    fn uses(
        &self,
        removals: &BTreeSet<InsnPosition>,
    ) -> Result<(BTreeSet<ArgumentSite>, BTreeSet<PhiUse>), ConstructorRecoveryError> {
        let constructors = self
            .initialization
            .constructors
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let mut instruction_uses = BTreeSet::new();
        for alias in &self.initialization.aliases {
            let Some(value) = self.values.value(*alias) else {
                continue;
            };
            for usage in &value.uses {
                let position = usage.instruction;
                if self
                    .cfg
                    .block(position.block)
                    .and_then(|block| block.insns.get(position.index))
                    .is_none()
                {
                    continue;
                }
                if removals.contains(&position)
                    || (constructors.contains(&position) && usage.argument == 0)
                {
                    continue;
                }
                instruction_uses.insert(ArgumentSite {
                    position,
                    argument: usage.argument,
                });
            }
        }

        let mut phi_uses = BTreeSet::new();
        for phi in self.values.phis() {
            if self.initialization.aliases.contains(&phi.result) {
                continue;
            }
            let position = self
                .values
                .value(phi.result)
                .and_then(|value| value.definition)
                .ok_or(ConstructorRecoveryError::MissingPhiDefinition(phi.block))?;
            for (argument, input) in phi.inputs.iter().enumerate() {
                if self.initialization.aliases.contains(&input.value) {
                    phi_uses.insert(PhiUse {
                        site: ArgumentSite { position, argument },
                        predecessor: input.predecessor,
                        target: phi.block,
                        kind: input.edge_kind,
                    });
                }
            }
        }
        Ok((instruction_uses, phi_uses))
    }

    fn live_in(
        &self,
        instruction_uses: &BTreeSet<ArgumentSite>,
        phi_uses: &BTreeSet<PhiUse>,
    ) -> BTreeSet<BlockId> {
        let definitions = self
            .initialization
            .constructors
            .iter()
            .map(|position| position.block)
            .collect::<BTreeSet<_>>();
        let mut pending = instruction_uses
            .iter()
            .map(|usage| usage.position.block)
            .chain(phi_uses.iter().map(|usage| usage.predecessor))
            .collect::<VecDeque<_>>();
        let mut live_in = BTreeSet::new();
        while let Some(block) = pending.pop_front() {
            if definitions.contains(&block) || !live_in.insert(block) {
                continue;
            }
            pending.extend(
                self.cfg
                    .incoming_edges(block)
                    .into_iter()
                    .map(|(predecessor, _)| predecessor),
            );
        }
        live_in
    }

    fn place_phis(&self, live_in: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut pending = self
            .initialization
            .constructors
            .iter()
            .map(|position| position.block)
            .collect::<VecDeque<_>>();
        let mut processed = BTreeSet::new();
        let mut phis = BTreeSet::new();
        while let Some(block) = pending.pop_front() {
            if !processed.insert(block) {
                continue;
            }
            for boundary in self.frontier.frontier(block) {
                if live_in.contains(&boundary) && phis.insert(boundary) {
                    pending.push_back(boundary);
                }
            }
        }
        phis
    }

    fn reaching_values(
        &self,
        constructors: &BTreeMap<InsnPosition, (SsaVar, ArgType)>,
        phis: &BTreeMap<BlockId, SsaVar>,
    ) -> Result<
        (
            BTreeMap<BlockId, FlowValue>,
            BTreeMap<(BlockId, BlockId, EdgeKind), FlowValue>,
        ),
        ConstructorRecoveryError,
    > {
        let mut inputs = BTreeMap::from([(self.cfg.entry, FlowValue::Absent)]);
        inputs.extend(
            phis.iter()
                .map(|(block, value)| (*block, FlowValue::Value(*value))),
        );
        let mut edges = BTreeMap::new();
        loop {
            let mut changed = false;
            for block in self.cfg.block_ids() {
                let input = if let Some(value) = phis.get(&block) {
                    FlowValue::Value(*value)
                } else if block == self.cfg.entry {
                    FlowValue::Absent
                } else {
                    self.cfg.incoming_edges(block).into_iter().fold(
                        FlowValue::Unknown,
                        |state, (predecessor, kind)| {
                            state.merge(
                                edges
                                    .get(&(predecessor, block, kind))
                                    .copied()
                                    .unwrap_or(FlowValue::Unknown),
                            )
                        },
                    )
                };
                if input == FlowValue::Unknown {
                    continue;
                }
                if inputs.insert(block, input) != Some(input) {
                    changed = true;
                }
                let (normal, exceptional) = self.transfer(block, input, constructors)?;
                for (successor, kind) in self.cfg.successors_with_kind(block) {
                    let output = if *kind == EdgeKind::Exception {
                        exceptional
                    } else {
                        normal
                    };
                    let key = (block, *successor, *kind);
                    if edges.insert(key, output) != Some(output) {
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Ok((inputs, edges))
    }

    fn transfer(
        &self,
        block: BlockId,
        input: FlowValue,
        constructors: &BTreeMap<InsnPosition, (SsaVar, ArgType)>,
    ) -> Result<(FlowValue, FlowValue), ConstructorRecoveryError> {
        let body = self
            .cfg
            .block(block)
            .ok_or(ConstructorRecoveryError::MissingBlock(block))?;
        let mut state = input;
        let mut exceptional = input;
        for (index, instruction) in body.insns.iter().enumerate() {
            let position = InsnPosition { block, index };
            let before = state;
            state = self.advance(position, state, constructors);
            if instruction.can_throw() {
                exceptional = before;
            }
        }
        Ok((state, exceptional))
    }

    fn value_before(
        &self,
        position: InsnPosition,
        inputs: &BTreeMap<BlockId, FlowValue>,
        constructors: &BTreeMap<InsnPosition, (SsaVar, ArgType)>,
    ) -> Result<FlowValue, ConstructorRecoveryError> {
        let body = self
            .cfg
            .block(position.block)
            .ok_or(ConstructorRecoveryError::MissingBlock(position.block))?;
        let mut state = inputs
            .get(&position.block)
            .copied()
            .unwrap_or(FlowValue::Unknown);
        for index in 0..position.index.min(body.insns.len()) {
            state = self.advance(
                InsnPosition {
                    block: position.block,
                    index,
                },
                state,
                constructors,
            );
        }
        if state == FlowValue::Conflict {
            return Err(ConstructorRecoveryError::AmbiguousObjectValue(
                position.block,
            ));
        }
        Ok(state)
    }

    fn advance(
        &self,
        position: InsnPosition,
        mut state: FlowValue,
        constructors: &BTreeMap<InsnPosition, (SsaVar, ArgType)>,
    ) -> FlowValue {
        if position == self.initialization.allocation {
            state = FlowValue::Absent;
        }
        if let Some((value, _)) = constructors.get(&position) {
            state = match state {
                FlowValue::Absent => FlowValue::Value(*value),
                FlowValue::Unknown => FlowValue::Unknown,
                FlowValue::Value(_) | FlowValue::Conflict => FlowValue::Conflict,
            };
        }
        state
    }

    fn register(value: SsaVar, ty: &ArgType) -> RegisterArg {
        let mut register = RegisterArg::new(value.reg_num, ty.clone());
        register.ssa_version = Some(value.version);
        register
    }
}

impl Pass for RecoverConstructors<'_> {
    type Error = ConstructorRecoveryError;

    fn name(&self) -> &'static str {
        "recover_constructors"
    }

    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error> {
        let values = SsaValueGraph::build(cfg).map_err(ConstructorRecoveryError::Ssa)?;
        let facts = ObjectInitializations::analyze(cfg, &values, self.hierarchy)
            .map_err(ConstructorRecoveryError::Initialization)?;
        if facts.entries().is_empty() && facts.discarded_allocations().is_empty() {
            return Ok(PassResult::Unchanged);
        }

        let mut replacements = BTreeMap::<SsaVar, SsaVar>::new();
        let mut removals = facts.discarded_allocations().clone();
        let mut constructors = BTreeMap::new();
        let mut exceptional_merges = Vec::new();
        let mut versions = SyntheticVersions::new(&values);
        let mut object_plans = Vec::new();
        for initialization in facts.entries() {
            if let [constructor] = initialization.constructors.as_slice() {
                replacements.extend(
                    initialization
                        .aliases
                        .iter()
                        .copied()
                        .map(|alias| (alias, initialization.value)),
                );
                removals.insert(initialization.allocation);
                for alias in &initialization.aliases {
                    if let Some(definition) =
                        values.value(*alias).and_then(|value| value.definition)
                    {
                        let instruction = cfg
                            .block(definition.block)
                            .and_then(|block| block.insns.get(definition.index))
                            .ok_or(ConstructorRecoveryError::MissingDefinition(definition))?;
                        if matches!(instruction.insn_type, InsnType::Move | InsnType::Phi) {
                            removals.insert(definition);
                        }
                    }
                }
                constructors.insert(
                    *constructor,
                    (initialization.value, initialization.ty.clone()),
                );
            } else {
                let plan = ObjectValueSsa::analyze(cfg, &values, initialization, &mut versions)?;
                removals.extend(plan.removals.iter().copied());
                constructors.extend(
                    plan.constructors
                        .iter()
                        .map(|(position, value)| (*position, (value.0, value.1.clone()))),
                );
                object_plans.push(plan);
            }
            exceptional_merges.push(ExceptionalAllocationMerge {
                allocation: initialization.allocation.block,
                handlers: initialization.allocation_exception_handlers.clone(),
            });
        }

        for (&block_id, block) in &mut cfg.blocks {
            let mut rewriter = ConstructorRewriter::new(&replacements);
            let original = std::mem::take(&mut block.insns);
            let mut rewritten = Vec::with_capacity(original.len());
            for (index, mut instruction) in original.into_iter().enumerate() {
                let position = InsnPosition {
                    block: block_id,
                    index,
                };
                if removals.contains(&position) {
                    continue;
                }
                InstructionTree::transform_args(&mut instruction, &mut rewriter)?;
                for (argument, value) in instruction.args.iter_mut().enumerate() {
                    let site = ArgumentSite { position, argument };
                    for plan in &object_plans {
                        let Some(replacement) = plan.replacements.get(&site).copied() else {
                            continue;
                        };
                        let mut rewriter = ObjectArgumentRewriter {
                            aliases: &plan.aliases,
                            replacement,
                        };
                        *value = InstructionTree::transform_arg(value.clone(), &mut rewriter)?;
                    }
                }
                if let Some(target) = &mut instruction.payload.compound_target {
                    let site = ArgumentSite {
                        position,
                        argument: instruction.args.len(),
                    };
                    for plan in &object_plans {
                        let Some(replacement) = plan.replacements.get(&site).copied() else {
                            continue;
                        };
                        let mut rewriter = ObjectArgumentRewriter {
                            aliases: &plan.aliases,
                            replacement,
                        };
                        *target = InstructionTree::transform_arg(target.clone(), &mut rewriter)?;
                    }
                }
                if let Some((value, ty)) = constructors.get(&position) {
                    let mut result = RegisterArg::new(value.reg_num, ty.clone());
                    result.ssa_version = Some(value.version);
                    instruction.insn_type = InsnType::Constructor;
                    instruction.result = Some(result);
                    instruction.payload.class_type = Some(ty.clone());
                }
                rewritten.push(instruction);
            }
            block.insns = rewritten;
        }
        let mut phis = BTreeMap::<BlockId, Vec<InsnNode>>::new();
        for plan in object_plans {
            for (block, phi) in plan.phis {
                phis.entry(block).or_default().push(phi);
            }
        }
        for (block, mut inserted) in phis {
            inserted.sort_by_key(|phi| {
                phi.result
                    .as_ref()
                    .and_then(SsaVar::from_reg)
                    .unwrap_or(SsaVar::new(u32::MAX, u32::MAX))
            });
            let body = cfg
                .block_mut(block)
                .ok_or(ConstructorRecoveryError::MissingBlock(block))?;
            inserted.extend(std::mem::take(&mut body.insns));
            body.insns = inserted;
        }
        for merge in exceptional_merges {
            merge.apply(cfg)?;
        }
        Ok(PassResult::Changed)
    }
}

struct ExceptionalAllocationMerge {
    allocation: crate::ir::BlockId,
    handlers: Vec<crate::ir::BlockId>,
}

impl ExceptionalAllocationMerge {
    fn apply(self, cfg: &mut CFG) -> Result<(), ConstructorRecoveryError> {
        for handler in self.handlers {
            cfg.remove_edge(self.allocation, handler);
            let block = cfg
                .block_mut(handler)
                .ok_or(ConstructorRecoveryError::MissingHandler(handler))?;
            for phi in block
                .insns
                .iter_mut()
                .filter(|instruction| instruction.insn_type == InsnType::Phi)
            {
                if phi.args.len() != phi.payload.phi_edges.len() {
                    return Err(ConstructorRecoveryError::MalformedHandlerPhi(handler));
                }
                let mut arguments = std::mem::take(&mut phi.args).into_iter();
                let mut edges = std::mem::take(&mut phi.payload.phi_edges).into_iter();
                while let (Some(argument), Some(edge)) = (arguments.next(), edges.next()) {
                    if edge != (self.allocation, crate::ir::EdgeKind::Exception) {
                        phi.args.push(argument);
                        phi.payload.phi_edges.push(edge);
                    }
                }
            }
        }
        Ok(())
    }
}

struct ConstructorRewriter<'a> {
    replacements: &'a BTreeMap<SsaVar, SsaVar>,
}

impl<'a> ConstructorRewriter<'a> {
    fn new(replacements: &'a BTreeMap<SsaVar, SsaVar>) -> Self {
        Self { replacements }
    }
}

impl InstructionTransform for ConstructorRewriter<'_> {
    fn transform_register(&mut self, mut register: RegisterArg) -> InsnArg {
        if let Some(replacement) = SsaVar::from_reg(&register)
            .and_then(|value| self.replacements.get(&value))
            .copied()
        {
            replacement.apply_to(&mut register);
        }
        InsnArg::Reg(register)
    }
}

struct ObjectArgumentRewriter<'a> {
    aliases: &'a BTreeSet<SsaVar>,
    replacement: SsaVar,
}

impl InstructionTransform for ObjectArgumentRewriter<'_> {
    fn transform_register(&mut self, mut register: RegisterArg) -> InsnArg {
        if SsaVar::from_reg(&register).is_some_and(|value| self.aliases.contains(&value)) {
            self.replacement.apply_to(&mut register);
        }
        InsnArg::Reg(register)
    }
}
