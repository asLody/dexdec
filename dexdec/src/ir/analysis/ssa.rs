//! Canonical SSA value graph and source-variable congruence classes.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    ArgType, BlockId, InsnArg, InsnNode, InsnType, InstructionTransform, InstructionTree,
    InstructionVisitor, RegisterArg, CFG,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SsaVar {
    pub reg_num: u32,
    pub version: u32,
}

impl SsaVar {
    pub fn new(reg_num: u32, version: u32) -> Self {
        Self { reg_num, version }
    }

    pub fn from_reg(register: &RegisterArg) -> Option<Self> {
        Some(Self::new(register.reg_num, register.ssa_version?))
    }

    pub fn apply_to(self, register: &mut RegisterArg) {
        register.reg_num = self.reg_num;
        register.ssa_version = Some(self.version);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InsnPosition {
    pub block: BlockId,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UsePosition {
    pub instruction: InsnPosition,
    pub argument: usize,
    phi: Option<SsaVar>,
}

impl UsePosition {
    pub(super) fn phi(instruction: InsnPosition, argument: usize, result: SsaVar) -> Self {
        Self {
            instruction,
            argument,
            phi: Some(result),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum SsaUseSite<'a> {
    Instruction(&'a InsnNode),
    Phi(&'a PhiMerge),
}

#[derive(Debug, Clone)]
pub struct SsaValue {
    pub variable: SsaVar,
    pub definition: Option<InsnPosition>,
    pub uses: Vec<UsePosition>,
    pub observed_types: BTreeSet<ArgType>,
}

impl SsaValue {
    fn new(variable: SsaVar) -> Self {
        Self {
            variable,
            definition: None,
            uses: Vec::new(),
            observed_types: BTreeSet::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PhiInput {
    pub predecessor: BlockId,
    pub edge_kind: crate::ir::EdgeKind,
    pub value: SsaVar,
}

#[derive(Debug, Clone)]
pub struct PhiMerge {
    pub block: BlockId,
    pub instruction: crate::ir::InstructionId,
    pub result: SsaVar,
    pub inputs: Vec<PhiInput>,
}

#[derive(Debug, Clone, Copy)]
pub struct ValueCopy {
    pub result: SsaVar,
    pub source: SsaVar,
}

#[derive(Debug, Clone, Default)]
pub struct SsaValueGraph {
    values: BTreeMap<SsaVar, SsaValue>,
    phis: Vec<PhiMerge>,
    copies: Vec<ValueCopy>,
}

#[derive(Debug, Clone)]
pub enum SsaInvariantError {
    DefinitionWithoutIdentity(InsnPosition),
    MultipleDefinitions {
        value: SsaVar,
        first: InsnPosition,
        second: InsnPosition,
    },
    UseWithoutIdentity(InsnPosition),
    PhiWithoutResult(BlockId),
    PhiArity {
        block: BlockId,
        values: usize,
        edges: usize,
    },
    InvalidPhiInput {
        predecessor: BlockId,
        block: BlockId,
    },
    MissingPhiPredecessor(BlockId),
    PhiTopology {
        block: BlockId,
        actual: Vec<(BlockId, crate::ir::EdgeKind)>,
        expected: Vec<(BlockId, crate::ir::EdgeKind)>,
    },
    Dominance(super::DominanceError),
    UndefinedValue(SsaVar),
    NonDominatingDefinition {
        value: SsaVar,
        definition: InsnPosition,
        usage: InsnPosition,
    },
}

impl std::fmt::Display for SsaInvariantError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DefinitionWithoutIdentity(position) => {
                write!(formatter, "definition without SSA identity at {position:?}")
            }
            Self::MultipleDefinitions {
                value,
                first,
                second,
            } => write!(
                formatter,
                "{value:?} is defined at both {first:?} and {second:?}"
            ),
            Self::UseWithoutIdentity(position) => {
                write!(formatter, "use without SSA identity at {position:?}")
            }
            Self::PhiWithoutResult(block) => write!(formatter, "Phi without result in {block}"),
            Self::PhiArity {
                block,
                values,
                edges,
            } => write!(
                formatter,
                "Phi in {block} has {values} values for {edges} edges"
            ),
            Self::InvalidPhiInput { predecessor, block } => write!(
                formatter,
                "unresolved Phi input on edge {predecessor} -> {block}"
            ),
            Self::MissingPhiPredecessor(block) => {
                write!(formatter, "Phi predecessor block {block} is missing")
            }
            Self::PhiTopology {
                block,
                actual,
                expected,
            } => write!(
                formatter,
                "Phi predecessors in {block} are {actual:?}, expected {expected:?}"
            ),
            Self::Dominance(error) => error.fmt(formatter),
            Self::UndefinedValue(value) => {
                write!(formatter, "{value:?} is used without a definition")
            }
            Self::NonDominatingDefinition {
                value,
                definition,
                usage,
            } => write!(
                formatter,
                "definition of {value:?} at {definition:?} does not dominate use at {usage:?}"
            ),
        }
    }
}

impl std::error::Error for SsaInvariantError {}

impl SsaValueGraph {
    pub fn build(cfg: &CFG) -> Result<Self, SsaInvariantError> {
        let mut graph = Self::default();
        for (&block, body) in &cfg.blocks {
            for (index, instruction) in body.insns.iter().enumerate() {
                let position = InsnPosition { block, index };
                if let Some(result) = &instruction.result {
                    let variable = SsaVar::from_reg(result)
                        .ok_or(SsaInvariantError::DefinitionWithoutIdentity(position))?;
                    let value = graph.value_mut(variable);
                    if let Some(first) = value.definition.replace(position) {
                        return Err(SsaInvariantError::MultipleDefinitions {
                            value: variable,
                            first,
                            second: position,
                        });
                    }
                    value.observed_types.insert(result.ty.clone());
                }
                let arguments: &[InsnArg] = if instruction.insn_type == InsnType::Phi {
                    &[]
                } else if instruction.insn_type == InsnType::Constructor {
                    instruction.args.get(1..).unwrap_or_default()
                } else {
                    &instruction.args
                };
                for (argument, value) in arguments.iter().enumerate() {
                    graph.collect_use(
                        value,
                        UsePosition {
                            instruction: position,
                            argument,
                            phi: None,
                        },
                    )?;
                }
                if let Some(target) = &instruction.payload.compound_target {
                    graph.collect_use(
                        target,
                        UsePosition {
                            instruction: position,
                            argument: instruction.args.len(),
                            phi: None,
                        },
                    )?;
                }
                if instruction.insn_type == InsnType::Phi {
                    graph.collect_phi(cfg, block, instruction)?;
                } else if instruction.insn_type == InsnType::Move {
                    if let (Some(result), Some(source)) = (
                        instruction.result.as_ref().and_then(SsaVar::from_reg),
                        instruction
                            .args
                            .first()
                            .and_then(InsnArg::as_register)
                            .and_then(SsaVar::from_reg),
                    ) {
                        graph.copies.push(ValueCopy { result, source });
                    }
                }
            }
        }
        graph.validate_phi_edges(cfg)?;
        graph.validate_dominance(cfg)?;
        Ok(graph)
    }

    pub fn values(&self) -> impl Iterator<Item = &SsaValue> {
        self.values.values()
    }

    pub fn value(&self, variable: SsaVar) -> Option<&SsaValue> {
        self.values.get(&variable)
    }

    pub fn use_site<'a>(
        &'a self,
        cfg: &'a CFG,
        value: SsaVar,
        usage: UsePosition,
    ) -> Option<SsaUseSite<'a>> {
        if let Some(result) = usage.phi {
            return self.phis.iter().find_map(|phi| {
                let input = phi.inputs.get(usage.argument)?;
                (phi.result == result
                    && input.value == value
                    && input.predecessor == usage.instruction.block)
                    .then_some(SsaUseSite::Phi(phi))
            });
        }
        cfg.block(usage.instruction.block)
            .and_then(|block| block.insns.get(usage.instruction.index))
            .map(SsaUseSite::Instruction)
    }

    pub fn phis(&self) -> &[PhiMerge] {
        &self.phis
    }

    pub fn copies(&self) -> &[ValueCopy] {
        &self.copies
    }

    pub fn copy_classes(&self) -> SsaClasses {
        let mut classes = SsaClasses::new(self.values.keys().copied());
        for copy in &self.copies {
            classes.union(copy.result, copy.source);
        }
        classes
    }

    fn value_mut(&mut self, variable: SsaVar) -> &mut SsaValue {
        self.values
            .entry(variable)
            .or_insert_with(|| SsaValue::new(variable))
    }

    fn collect_use(
        &mut self,
        argument: &InsnArg,
        position: UsePosition,
    ) -> Result<(), SsaInvariantError> {
        let mut collector = UseCollector {
            graph: self,
            position,
            error: None,
        };
        InstructionTree::visit_arg(argument, &mut collector);
        collector.error.map_or(Ok(()), Err)
    }

    fn collect_phi(
        &mut self,
        cfg: &CFG,
        block: BlockId,
        instruction: &crate::ir::InsnNode,
    ) -> Result<(), SsaInvariantError> {
        let result = instruction
            .result
            .as_ref()
            .and_then(SsaVar::from_reg)
            .ok_or(SsaInvariantError::PhiWithoutResult(block))?;
        if instruction.payload.phi_edges.len() != instruction.args.len() {
            return Err(SsaInvariantError::PhiArity {
                block,
                values: instruction.args.len(),
                edges: instruction.payload.phi_edges.len(),
            });
        }
        let mut inputs = Vec::with_capacity(instruction.args.len());
        for (&(predecessor, edge_kind), argument) in
            instruction.payload.phi_edges.iter().zip(&instruction.args)
        {
            let value = argument
                .as_register()
                .and_then(SsaVar::from_reg)
                .ok_or(SsaInvariantError::InvalidPhiInput { predecessor, block })?;
            let predecessor_len = cfg
                .block(predecessor)
                .ok_or(SsaInvariantError::MissingPhiPredecessor(predecessor))?
                .insns
                .len();
            let position = UsePosition::phi(
                InsnPosition {
                    block: predecessor,
                    index: predecessor_len,
                },
                inputs.len(),
                result,
            );
            let input = self.value_mut(value);
            input.uses.push(position);
            if let Some(register) = argument.as_register() {
                input.observed_types.insert(register.ty.clone());
            }
            inputs.push(PhiInput {
                predecessor,
                edge_kind,
                value,
            });
        }
        self.phis.push(PhiMerge {
            block,
            instruction: instruction.id,
            result,
            inputs,
        });
        Ok(())
    }

    fn validate_phi_edges(&self, cfg: &CFG) -> Result<(), SsaInvariantError> {
        for phi in &self.phis {
            let expected = cfg.incoming_edges(phi.block);
            let actual = phi
                .inputs
                .iter()
                .map(|input| (input.predecessor, input.edge_kind))
                .collect::<Vec<_>>();
            if actual != expected {
                return Err(SsaInvariantError::PhiTopology {
                    block: phi.block,
                    actual,
                    expected,
                });
            }
        }
        Ok(())
    }

    fn validate_dominance(&self, cfg: &CFG) -> Result<(), SsaInvariantError> {
        let dominators =
            super::DominatorTree::compute(cfg).map_err(SsaInvariantError::Dominance)?;
        let first_input = cfg.registers.saturating_sub(cfg.ins);
        for value in self.values.values() {
            let Some(definition) = value.definition else {
                let method_input = value.variable.version == 0
                    && first_input <= value.variable.reg_num
                    && value.variable.reg_num < cfg.registers;
                if method_input {
                    continue;
                }
                return Err(SsaInvariantError::UndefinedValue(value.variable));
            };
            for usage in &value.uses {
                let dominated = if definition.block == usage.instruction.block {
                    definition.index < usage.instruction.index
                } else {
                    dominators.dominates(definition.block, usage.instruction.block)
                };
                if !dominated {
                    return Err(SsaInvariantError::NonDominatingDefinition {
                        value: value.variable,
                        definition,
                        usage: usage.instruction,
                    });
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct CodeVariables {
    classes: BTreeMap<SsaVar, u32>,
}

impl CodeVariables {
    pub(super) fn from_classes(mut classes: SsaClasses) -> Self {
        let mut roots = BTreeMap::new();
        let mut assignments = BTreeMap::new();
        for variable in classes.parents.keys().copied().collect::<Vec<_>>() {
            let root = classes.root(variable);
            let next = roots.len() as u32;
            let id = *roots.entry(root).or_insert(next);
            assignments.insert(variable, id);
        }
        Self {
            classes: assignments,
        }
    }

    pub fn annotate(&self, cfg: &mut CFG) -> Result<(), crate::ir::InstructionTreeError> {
        for block in cfg.blocks.values_mut() {
            for instruction in &mut block.insns {
                if let Some(result) = &mut instruction.result {
                    result.code_var = self.class_of(result);
                }
                InstructionTree::transform_args(
                    instruction,
                    &mut CodeVariableAnnotation { variables: self },
                )?;
            }
        }
        self.bind_inputs(cfg);
        Ok(())
    }

    pub(super) fn next_id(&self) -> u32 {
        self.classes
            .values()
            .copied()
            .max()
            .map_or(0, |variable| variable + 1)
    }

    pub(super) fn variable_of(&self, value: SsaVar) -> Option<u32> {
        self.classes.get(&value).copied()
    }

    pub(super) fn assignments(&self) -> impl Iterator<Item = (&SsaVar, &u32)> {
        self.classes.iter()
    }

    fn class_of(&self, register: &RegisterArg) -> Option<u32> {
        SsaVar::from_reg(register).and_then(|variable| self.variable_of(variable))
    }

    fn bind_inputs(&self, cfg: &mut CFG) {
        let mut register = cfg.registers.saturating_sub(cfg.ins);
        let this_variable = if !cfg.method().is_static() && register < cfg.registers {
            let variable = self.classes.get(&SsaVar::new(register, 0)).copied();
            register += 1;
            variable
        } else {
            None
        };
        let parameter_variables = cfg
            .method()
            .descriptor()
            .parameters
            .iter()
            .map(|parameter| {
                let value = self.classes.get(&SsaVar::new(register, 0)).copied();
                register += parameter_slots(parameter);
                value
            })
            .collect();
        cfg.set_source_variables(this_variable, parameter_variables);
    }
}

struct UseCollector<'a> {
    graph: &'a mut SsaValueGraph,
    position: UsePosition,
    error: Option<SsaInvariantError>,
}

impl InstructionVisitor for UseCollector<'_> {
    fn visit_register(&mut self, register: &RegisterArg) {
        if self.error.is_some() {
            return;
        }
        let Some(variable) = SsaVar::from_reg(register) else {
            self.error = Some(SsaInvariantError::UseWithoutIdentity(
                self.position.instruction,
            ));
            return;
        };
        let value = self.graph.value_mut(variable);
        value.uses.push(self.position);
        value.observed_types.insert(register.ty.clone());
    }
}

struct CodeVariableAnnotation<'a> {
    variables: &'a CodeVariables,
}

impl InstructionTransform for CodeVariableAnnotation<'_> {
    fn transform_register(&mut self, mut register: RegisterArg) -> InsnArg {
        register.code_var = self.variables.class_of(&register);
        InsnArg::Reg(register)
    }

    fn transform_result(&mut self, mut result: RegisterArg) -> RegisterArg {
        result.code_var = self.variables.class_of(&result);
        result
    }
}

#[derive(Debug, Clone)]
pub struct SsaClasses {
    parents: BTreeMap<SsaVar, SsaVar>,
}

impl Default for SsaClasses {
    fn default() -> Self {
        Self::new([])
    }
}

impl SsaClasses {
    pub fn new(values: impl IntoIterator<Item = SsaVar>) -> Self {
        Self {
            parents: values.into_iter().map(|value| (value, value)).collect(),
        }
    }

    pub fn root(&mut self, value: SsaVar) -> SsaVar {
        self.parents.entry(value).or_insert(value);
        let mut path = Vec::new();
        let mut current = value;
        loop {
            let parent = self.parents.get(&current).copied().unwrap_or(current);
            if parent == current {
                break;
            }
            path.push(current);
            current = parent;
        }
        for member in path {
            self.parents.insert(member, current);
        }
        current
    }

    pub fn union(&mut self, left: SsaVar, right: SsaVar) {
        let left = self.root(left);
        let right = self.root(right);
        if left == right {
            return;
        }
        let (root, child) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        self.parents.insert(child, root);
    }

    pub fn values(&self) -> Vec<SsaVar> {
        self.parents.keys().copied().collect()
    }

    pub fn groups(&mut self) -> BTreeMap<SsaVar, BTreeSet<SsaVar>> {
        let mut groups = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        for value in self.parents.keys().copied().collect::<Vec<_>>() {
            groups.entry(self.root(value)).or_default().insert(value);
        }
        groups
    }
}

fn parameter_slots(parameter: &ArgType) -> u32 {
    if parameter.is_wide() {
        2
    } else {
        1
    }
}
