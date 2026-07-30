//! Interference-aware allocation of SSA values to Kotlin source variables.
//!
//! SSA remains intact through region construction and sparse value recovery.
//! This analysis first assigns non-interfering values to source variables,
//! then lowers Phi edge copies into identified Semantic IR basic blocks.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::ir::{
    BlockId, InsnArg, InstructionTreeError, RegionGraph, RegisterArg, SemanticExpression,
    SemanticExpressionTransform, SemanticFoldError, SemanticFolder, SemanticInstructions,
    SemanticMethod, SemanticNode, SemanticOperation, SemanticVisitor, SourceSemantics,
    ValueSemantics, CFG,
};

use super::types::SourceTypeLattice;
use super::{
    CodeVariables, ControlContractions, NormalCopySite, SourceTypeEnvironment, SsaClasses,
    SsaTypeEnvironment, SsaUseSite, SsaValueGraph, SsaVar, TypeConstraintError,
};

mod edge_arguments;
mod interference;
mod lexical_exits;
mod loop_exit_copies;
mod phi;

use interference::{ClassInterference, InterferenceGraph, SsaLiveness};
use lexical_exits::LexicalExitLowering;
use phi::{
    ExceptionalCopyPlacement, PhiCopies, PhiLowering, PhiTypeAnalysis, RequiredPhiValues,
    RetainedSsaValues, StatementDefinitions,
};

pub struct SourceVariableAllocation {
    variables: CodeVariables,
    liveness: SsaLiveness,
    required_phis: BTreeSet<SsaVar>,
    statement_definitions: BTreeSet<SsaVar>,
    contractions: ControlContractions,
    phi_types: BTreeMap<SsaVar, crate::ir::ArgType>,
}

impl SourceVariableAllocation {
    pub fn analyze(
        cfg: &CFG,
        values: &SsaValueGraph,
        constants: &BTreeMap<SsaVar, InsnArg>,
        recovered_phis: &BTreeSet<SsaVar>,
        root: &SemanticNode,
        types: &SsaTypeEnvironment,
        hierarchy: &dyn super::TypeHierarchy,
        regions: &RegionGraph,
    ) -> Result<Self, SourceVariableError> {
        let contractions = ControlContractions::for_edge_arguments(cfg, regions);
        let required_phis = RequiredPhiValues::collect(
            cfg,
            values,
            root,
            constants,
            recovered_phis,
            &contractions,
        )?;
        let statement_definitions = StatementDefinitions::collect(root);
        let mut cleanup_values = regions
            .cleanup_value_bindings()
            .iter()
            .flat_map(|(handler, normal)| [*handler, *normal])
            .collect::<BTreeSet<_>>();
        let cleanup_phis = values
            .phis()
            .iter()
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let mut pending = cleanup_values.iter().copied().collect::<Vec<_>>();
        while let Some(value) = pending.pop() {
            let Some(phi) = cleanup_phis.get(&value) else {
                continue;
            };
            for input in &phi.inputs {
                if cleanup_values.insert(input.value) {
                    pending.push(input.value);
                }
            }
        }
        let mut retained = RetainedSsaValues::collect(root);
        retained.extend(required_phis.iter().copied());
        retained.extend(cleanup_values.iter().copied());
        let liveness = SsaLiveness::analyze(cfg, &retained)?;
        let edge_arguments =
            edge_arguments::ContractedEdgeArguments::new(cfg, values, constants, &contractions);
        let mut interference = InterferenceGraph::build(cfg, root, &liveness)?;
        interference.add_exceptional_edge_interference(cfg, &liveness, &edge_arguments)?;
        let classes = SsaClasses::new(
            values
                .values()
                .map(|value| value.variable)
                .chain(SourceInputs::of(cfg)),
        );
        let exception_types = ExceptionValueTypes::collect(root, hierarchy);
        let phi_types =
            PhiTypeAnalysis::solve(cfg, &required_phis, values, types, constants, hierarchy)?;
        let dominators =
            super::DominatorTree::compute(cfg).map_err(SourceVariableError::Dominance)?;
        let mut coalescer = SourceClassCoalescer::new(
            classes,
            interference,
            types,
            values,
            &exception_types,
            &phi_types,
            hierarchy,
        );
        let inputs = SourceInputs::of(cfg);
        if !cfg.method().is_static() {
            if let Some(this) = inputs.first().copied() {
                coalescer.fix(this);
            }
        }
        for input in inputs {
            coalescer.pin(input);
        }
        for (handler, normal) in regions.cleanup_value_bindings() {
            coalescer.coalesce_proven(*handler, *normal);
        }
        for phi in values
            .phis()
            .iter()
            .filter(|phi| cleanup_values.contains(&phi.result))
        {
            for input in &phi.inputs {
                coalescer.coalesce_proven(phi.result, input.value);
            }
        }
        let phis_by_result = values
            .phis()
            .iter()
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let mut coalescing_phis = required_phis
            .iter()
            .chain(recovered_phis)
            .copied()
            .collect::<BTreeSet<_>>();
        let mut pending_phis = coalescing_phis.iter().copied().collect::<Vec<_>>();
        while let Some(result) = pending_phis.pop() {
            let Some(phi) = phis_by_result.get(&result) else {
                continue;
            };
            for input in &phi.inputs {
                if phis_by_result.contains_key(&input.value) && coalescing_phis.insert(input.value)
                {
                    pending_phis.push(input.value);
                }
            }
        }
        for phi in values
            .phis()
            .iter()
            .filter(|phi| coalescing_phis.contains(&phi.result))
        {
            let acyclic = phi
                .inputs
                .iter()
                .filter(|input| !constants.contains_key(&input.value))
                .all(|input| !dominators.dominates(phi.block, input.predecessor));
            for input in &phi.inputs {
                if !constants.contains_key(&input.value) {
                    let phi_only = values.value(input.value).is_some_and(|value| {
                        value.uses.iter().all(|usage| {
                            matches!(
                                values.use_site(cfg, input.value, *usage),
                                Some(SsaUseSite::Phi(_))
                            )
                        })
                    });
                    coalescer.coalesce_phi(phi.result, input.value, acyclic, phi_only);
                }
            }
        }
        CanonicalCatchParameters::collect(cfg, regions).coalesce(&mut coalescer);
        for copy in values
            .copies()
            .iter()
            .filter(|copy| !constants.contains_key(&copy.source))
        {
            coalescer.coalesce_copy(copy.result, copy.source);
        }
        let variables = CodeVariables::from_classes(coalescer.finish());
        for value in retained {
            if variables.variable_of(value).is_none() {
                return Err(SourceVariableError::MissingCodeVariable(value));
            }
        }
        Ok(Self {
            variables,
            liveness,
            required_phis,
            statement_definitions,
            contractions,
            phi_types,
        })
    }

    fn annotate_cfg(&self, cfg: &mut CFG) -> Result<(), SourceVariableError> {
        self.variables
            .annotate(cfg)
            .map_err(SourceVariableError::InstructionTree)?;
        Ok(())
    }

    pub fn apply(
        &self,
        cfg: &mut CFG,
        mut method: SemanticMethod<ValueSemantics>,
        types: SsaTypeEnvironment,
        hierarchy: &dyn super::TypeHierarchy,
    ) -> Result<SemanticMethod<SourceSemantics>, SourceVariableError> {
        self.annotate_cfg(cfg)?;
        SourceAnnotation::new(&self.variables).apply(method.body_mut())?;
        let copies = PhiCopies::collect(
            cfg,
            &self.required_phis,
            &self.statement_definitions,
            method.state().values(),
            method.state().constants(),
            &self.phi_types,
            &self.contractions,
            method.state().regions(),
            hierarchy,
        )?;
        let copies = ExceptionalCopyPlacement::new(
            cfg,
            &self.variables,
            &self.liveness,
            &self.statement_definitions,
            method.body(),
            &self.contractions,
            method.state().regions(),
        )
        .verify(copies)?;
        let mut source_types = SourceTypeEnvironment::from_ssa(
            types,
            &self.variables,
            method.state().values(),
            method.state().constants(),
            hierarchy,
        )?;
        DeclaredInputTypes::apply(cfg, &mut source_types, hierarchy)?;
        let phi_lowering = PhiLowering::new(
            cfg,
            copies,
            self.variables.next_id(),
            &mut source_types,
            hierarchy,
            method.state().regions(),
        )?;
        let next_variable = phi_lowering.next_variable();
        phi_lowering.apply(method.body_mut())?;
        LexicalExitLowering::apply(method.body_mut(), next_variable, &mut source_types)?;
        ExceptionTypeBinding::apply(method.body(), &mut source_types, hierarchy)?;
        let (body, state) = method.into_parts();
        Ok(SemanticMethod::from_source(
            body,
            source_types,
            state.into_regions(),
        ))
    }
}

struct CanonicalCatchParameters {
    groups: Vec<Vec<SsaVar>>,
}

impl CanonicalCatchParameters {
    fn collect(cfg: &CFG, regions: &RegionGraph) -> Self {
        let mut groups = BTreeMap::<BlockId, Vec<SsaVar>>::new();
        for (&adapter, &canonical_entry) in regions.handler_adapters() {
            let values = cfg
                .block(adapter)
                .into_iter()
                .flat_map(|block| &block.insns)
                .filter(|instruction| instruction.insn_type == crate::ir::InsnType::MoveException)
                .filter_map(|instruction| instruction.result.as_ref())
                .filter_map(SsaVar::from_reg);
            groups.entry(canonical_entry).or_default().extend(values);
        }
        Self {
            groups: groups.into_values().collect(),
        }
    }

    fn coalesce(self, coalescer: &mut SourceClassCoalescer<'_>) {
        for group in self.groups {
            let Some((&representative, rest)) = group.split_first() else {
                continue;
            };
            for &value in rest {
                coalescer.coalesce_proven(representative, value);
            }
        }
    }
}

struct DeclaredInputTypes;

impl DeclaredInputTypes {
    fn apply(
        cfg: &CFG,
        types: &mut SourceTypeEnvironment,
        hierarchy: &dyn super::TypeHierarchy,
    ) -> Result<(), TypeConstraintError> {
        if let Some(variable) = cfg.this_code_variable() {
            types.bind_declared_variable(variable, cfg.method().owner().clone(), hierarchy)?;
        }
        for (variable, ty) in cfg
            .parameter_code_variables()
            .iter()
            .zip(&cfg.method().descriptor().parameters)
        {
            if let Some(variable) = variable {
                types.bind_declared_variable(*variable, ty.clone(), hierarchy)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum ExceptionDefinition {
    Null,
    Copy(u32),
    Other,
}

struct ExceptionTypeBinding<'a> {
    exception_types: ExceptionTypes<'a>,
    seeds: BTreeMap<u32, crate::ir::ArgType>,
    definitions: BTreeMap<u32, Vec<ExceptionDefinition>>,
}

impl<'a> ExceptionTypeBinding<'a> {
    fn apply(
        root: &SemanticNode,
        types: &'a mut SourceTypeEnvironment,
        hierarchy: &'a dyn super::TypeHierarchy,
    ) -> Result<(), TypeConstraintError> {
        let mut binding = Self {
            exception_types: ExceptionTypes::new(hierarchy),
            seeds: BTreeMap::new(),
            definitions: BTreeMap::new(),
        };
        binding.visit_node(root);
        for (variable, ty) in binding.solve() {
            types.bind_exception_type(variable, ty)?;
        }
        Ok(())
    }

    fn solve(&self) -> BTreeMap<u32, crate::ir::ArgType> {
        let mut inferred = self.seeds.clone();
        loop {
            let mut changed = false;
            for (&variable, definitions) in &self.definitions {
                if self.seeds.contains_key(&variable) {
                    continue;
                }
                let mut ty = None;
                let mut complete = true;
                for definition in definitions {
                    match definition {
                        ExceptionDefinition::Null => {}
                        ExceptionDefinition::Copy(source) if *source == variable => {}
                        ExceptionDefinition::Copy(source) => {
                            let Some(source_type) = inferred.get(source) else {
                                complete = false;
                                break;
                            };
                            ty = Some(match ty {
                                Some(current) => {
                                    self.exception_types.merge_pair(&current, source_type)
                                }
                                None => source_type.clone(),
                            });
                        }
                        ExceptionDefinition::Other => {
                            complete = false;
                            break;
                        }
                    }
                }
                let Some(ty) = complete.then_some(ty).flatten() else {
                    continue;
                };
                if inferred.get(&variable) != Some(&ty) {
                    inferred.insert(variable, ty);
                    changed = true;
                }
            }
            if !changed {
                return inferred;
            }
        }
    }

    fn record_definition(&mut self, result: &RegisterArg, value: &SemanticExpression) {
        let Some(variable) = result.code_var else {
            return;
        };
        self.definitions
            .entry(variable)
            .or_default()
            .push(Self::classify(value));
    }

    fn classify(mut value: &SemanticExpression) -> ExceptionDefinition {
        loop {
            match value {
                SemanticExpression::Literal(literal)
                    if literal.value == 0 && literal.ty.is_reference() =>
                {
                    return ExceptionDefinition::Null;
                }
                SemanticExpression::Register(register) => {
                    return register
                        .code_var
                        .map(ExceptionDefinition::Copy)
                        .unwrap_or(ExceptionDefinition::Other);
                }
                SemanticExpression::Operation(operation)
                    if operation.insn_type == crate::ir::InsnType::Move
                        && operation.operands().len() == 1 =>
                {
                    value = &operation.operands()[0];
                }
                SemanticExpression::Literal(_)
                | SemanticExpression::Operation(_)
                | SemanticExpression::Select { .. } => return ExceptionDefinition::Other,
            }
        }
    }
}

impl SemanticVisitor for ExceptionTypeBinding<'_> {
    fn enter_node(&mut self, node: &SemanticNode) {
        let SemanticNode::Try { catches, .. } = node else {
            return;
        };
        for catch in catches {
            let Some(variable) = catch
                .exception_value
                .as_ref()
                .and_then(|exception| exception.code_var)
            else {
                continue;
            };
            let ty = self.exception_types.merge(&catch.exception_types);
            self.seeds
                .entry(variable)
                .and_modify(|current| {
                    *current = self.exception_types.merge_pair(current, &ty);
                })
                .or_insert(ty);
        }
    }

    fn visit_statement(&mut self, statement: &crate::ir::SemanticStatement) {
        match &statement.kind {
            crate::ir::SemanticStatementKind::Definition { result, value, .. } => {
                self.record_definition(result, value);
            }
            crate::ir::SemanticStatementKind::Instruction(operation) => {
                let Some(result) = operation.result.as_ref() else {
                    return;
                };
                self.record_definition(
                    result,
                    &SemanticExpression::Operation(Box::new(operation.clone())),
                );
            }
        }
    }
}

struct ExceptionValueTypes;

impl ExceptionValueTypes {
    fn collect(
        root: &SemanticNode,
        hierarchy: &dyn super::TypeHierarchy,
    ) -> BTreeMap<SsaVar, crate::ir::ArgType> {
        struct Collector<'a> {
            types: ExceptionTypes<'a>,
            values: BTreeMap<SsaVar, crate::ir::ArgType>,
        }

        impl SemanticVisitor for Collector<'_> {
            fn enter_node(&mut self, node: &SemanticNode) {
                let SemanticNode::Try { catches, .. } = node else {
                    return;
                };
                for catch in catches {
                    let Some(value) = catch.exception_value.as_ref().and_then(SsaVar::from_reg)
                    else {
                        continue;
                    };
                    let ty = self.types.merge(&catch.exception_types);
                    self.values
                        .entry(value)
                        .and_modify(|existing| {
                            *existing = self.types.merge_pair(existing, &ty);
                        })
                        .or_insert(ty);
                }
            }
        }

        let mut collector = Collector {
            types: ExceptionTypes::new(hierarchy),
            values: BTreeMap::new(),
        };
        collector.visit_node(root);
        collector.values
    }
}

struct ExceptionTypes<'a> {
    lattice: SourceTypeLattice<'a>,
}

impl<'a> ExceptionTypes<'a> {
    fn new(hierarchy: &'a dyn super::TypeHierarchy) -> Self {
        Self {
            lattice: SourceTypeLattice::new(hierarchy),
        }
    }

    fn merge(&self, types: &[crate::ir::ArgType]) -> crate::ir::ArgType {
        types
            .iter()
            .cloned()
            .reduce(|left, right| self.merge_pair(&left, &right))
            .unwrap_or_else(crate::ir::ArgType::throwable)
    }

    fn merge_pair(
        &self,
        left: &crate::ir::ArgType,
        right: &crate::ir::ArgType,
    ) -> crate::ir::ArgType {
        self.lattice
            .join(left, right)
            .filter(|ty| ty != &crate::ir::ArgType::object("java/lang/Object"))
            .unwrap_or_else(crate::ir::ArgType::throwable)
    }
}

struct SourceClassCoalescer<'a> {
    classes: SsaClasses,
    interference: ClassInterference,
    class_types: BTreeMap<SsaVar, crate::ir::ArgType>,
    type_lattice: SourceTypeLattice<'a>,
    pinned: BTreeSet<SsaVar>,
    fixed: BTreeSet<SsaVar>,
}

impl<'a> SourceClassCoalescer<'a> {
    fn new(
        mut classes: SsaClasses,
        interference: InterferenceGraph,
        types: &SsaTypeEnvironment,
        values: &SsaValueGraph,
        exception_types: &BTreeMap<SsaVar, crate::ir::ArgType>,
        phi_types: &BTreeMap<SsaVar, crate::ir::ArgType>,
        hierarchy: &'a dyn super::TypeHierarchy,
    ) -> Self {
        let lattice = SourceTypeLattice::new(hierarchy);
        let mut class_types: BTreeMap<SsaVar, crate::ir::ArgType> = classes
            .values()
            .into_iter()
            .filter_map(|value| {
                types
                    .value_type(value)
                    .cloned()
                    .or_else(|| {
                        values
                            .value(value)
                            .and_then(|value| lattice.select_observed(&value.observed_types))
                    })
                    .map(|ty| (value, ty))
            })
            .collect();
        class_types.extend(
            exception_types
                .iter()
                .map(|(value, ty)| (*value, ty.clone())),
        );
        class_types.extend(phi_types.iter().map(|(value, ty)| (*value, ty.clone())));
        let interference = ClassInterference::new(interference, &mut classes);
        Self {
            classes,
            interference,
            class_types,
            type_lattice: lattice,
            pinned: BTreeSet::new(),
            fixed: BTreeSet::new(),
        }
    }

    fn pin(&mut self, value: SsaVar) {
        let root = self.classes.root(value);
        self.pinned.insert(root);
    }

    fn fix(&mut self, value: SsaVar) {
        let root = self.classes.root(value);
        self.fixed.insert(root);
    }

    fn coalesce_copy(&mut self, left: SsaVar, right: SsaVar) {
        self.coalesce(left, right, CoalescingPolicy::AllInterference);
    }

    fn coalesce_proven(&mut self, left: SsaVar, right: SsaVar) {
        self.coalesce(left, right, CoalescingPolicy::SemanticCongruence);
    }

    fn coalesce_phi(&mut self, left: SsaVar, right: SsaVar, acyclic: bool, phi_only: bool) {
        let policy = if acyclic {
            CoalescingPolicy::AcyclicPhi { phi_only }
        } else {
            CoalescingPolicy::AllInterference
        };
        self.coalesce(left, right, policy);
    }

    fn coalesce(&mut self, left: SsaVar, right: SsaVar, policy: CoalescingPolicy) {
        let left = self.classes.root(left);
        let right = self.classes.root(right);
        let merged_type = policy.merged_type(self, left, right);
        let decision = if left == right {
            CoalescingDecision::Identical
        } else if self.fixed.contains(&left) || self.fixed.contains(&right) {
            CoalescingDecision::Fixed
        } else if self.pinned.contains(&left) && self.pinned.contains(&right) {
            CoalescingDecision::Pinned
        } else if policy.interferes(&self.interference, left, right) {
            CoalescingDecision::Interference
        } else if merged_type.is_err() {
            CoalescingDecision::IncompatibleTypes
        } else {
            CoalescingDecision::Merge
        };
        if decision != CoalescingDecision::Merge {
            return;
        }
        self.classes.union(left, right);
        let root = self.classes.root(left);
        let absorbed = if root == left { right } else { left };
        self.class_types.remove(&left);
        self.class_types.remove(&right);
        if let Ok(Some(ty)) = merged_type {
            self.class_types.insert(root, ty);
        }
        if self.pinned.remove(&absorbed) {
            self.pinned.insert(root);
        }
        if self.fixed.remove(&absorbed) {
            self.fixed.insert(root);
        }
        self.interference.merge(root, absorbed);
    }

    fn merged_type(&self, left: SsaVar, right: SsaVar) -> Result<Option<crate::ir::ArgType>, ()> {
        match (self.class_types.get(&left), self.class_types.get(&right)) {
            (Some(left), Some(right)) => self.type_lattice.meet(left, right).map(Some).ok_or(()),
            (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty.clone())),
            (None, None) => Ok(None),
        }
    }

    fn finish(self) -> SsaClasses {
        self.classes
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CoalescingDecision {
    Identical,
    Fixed,
    Pinned,
    Interference,
    IncompatibleTypes,
    Merge,
}

#[derive(Debug, Clone, Copy)]
enum CoalescingPolicy {
    AllInterference,
    AcyclicPhi { phi_only: bool },
    SemanticCongruence,
}

impl CoalescingPolicy {
    fn interferes(self, graph: &ClassInterference, left: SsaVar, right: SsaVar) -> bool {
        match self {
            Self::AllInterference => graph.interferes(left, right),
            Self::AcyclicPhi { .. } => graph.hard_interferes(left, right),
            // Cleanup equivalence and its Phi closure describe one logical
            // source state across mutually exclusive normal/exceptional
            // domains. Physical exceptional liveness overlaps those domains
            // by construction and is not a valid conflict for this class.
            Self::SemanticCongruence => false,
        }
    }

    fn merged_type(
        self,
        coalescer: &SourceClassCoalescer<'_>,
        left: SsaVar,
        right: SsaVar,
    ) -> Result<Option<crate::ir::ArgType>, ()> {
        match self {
            Self::AllInterference | Self::SemanticCongruence => coalescer.merged_type(left, right),
            Self::AcyclicPhi { phi_only } => match (
                coalescer.class_types.get(&left),
                coalescer.class_types.get(&right),
            ) {
                (Some(left), Some(right)) if left == right => Ok(Some(left.clone())),
                (Some(left), Some(right)) if phi_only => {
                    coalescer.type_lattice.join(left, right).map(Some).ok_or(())
                }
                (Some(_), Some(_)) => Err(()),
                (Some(ty), None) | (None, Some(ty)) => Ok(Some(ty.clone())),
                (None, None) => Ok(None),
            },
        }
    }
}

struct SourceInputs;

impl SourceInputs {
    fn of(cfg: &CFG) -> Vec<SsaVar> {
        let mut register = cfg.registers.saturating_sub(cfg.ins);
        let mut inputs = Vec::new();
        if !cfg.method().is_static() && register < cfg.registers {
            inputs.push(SsaVar::new(register, 0));
            register += 1;
        }
        for parameter in &cfg.method().descriptor().parameters {
            if register < cfg.registers {
                inputs.push(SsaVar::new(register, 0));
            }
            register += if parameter.is_wide() { 2 } else { 1 };
        }
        inputs
    }
}

struct SourceAnnotation<'a> {
    variables: &'a CodeVariables,
}

impl<'a> SourceAnnotation<'a> {
    fn new(variables: &'a CodeVariables) -> Self {
        Self { variables }
    }

    fn apply(mut self, root: &mut SemanticNode) -> Result<(), SourceVariableError> {
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = self.fold_node(body)?;
        Ok(())
    }

    fn annotate_register(&self, register: &mut RegisterArg) {
        register.code_var =
            SsaVar::from_reg(register).and_then(|value| self.variables.variable_of(value));
    }

    fn is_identity_copy(instruction: &SemanticOperation) -> bool {
        if instruction.insn_type != crate::ir::InsnType::Move {
            return false;
        }
        let Some(destination) = instruction
            .result
            .as_ref()
            .and_then(|result| result.code_var)
        else {
            return false;
        };
        instruction
            .operands()
            .first()
            .and_then(SemanticExpression::as_register)
            .and_then(|source| source.code_var)
            == Some(destination)
    }
}

impl SemanticExpressionTransform for SourceAnnotation<'_> {
    fn transform_register(&mut self, mut register: RegisterArg) -> SemanticExpression {
        self.annotate_register(&mut register);
        SemanticExpression::Register(register)
    }

    fn transform_result(&mut self, mut result: RegisterArg) -> RegisterArg {
        self.annotate_register(&mut result);
        result
    }
}

impl SemanticFolder for SourceAnnotation<'_> {
    type Error = SourceVariableError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        SemanticInstructions::transform_node(&mut node, self)?;
        if let SemanticNode::BasicBlock(block) = &mut node {
            block.statements.retain(|statement| {
                statement
                    .instruction_ref()
                    .is_none_or(|instruction| !Self::is_identity_copy(instruction))
            });
        }
        Ok(node)
    }
}

#[derive(Debug)]
pub enum SourceVariableError {
    InstructionTree(InstructionTreeError),
    SemanticTransform(SemanticFoldError),
    Type(TypeConstraintError),
    Dominance(super::DominanceError),
    MissingPhiResult(BlockId),
    NonRegisterPhiInput {
        predecessor: BlockId,
        successor: BlockId,
    },
    UnsplitNormalEdge {
        predecessor: BlockId,
        successor: BlockId,
        targets: Vec<BlockId>,
    },
    MissingBlock(BlockId),
    MissingThrowSite(BlockId),
    MissingSemanticSite(&'static str),
    IncompleteSemanticFlow,
    MissingRegisterIdentity,
    MissingCodeVariable(SsaVar),
    LivenessMismatch(BlockId),
    ExceptionalCopyClobbersNormalValue {
        predecessor: BlockId,
        variable: u32,
    },
    ConflictingExceptionalCopies {
        predecessor: BlockId,
        variable: u32,
        left_handler: BlockId,
        right_handler: BlockId,
    },
    ConflictingPhiVariable {
        variable: u32,
        left_value: SsaVar,
        left_block: BlockId,
        left_type: crate::ir::ArgType,
        right_value: SsaVar,
        right_block: BlockId,
        right_type: crate::ir::ArgType,
    },
    EmptyParallelCopyCycle,
    MissingSemanticBlock(BlockId),
    MissingSemanticEdge(crate::ir::RegionEdge),
    MissingExceptionalCopySite {
        block: BlockId,
        instruction: crate::ir::InstructionId,
    },
    MissingHandlerEntry(BlockId),
    UnresolvedContractedPhi {
        predecessor: BlockId,
        successor: BlockId,
        value: SsaVar,
    },
    DuplicateSemanticBlock(BlockId),
    MissingSemanticThrowSite(BlockId),
    SyntheticIdentityExhausted,
}

impl fmt::Display for SourceVariableError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InstructionTree(error) => error.fmt(formatter),
            Self::SemanticTransform(error) => error.fmt(formatter),
            Self::Type(error) => error.fmt(formatter),
            Self::Dominance(error) => error.fmt(formatter),
            Self::MissingPhiResult(block) => write!(formatter, "Phi in {block} has no result"),
            Self::NonRegisterPhiInput {
                predecessor,
                successor,
            } => write!(
                formatter,
                "Phi edge {predecessor} -> {successor} has a non-register input"
            ),
            Self::UnsplitNormalEdge {
                predecessor,
                successor,
                targets,
            } => write!(
                formatter,
                "normal Phi edge {predecessor} -> {successor} is not split: {targets:?}"
            ),
            Self::MissingBlock(block) => write!(formatter, "missing Phi predecessor {block}"),
            Self::MissingThrowSite(block) => {
                write!(
                    formatter,
                    "exceptional Phi predecessor {block} has no unique terminal throw site"
                )
            }
            Self::MissingSemanticSite(kind) => {
                write!(formatter, "structured {kind} has no numbered semantic site")
            }
            Self::IncompleteSemanticFlow => {
                formatter.write_str("structured semantic flow is incomplete")
            }
            Self::MissingRegisterIdentity => {
                formatter.write_str("parallel copy register has no SSA identity")
            }
            Self::MissingCodeVariable(variable) => {
                write!(formatter, "SSA value {variable:?} has no source variable")
            }
            Self::LivenessMismatch(block) => {
                write!(
                    formatter,
                    "SSA liveness transfer is inconsistent in {block}"
                )
            }
            Self::ExceptionalCopyClobbersNormalValue {
                predecessor,
                variable,
            } => write!(
                formatter,
                "exceptional copy in {predecessor} clobbers normal-live variable v{variable}"
            ),
            Self::ConflictingExceptionalCopies {
                predecessor,
                variable,
                left_handler,
                right_handler,
            } => write!(
                formatter,
                "exceptional edges from {predecessor} to {left_handler} and {right_handler} assign different values to v{variable}"
            ),
            Self::ConflictingPhiVariable {
                variable,
                left_value,
                left_block,
                left_type,
                right_value,
                right_block,
                right_type,
            } => write!(
                formatter,
                "source variable v{variable} combines Phi {left_value:?} in {left_block} ({left_type:?}) with {right_value:?} in {right_block} ({right_type:?})"
            ),
            Self::EmptyParallelCopyCycle => formatter.write_str("empty parallel-copy cycle"),
            Self::MissingSemanticBlock(block) => {
                write!(formatter, "Phi lowering cannot find semantic block {block}")
            }
            Self::MissingSemanticEdge(edge) => {
                write!(
                    formatter,
                    "Phi lowering cannot find semantic edge {} -> {} ({:?})",
                    edge.source, edge.target, edge.kind
                )
            }
            Self::MissingExceptionalCopySite { block, instruction } => write!(
                formatter,
                "exceptional Phi copy for instruction {instruction:?} has no semantic site in {block}"
            ),
            Self::MissingHandlerEntry(block) => {
                write!(
                    formatter,
                    "exceptional Phi copy has no handler entry {block}"
                )
            }
            Self::UnresolvedContractedPhi {
                predecessor,
                successor,
                value,
            } => write!(
                formatter,
                "SSA value {value:?} on contracted edge {predecessor} -> {successor} is not representable"
            ),
            Self::DuplicateSemanticBlock(block) => {
                write!(formatter, "semantic block {block} occurs more than once")
            }
            Self::MissingSemanticThrowSite(block) => {
                write!(
                    formatter,
                    "semantic block {block} has no throwing instruction for exceptional Phi copies"
                )
            }
            Self::SyntheticIdentityExhausted => {
                formatter.write_str("source control lowering exhausted method-local identities")
            }
        }
    }
}

impl std::error::Error for SourceVariableError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InstructionTree(error) => Some(error),
            Self::SemanticTransform(error) => Some(error),
            Self::Type(error) => Some(error),
            Self::Dominance(error) => Some(error),
            _ => None,
        }
    }
}

impl From<SemanticFoldError> for SourceVariableError {
    fn from(source: SemanticFoldError) -> Self {
        Self::SemanticTransform(source)
    }
}

impl From<TypeConstraintError> for SourceVariableError {
    fn from(source: TypeConstraintError) -> Self {
        Self::Type(source)
    }
}
