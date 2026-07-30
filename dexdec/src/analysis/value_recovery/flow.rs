use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::ir::{
    analysis::{PhiMerge, SsaValueGraph, SsaVar},
    BoolVariable, InsnArg, InsnType, SemanticExpression, SemanticNode, SemanticOperation,
    SemanticPredicate, SemanticVisitor, StatementOrigin, Utf16String,
};

mod collector;
mod effect_versions;
mod effects;
mod facts;
mod gated;
mod planner;
mod reaching;

use super::constant::ConstantEvaluator;
use super::domain::{ControlDomain, DomainLogic};
use super::ValueRecoveryError;
use collector::FlowCollector;
use effects::EffectSummary;
use gated::GatedPhiAnalysis;
pub(super) use gated::{GatedControlFlow, PhiExpressionPlacement};
use planner::ValuePlanner;

#[derive(Debug, Clone)]
pub(super) struct DefinitionFact<'ir> {
    pub(super) key: SsaVar,
    pub(super) site: Option<crate::ir::SemanticSiteId>,
    pub(super) origin: Option<&'ir StatementOrigin>,
    pub(super) instruction: crate::ir::InstructionId,
    pub(super) result: &'ir crate::ir::RegisterArg,
    pub(super) value: Cow<'ir, SemanticExpression>,
    pub(super) domain: ControlDomain,
    pub(super) scope: Arc<[u32]>,
    pub(super) protections: Arc<[u32]>,
    pub(super) loop_owners: Arc<[u32]>,
    pub(super) event: usize,
    pub(super) repetitive: bool,
}

impl DefinitionFact<'_> {
    pub(super) fn expression(&self) -> &SemanticExpression {
        self.value.as_ref()
    }

    pub(super) fn owned_expression(&self) -> SemanticExpression {
        self.value.clone().into_owned()
    }

    pub(super) fn operation(&self) -> Option<&SemanticOperation> {
        self.expression().as_operation()
    }

    fn edge_copy(&self) -> bool {
        self.operation()
            .is_some_and(|operation| operation.payload.edge_copy)
    }
}

#[derive(Debug, Clone)]
struct UseFact {
    point: Option<crate::ir::analysis::SemanticFlowPoint>,
    domain: ControlDomain,
    scope: Arc<[u32]>,
    protections: Arc<[u32]>,
    loop_owners: Arc<[u32]>,
    event: usize,
    repetitive: bool,
    evaluation_prefix: EffectSummary,
    context: UseContext,
    site: Option<UseSite>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UseContext {
    Value,
    Predicate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum UseSite {
    Leave(crate::ir::SemanticSiteId),
    Statement(crate::ir::SemanticSiteId),
    SelectedArgument(crate::ir::SemanticSiteId, u32),
    SelectedPredicate(crate::ir::SemanticSiteId, u32),
    Predicate(crate::ir::SemanticSiteId),
    Argument(crate::ir::SemanticSiteId),
}

#[derive(Debug, Clone)]
pub(super) struct ValueExpression {
    pub(super) value: SemanticExpression,
}

#[derive(Debug, Clone)]
struct EffectFact {
    point: crate::ir::analysis::SemanticFlowPoint,
    domain: ControlDomain,
    effect: EffectSummary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PredicateUseFact {
    operand_point: crate::ir::analysis::SemanticFlowPoint,
    effect_point: crate::ir::analysis::SemanticFlowPoint,
    domain: ControlDomain,
}

#[derive(Debug, Clone)]
pub(super) enum ValueAction {
    Propagate {
        event: usize,
        key: SsaVar,
        replacement: InsnArg,
    },
    Inline {
        event: usize,
        key: SsaVar,
        expression: SemanticExpression,
    },
    InlineAt {
        event: usize,
        key: SsaVar,
        remove_key: bool,
        remove_definitions: Vec<crate::ir::SemanticSiteId>,
        replacements: Vec<(UseSite, ValueExpression)>,
    },
    ReplaceAt {
        event: usize,
        key: SsaVar,
        replacements: Vec<(UseSite, InsnArg)>,
    },
    EliminateStatements {
        event: usize,
        statements: Vec<crate::ir::SemanticSiteId>,
    },
    Remove {
        event: usize,
        key: SsaVar,
    },
    DiscardResult {
        event: usize,
        key: SsaVar,
    },
}

pub(super) struct ValuePlan {
    pub(super) actions: Vec<ValueAction>,
    pub(super) constants: BTreeMap<SsaVar, InsnArg>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RecoveryMode {
    Structural,
    Full,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ValueIdentity {
    Ssa,
    Source,
}

#[derive(Debug, Clone, Default)]
struct SsaCopyFlow {
    sources: BTreeMap<SsaVar, SsaVar>,
    omitted: BTreeSet<SsaVar>,
    types: BTreeMap<SsaVar, crate::ir::ArgType>,
}

impl SsaCopyFlow {
    fn analyze(
        values: &SsaValueGraph,
        definitions: &BTreeMap<SsaVar, Vec<DefinitionFact>>,
    ) -> Self {
        let sources = values
            .copies()
            .iter()
            .map(|copy| (copy.result, copy.source))
            .collect::<BTreeMap<_, _>>();
        let omitted = sources
            .keys()
            .filter(|result| !definitions.contains_key(result))
            .copied()
            .collect();
        let types = values
            .values()
            .filter_map(|value| {
                value
                    .observed_types
                    .iter()
                    .find(|ty| ty.is_known())
                    .cloned()
                    .map(|ty| (value.variable, ty))
            })
            .collect();
        Self {
            sources,
            omitted,
            types,
        }
    }

    fn source(&self, mut value: SsaVar) -> SsaVar {
        let mut visited = BTreeSet::new();
        while visited.insert(value) {
            let Some(source) = self.sources.get(&value).copied() else {
                break;
            };
            value = source;
        }
        value
    }

    fn argument(&self, value: SsaVar) -> InsnArg {
        InsnArg::reg_ssa(
            value.reg_num,
            value.version,
            self.types
                .get(&value)
                .cloned()
                .unwrap_or_else(crate::ir::ArgType::unknown),
        )
    }

    fn aliases(&self) -> impl Iterator<Item = (SsaVar, SsaVar)> + '_ {
        self.omitted
            .iter()
            .copied()
            .map(|result| (result, self.source(result)))
            .filter(|(result, source)| result != source)
    }
}

impl ValueIdentity {
    pub(super) fn key(self, register: &crate::ir::RegisterArg) -> Option<SsaVar> {
        match self {
            Self::Ssa => SsaVar::from_reg(register),
            Self::Source => register.code_var.map(|variable| SsaVar::new(variable, 0)),
        }
    }
}

impl UseSite {
    fn id(self) -> crate::ir::SemanticSiteId {
        match self {
            Self::Leave(site)
            | Self::Statement(site)
            | Self::SelectedArgument(site, _)
            | Self::SelectedPredicate(site, _)
            | Self::Predicate(site)
            | Self::Argument(site) => site,
        }
    }

    fn before(self) -> crate::ir::analysis::SemanticFlowPoint {
        crate::ir::analysis::SemanticFlowPoint::before(self.id())
    }
}

pub(super) struct ValueFlowGraph<'ir> {
    identity: ValueIdentity,
    logic: DomainLogic,
    definitions: BTreeMap<SsaVar, Vec<DefinitionFact<'ir>>>,
    /// Values introduced by lexical binders rather than executable statements.
    /// Their definition classes are intentionally open to statement scheduling.
    bindings: BTreeSet<SsaVar>,
    uses: BTreeMap<SsaVar, Vec<UseFact>>,
    phis: Vec<PhiMerge>,
    copies: SsaCopyFlow,
    retained_phi_inputs: BTreeSet<SsaVar>,
    retained_values: BTreeSet<SsaVar>,
    effects: Vec<EffectFact>,
    block_domains: BTreeMap<crate::ir::BlockId, ControlDomain>,
    predicate_tests: BTreeMap<crate::ir::InstructionId, SemanticOperation>,
    predicate_uses: BTreeMap<crate::ir::InstructionId, BTreeSet<PredicateUseFact>>,
    canonical: BTreeMap<SsaVar, InsnArg>,
    identity_statements: Vec<(crate::ir::SemanticSiteId, usize)>,
    semantic_flow: Option<crate::ir::analysis::SemanticFlowGraph>,
}

impl<'ir> ValueFlowGraph<'ir> {
    pub(super) fn build(
        root: &'ir SemanticNode,
        values: &SsaValueGraph,
        canonical: &BTreeMap<SsaVar, InsnArg>,
    ) -> Result<Self, ValueRecoveryError> {
        Self::build_ssa(root, values, canonical, true)
    }

    pub(super) fn build_gated(
        root: &'ir SemanticNode,
        values: &SsaValueGraph,
        canonical: &BTreeMap<SsaVar, InsnArg>,
    ) -> Result<Self, ValueRecoveryError> {
        Self::build_ssa(root, values, canonical, false)
    }

    fn build_ssa(
        root: &'ir SemanticNode,
        values: &SsaValueGraph,
        canonical: &BTreeMap<SsaVar, InsnArg>,
        semantic_flow: bool,
    ) -> Result<Self, ValueRecoveryError> {
        let symbols = crate::profile_scope!(
            "value.graph.control_symbols",
            ControlSymbolClosure::analyze(root)
        );
        let logic =
            crate::profile_scope!("value.graph.domain", DomainLogic::new(&symbols.variables));
        let semantic_flow = crate::profile_scope!(
            "value.graph.semantic_flow",
            semantic_flow.then(|| crate::ir::analysis::SemanticFlowGraph::analyze(root))
        );
        let graph = Self {
            identity: ValueIdentity::Ssa,
            logic,
            definitions: BTreeMap::new(),
            bindings: BTreeSet::new(),
            uses: BTreeMap::new(),
            phis: Vec::new(),
            copies: SsaCopyFlow::default(),
            retained_phi_inputs: BTreeSet::new(),
            retained_values: BTreeSet::new(),
            effects: Vec::new(),
            block_domains: BTreeMap::new(),
            predicate_tests: symbols.tests,
            predicate_uses: BTreeMap::new(),
            canonical: canonical.clone(),
            identity_statements: Vec::new(),
            semantic_flow,
        };
        let mut graph = crate::profile_scope!(
            "value.graph.collect",
            FlowCollector::new(graph).collect(root)
        )?;
        graph.phis = values.phis().to_vec();
        graph.copies = crate::profile_scope!(
            "value.graph.ssa_copies",
            SsaCopyFlow::analyze(values, &graph.definitions)
        );
        crate::profile_scope!("value.graph.validate", graph.validate(values))?;
        Ok(graph)
    }

    pub(super) fn build_source(root: &'ir SemanticNode) -> Result<Self, ValueRecoveryError> {
        Self::build_allocated(root, ValueIdentity::Source)
    }

    fn build_allocated(
        root: &'ir SemanticNode,
        identity: ValueIdentity,
    ) -> Result<Self, ValueRecoveryError> {
        let symbols = crate::profile_scope!(
            "value.graph.control_symbols",
            ControlSymbolClosure::analyze(root)
        );
        let logic =
            crate::profile_scope!("value.graph.domain", DomainLogic::new(&symbols.variables));
        let semantic_flow = crate::profile_scope!(
            "value.graph.semantic_flow",
            crate::ir::analysis::SemanticFlowGraph::analyze(root)
        );
        let graph = Self {
            identity,
            logic,
            definitions: BTreeMap::new(),
            bindings: BTreeSet::new(),
            uses: BTreeMap::new(),
            phis: Vec::new(),
            copies: SsaCopyFlow::default(),
            retained_phi_inputs: BTreeSet::new(),
            retained_values: BTreeSet::new(),
            effects: Vec::new(),
            block_domains: BTreeMap::new(),
            predicate_tests: symbols.tests,
            predicate_uses: BTreeMap::new(),
            canonical: BTreeMap::new(),
            identity_statements: Vec::new(),
            semantic_flow: Some(semantic_flow),
        };
        crate::profile_scope!(
            "value.graph.collect",
            FlowCollector::new(graph).collect(root)
        )
    }

    pub(super) fn schedule(&self, mode: RecoveryMode) -> Result<ValuePlan, ValueRecoveryError> {
        let planner = crate::profile_scope!("value.plan.facts", ValuePlanner::new(self, mode))?;
        crate::profile_scope!("value.plan.actions", planner.schedule())
    }

    pub(super) fn recover_gated_phis(
        &self,
        values: &SsaValueGraph,
        control: &GatedControlFlow,
    ) -> Result<gated::GatedPhiRecovery, ValueRecoveryError> {
        GatedPhiAnalysis::new(self, values, control).analyze()
    }

    pub(super) fn exclude_phis(&mut self, recovered: &BTreeSet<SsaVar>) {
        let excluded = self
            .phis
            .iter()
            .filter(|phi| recovered.contains(&phi.result))
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let mut pending = excluded
            .keys()
            .filter(|result| {
                self.has_reaching_use(**result) && !self.definitions.contains_key(result)
            })
            .copied()
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(result) = pending.pop() {
            if !visited.insert(result) {
                continue;
            }
            let Some(phi) = excluded.get(&result) else {
                continue;
            };
            for input in &phi.inputs {
                self.retained_phi_inputs.insert(input.value);
                if excluded.contains_key(&input.value) {
                    pending.push(input.value);
                }
            }
        }
        self.phis.retain(|phi| !recovered.contains(&phi.result));
    }

    pub(super) fn retain_values(&mut self, values: impl IntoIterator<Item = SsaVar>) {
        self.retained_values.extend(values);
    }

    fn is_retained(&self, value: SsaVar) -> bool {
        self.retained_values.contains(&value)
    }

    fn is_bound(&self, value: SsaVar) -> bool {
        self.bindings.contains(&value)
    }

    pub(super) fn identity(&self) -> ValueIdentity {
        self.identity
    }

    fn copy_source(&self, value: SsaVar) -> SsaVar {
        self.copies.source(value)
    }

    fn semantic_use_roots(&self) -> BTreeSet<SsaVar> {
        self.uses
            .keys()
            .flat_map(|value| [*value, self.copy_source(*value)])
            .collect()
    }

    fn has_reaching_use(&self, value: SsaVar) -> bool {
        self.uses
            .keys()
            .any(|used| *used == value || self.copy_source(*used) == value)
    }

    fn key(&self, register: &crate::ir::RegisterArg) -> Option<SsaVar> {
        self.identity.key(register)
    }

    fn record_binding(&mut self, register: &crate::ir::RegisterArg) {
        if let Some(value) = self.key(register) {
            self.bindings.insert(value);
        }
    }

    fn is_identity_move(&self, instruction: &SemanticOperation) -> bool {
        if instruction.insn_type != InsnType::Move || instruction.operands().len() != 1 {
            return false;
        }
        let Some(result) = instruction
            .result
            .as_ref()
            .and_then(|result| self.key(result))
        else {
            return false;
        };
        Self::canonical_semantic_move_operand(&instruction.operands()[0])
            .as_register()
            .and_then(|source| self.key(source))
            == Some(result)
    }

    fn is_identity_definition(
        &self,
        result: &crate::ir::RegisterArg,
        value: &SemanticExpression,
    ) -> bool {
        let Some(result) = self.key(result) else {
            return false;
        };
        Self::canonical_semantic_move_operand(value)
            .as_register()
            .and_then(|source| self.key(source))
            == Some(result)
    }

    fn canonical_semantic_move_operand(mut value: &SemanticExpression) -> &SemanticExpression {
        loop {
            let SemanticExpression::Operation(operation) = value else {
                return value;
            };
            if operation.insn_type != InsnType::Move || operation.operands().len() != 1 {
                return value;
            }
            value = &operation.operands()[0];
        }
    }

    fn semantic_flow(&self) -> Option<&crate::ir::analysis::SemanticFlowGraph> {
        self.semantic_flow.as_ref()
    }

    fn movement_points(&self) -> BTreeSet<crate::ir::analysis::SemanticFlowPoint> {
        self.definitions
            .values()
            .flatten()
            .filter_map(|definition| {
                definition
                    .site
                    .map(crate::ir::analysis::SemanticFlowPoint::after)
            })
            .chain(self.uses.values().flatten().filter_map(|usage| usage.point))
            .chain(self.effects.iter().map(|effect| effect.point))
            .collect()
    }

    fn is_constant(value: &InsnArg) -> bool {
        matches!(value, InsnArg::Lit(_))
            || matches!(
                value,
                InsnArg::Wrapped(instruction)
                    if matches!(instruction.insn_type, InsnType::Const | InsnType::ConstStr)
            )
    }

    fn validate(&self, values: &SsaValueGraph) -> Result<(), ValueRecoveryError> {
        for (value, definitions) in &self.definitions {
            if definitions.len() > 1 && !Self::are_structural_replicas(definitions) {
                return Err(ValueRecoveryError::DuplicateDefinition(*value));
            }
            if values.value(*value).is_none() {
                return Err(ValueRecoveryError::UnknownValue(*value));
            }
        }
        for value in self.uses.keys() {
            if values.value(*value).is_none() {
                return Err(ValueRecoveryError::UnknownValue(*value));
            }
        }
        Ok(())
    }

    pub(super) fn are_structural_replicas(definitions: &[DefinitionFact]) -> bool {
        let Some(first) = definitions.first() else {
            return false;
        };
        let Some(origin) = first.origin else {
            return false;
        };
        definitions.iter().all(|definition| {
            definition.origin == Some(origin)
                && definition.instruction == first.instruction
                && definition.operation().map(|operation| operation.insn_type)
                    == first.operation().map(|operation| operation.insn_type)
        })
    }

    fn canonical_values(&self) -> BTreeMap<SsaVar, InsnArg> {
        let mut definition_classes = self
            .definitions
            .iter()
            .filter(|(_, definitions)| !definitions.is_empty())
            .collect::<Vec<_>>();
        definition_classes.sort_by_key(|(_, definitions)| {
            definitions
                .iter()
                .map(|definition| definition.event)
                .max()
                .unwrap_or_default()
        });
        let mut values = self.canonical.clone();
        for (result, source) in self.copies.aliases() {
            values
                .entry(result)
                .or_insert_with(|| self.copies.argument(source));
        }
        loop {
            let mut changed = false;
            for (&key, definitions) in &definition_classes {
                let Some(value) = self.canonical_class_value(definitions, &values) else {
                    continue;
                };
                let value_key = self.canonical_key(&value);
                if values.get(&key).and_then(|value| self.canonical_key(value)) != value_key {
                    values.insert(key, value);
                    changed = true;
                }
            }
            for phi in &self.phis {
                let Some((replacement_key, replacement)) =
                    self.trivial_phi_replacement(phi, &values)
                else {
                    continue;
                };
                let changed_value = values
                    .get(&phi.result)
                    .and_then(|value| self.canonical_key(value))
                    .is_none_or(|current| current != replacement_key);
                if changed_value {
                    values.insert(phi.result, replacement);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        values
    }

    /// Computes the meet of every definition assigned to one value identity.
    /// Source allocation deliberately coalesces multiple SSA definitions into
    /// one local; a canonical value exists only when every reaching definition
    /// evaluates to the same lattice constant.
    fn canonical_class_value(
        &self,
        definitions: &[DefinitionFact],
        values: &BTreeMap<SsaVar, InsnArg>,
    ) -> Option<InsnArg> {
        let mut representative = None::<(CanonicalKey, InsnArg)>;
        for definition in definitions {
            if definition.edge_copy() {
                return None;
            }
            let value = self.resolve_canonical(self.canonical_value(definition, values)?, values);
            let key = self.canonical_key(&value)?;
            match &representative {
                None => representative = Some((key, value)),
                Some((representative_key, _)) if *representative_key == key => {}
                Some(_) => return None,
            }
        }
        representative.map(|(_, value)| value)
    }

    fn trivial_phi_replacement(
        &self,
        phi: &PhiMerge,
        values: &BTreeMap<SsaVar, InsnArg>,
    ) -> Option<(CanonicalKey, InsnArg)> {
        let self_key = CanonicalKey::Value(phi.result);
        let mut representative = None::<(CanonicalKey, InsnArg)>;
        for input in &phi.inputs {
            let value = self.resolve_canonical(
                InsnArg::reg_ssa(
                    input.value.reg_num,
                    input.value.version,
                    self.phi_value_type(input.value),
                ),
                values,
            );
            let key = self.canonical_key(&value)?;
            if key == self_key {
                continue;
            }
            match &representative {
                None => representative = Some((key, value)),
                Some((representative_key, _)) if *representative_key == key => {}
                Some(_) => return None,
            }
        }
        representative
    }

    fn canonical_value(
        &self,
        definition: &DefinitionFact,
        values: &BTreeMap<SsaVar, InsnArg>,
    ) -> Option<InsnArg> {
        if let SemanticExpression::Literal(literal) = definition.expression() {
            return Some(InsnArg::Lit(literal.clone()));
        }
        let expression = definition.operation()?;
        match expression.insn_type {
            InsnType::ConstStr => Some(InsnArg::wrap(
                expression.instruction_with_arguments(Vec::new()),
            )),
            InsnType::Move | InsnType::CheckCast => {
                let source = Self::semantic_leaf_argument(Self::canonical_semantic_move_operand(
                    expression.operands().first()?,
                ))?;
                if expression.insn_type == InsnType::CheckCast
                    && expression.conversion_type() != source.declared_type()
                {
                    return None;
                }
                match &source {
                    InsnArg::Lit(_) => Some(source),
                    InsnArg::Reg(register) => {
                        let key = self.key(register)?;
                        Some(values.get(&key).cloned().unwrap_or(source))
                    }
                    InsnArg::Wrapped(_) => None,
                }
            }
            _ => {
                let arguments = definition
                    .operation()?
                    .operands()
                    .iter()
                    .map(Self::semantic_leaf_argument)
                    .collect::<Option<Vec<_>>>()?
                    .into_iter()
                    .map(|argument| self.resolve_canonical(argument, values))
                    .collect::<Vec<_>>();
                let instruction = definition
                    .operation()?
                    .instruction_with_arguments(arguments.clone());
                ConstantEvaluator::fold(&instruction, &arguments)
            }
        }
    }

    fn semantic_leaf_argument(expression: &SemanticExpression) -> Option<InsnArg> {
        match expression {
            SemanticExpression::Register(register) => Some(InsnArg::Reg(register.clone())),
            SemanticExpression::Literal(literal) => Some(InsnArg::Lit(literal.clone())),
            SemanticExpression::Operation(_) | SemanticExpression::Select { .. } => None,
        }
    }

    fn resolve_canonical(&self, mut value: InsnArg, values: &BTreeMap<SsaVar, InsnArg>) -> InsnArg {
        let mut visited = BTreeSet::new();
        loop {
            let Some(variable) = value.as_register().and_then(|register| self.key(register)) else {
                return value;
            };
            if !visited.insert(variable) {
                return value;
            }
            let Some(replacement) = values.get(&variable) else {
                return value;
            };
            value = replacement.clone();
        }
    }

    fn phi_value_type(&self, value: SsaVar) -> crate::ir::ArgType {
        self.definitions
            .get(&value)
            .and_then(|definitions| definitions.first())
            .map(|definition| definition.result.ty.clone())
            .unwrap_or_else(crate::ir::ArgType::unknown)
    }

    fn canonical_key(&self, value: &InsnArg) -> Option<CanonicalKey> {
        match value {
            InsnArg::Lit(literal) => Some(CanonicalKey::Literal {
                value: literal.value,
                ty: literal.ty.clone(),
            }),
            InsnArg::Reg(register) => self.key(register).map(CanonicalKey::Value),
            InsnArg::Wrapped(instruction) => match instruction.insn_type {
                InsnType::Const => {
                    let literal = instruction.args.first()?.as_literal()?;
                    Some(CanonicalKey::Literal {
                        value: literal.value,
                        ty: instruction
                            .result
                            .as_ref()
                            .map(|result| result.ty.clone())
                            .unwrap_or_else(|| literal.ty.clone()),
                    })
                }
                InsnType::ConstStr => Some(CanonicalKey::String(
                    instruction.payload.string_value.clone()?,
                )),
                _ => None,
            },
        }
    }

    fn required_phi_inputs(&self) -> BTreeSet<SsaVar> {
        let phis = self
            .phis
            .iter()
            .map(|phi| (phi.result, phi))
            .collect::<BTreeMap<_, _>>();
        let mut pending = self
            .phis
            .iter()
            .filter(|phi| self.has_reaching_use(phi.result))
            .map(|phi| phi.result)
            .collect::<Vec<_>>();
        let mut required = self.retained_phi_inputs.clone();
        let mut visited = BTreeSet::new();
        while let Some(result) = pending.pop() {
            if !visited.insert(result) {
                continue;
            }
            let Some(phi) = phis.get(&result) else {
                continue;
            };
            for input in &phi.inputs {
                required.insert(input.value);
                if phis.contains_key(&input.value) {
                    pending.push(input.value);
                }
            }
        }
        required
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalKey {
    Value(SsaVar),
    Literal { value: i64, ty: crate::ir::ArgType },
    String(Utf16String),
}

#[derive(Default)]
struct ControlSymbolClosure {
    variables: BTreeSet<BoolVariable>,
    tests: BTreeMap<crate::ir::InstructionId, SemanticOperation>,
}

impl ControlSymbolClosure {
    fn analyze(root: &SemanticNode) -> Self {
        let mut closure = Self::default();
        closure.visit_node(root);
        closure
    }
}

impl SemanticVisitor for ControlSymbolClosure {
    fn visit_predicate(&mut self, predicate: &SemanticPredicate) {
        self.variables.extend(predicate.symbols());
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(instruction) => {
                    self.tests.insert(instruction.id, instruction.clone());
                    self.visit_operation(instruction);
                }
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms);
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        InsnNode, InsnType, InstructionId, RegionId, SemanticCatch, SemanticExpression,
    };

    fn operation(
        id: usize,
        insn_type: InsnType,
        operands: Vec<SemanticExpression>,
    ) -> SemanticOperation {
        let mut instruction = InsnNode::new(insn_type, operands.len());
        instruction.id = InstructionId::new(id);
        SemanticOperation::from_parts(instruction, operands, None)
    }

    #[test]
    fn control_symbol_closure_includes_selects_inside_predicate_operands() {
        let nested = SemanticPredicate::Test(operation(21, InsnType::If, Vec::new()));
        let selected = SemanticExpression::select(
            nested,
            SemanticExpression::Operation(Box::new(operation(22, InsnType::Const, Vec::new()))),
            SemanticExpression::Operation(Box::new(operation(23, InsnType::Const, Vec::new()))),
        );
        let outer = SemanticPredicate::Test(operation(20, InsnType::If, vec![selected]));

        let mut closure = ControlSymbolClosure::default();
        closure.visit_predicate(&outer);

        assert_eq!(
            closure.variables,
            BTreeSet::from([
                BoolVariable::Instruction(InstructionId::new(20)),
                BoolVariable::Instruction(InstructionId::new(21)),
            ])
        );
        assert_eq!(
            closure.tests.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([InstructionId::new(20), InstructionId::new(21)])
        );
    }

    #[test]
    fn catch_parameters_are_lexical_value_bindings() {
        let mut exception =
            crate::ir::RegisterArg::new(0, crate::ir::ArgType::object("java/lang/Throwable"));
        exception.code_var = Some(7);
        let root = SemanticNode::Try {
            region: RegionId::new(1),
            body: Box::new(SemanticNode::Empty),
            catches: vec![SemanticCatch {
                region: RegionId::new(2),
                exception_types: vec![crate::ir::ArgType::object("java/lang/Exception")],
                exception_value: Some(exception),
                body: SemanticNode::Empty,
            }],
            finally: None,
        };

        let graph = ValueFlowGraph::build_source(&root).unwrap();

        assert!(graph.is_bound(SsaVar::new(7, 0)));
    }
}
