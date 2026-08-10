//! Sparse SSA value recovery over structured semantic IR.
//!
//! Value identity comes from SSA, scheduling legality comes from control
//! domains and the effect model, and every transformation consumes facts from one
//! value-flow graph.

use std::collections::{BTreeMap, BTreeSet};

mod constant;
mod domain;
mod flow;
mod initialization;
mod loops;
mod numbering;
mod predicate_regions;
mod schedule;
mod source;
mod ssa_constants;

use crate::analysis::SemanticTransform;
use crate::ir::analysis::{DominanceError, SsaVar};
use crate::ir::{
    BlockId, SemanticFoldError, SemanticMethod, SourceVariableContext, SsaSemantics,
    ValueSemantics, CFG,
};

pub use domain::DomainError;
use flow::{
    GatedControlFlow, PhiExpressionPlacement, RecoveryMode, ValueAction, ValueFlowGraph,
    ValueIdentity,
};
use schedule::ValueSchedule;
use ssa_constants::SparseConstantPropagation;

#[derive(Debug)]
pub struct ValueRecovery {
    gated_control: GatedControlFlow,
    ssa_constants: BTreeMap<SsaVar, crate::ir::InsnArg>,
    source_bindings: BTreeSet<SsaVar>,
    diagnostics: crate::ir::ValueRecoveryDiagnostics,
}

#[derive(Debug, Clone)]
pub enum ValueRecoveryError {
    DuplicateDefinition(SsaVar),
    UnknownValue(SsaVar),
    ScopeUnderflow,
    ScopeKindMismatch,
    UnclosedScope,
    SourceEvaluation(crate::ir::analysis::SourceEvaluationError),
    MissingReplacement(SsaVar),
    MissingDependency(SsaVar),
    MissingPhiPlacement(BlockId),
    IncompleteSemanticFlow,
    MissingSemanticSite,
    MissingDefinitionSite(SsaVar),
    MissingUsePoint(SsaVar),
    MissingReachingFact {
        value: SsaVar,
        point: crate::ir::analysis::SemanticFlowPoint,
    },
    Dominance(DominanceError),
    ControlDomain(DomainError),
    SemanticTransform(SemanticFoldError),
    InstructionTree(crate::ir::InstructionTreeError),
}

impl std::fmt::Display for ValueRecoveryError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateDefinition(value) => {
                write!(formatter, "semantic IR defines {value:?} more than once")
            }
            Self::UnknownValue(value) => {
                write!(formatter, "semantic IR references unknown {value:?}")
            }
            Self::ScopeUnderflow => formatter.write_str("value-flow scope stack underflow"),
            Self::ScopeKindMismatch => formatter.write_str("value-flow scope kind mismatch"),
            Self::UnclosedScope => formatter.write_str("value-flow scope stack is not empty"),
            Self::SourceEvaluation(source) => {
                write!(formatter, "source evaluation failed: {source}")
            }
            Self::MissingReplacement(value) => {
                write!(formatter, "replacement graph is missing {value:?}")
            }
            Self::MissingDependency(value) => {
                write!(formatter, "replacement dependency is missing {value:?}")
            }
            Self::MissingPhiPlacement(block) => {
                write!(
                    formatter,
                    "gated Phi expression has no semantic block {block}"
                )
            }
            Self::IncompleteSemanticFlow => {
                formatter.write_str("semantic control graph has unresolved transfers")
            }
            Self::MissingSemanticSite => {
                formatter.write_str("semantic value fact has no numbered site")
            }
            Self::MissingDefinitionSite(value) => {
                write!(
                    formatter,
                    "definition of {value:?} has no numbered semantic site"
                )
            }
            Self::MissingUsePoint(value) => {
                write!(formatter, "use of {value:?} has no semantic flow point")
            }
            Self::MissingReachingFact { value, point } => {
                write!(
                    formatter,
                    "reaching-definition facts for {value:?} are missing at {point:?}"
                )
            }
            Self::Dominance(source) => write!(formatter, "dominance analysis failed: {source}"),
            Self::ControlDomain(source) => write!(formatter, "control domain failed: {source}"),
            Self::SemanticTransform(source) => {
                write!(formatter, "semantic transform failed: {source}")
            }
            Self::InstructionTree(source) => {
                write!(formatter, "instruction tree transform failed: {source}")
            }
        }
    }
}

impl std::error::Error for ValueRecoveryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Dominance(source) => Some(source),
            Self::ControlDomain(source) => Some(source),
            Self::SourceEvaluation(source) => Some(source),
            Self::SemanticTransform(source) => Some(source),
            Self::InstructionTree(source) => Some(source),
            _ => None,
        }
    }
}

impl From<DomainError> for ValueRecoveryError {
    fn from(source: DomainError) -> Self {
        Self::ControlDomain(source)
    }
}

impl From<DominanceError> for ValueRecoveryError {
    fn from(source: DominanceError) -> Self {
        Self::Dominance(source)
    }
}

impl From<SemanticFoldError> for ValueRecoveryError {
    fn from(source: SemanticFoldError) -> Self {
        Self::SemanticTransform(source)
    }
}

impl From<crate::ir::InstructionTreeError> for ValueRecoveryError {
    fn from(source: crate::ir::InstructionTreeError) -> Self {
        Self::InstructionTree(source)
    }
}

impl From<crate::ir::analysis::SourceEvaluationError> for ValueRecoveryError {
    fn from(source: crate::ir::analysis::SourceEvaluationError) -> Self {
        Self::SourceEvaluation(source)
    }
}

impl ValueRecovery {
    pub fn new(cfg: &CFG) -> Result<Self, ValueRecoveryError> {
        Ok(Self {
            gated_control: GatedControlFlow::analyze(cfg)?,
            ssa_constants: SparseConstantPropagation::new(cfg).solve(),
            source_bindings: BTreeSet::new(),
            diagnostics: crate::ir::ValueRecoveryDiagnostics::default(),
        })
    }

    pub(crate) fn bind_source_inputs(&mut self, cfg: &CFG) {
        self.source_bindings.clear();
        self.source_bindings.extend(
            cfg.this_code_variable()
                .into_iter()
                .chain(cfg.parameter_code_variables().iter().flatten().copied())
                .map(|variable| SsaVar::new(variable, 0)),
        );
    }

    pub fn diagnostics(&self) -> &crate::ir::ValueRecoveryDiagnostics {
        &self.diagnostics
    }

    pub fn recover_source<State: SourceVariableContext>(
        &mut self,
        method: &mut SemanticMethod<State>,
    ) -> Result<bool, ValueRecoveryError> {
        source::SourceValueRecovery::recover(method, RecoveryMode::Full, &self.source_bindings)
    }

    pub fn prepare_source<State: SourceVariableContext>(
        &mut self,
        method: &mut SemanticMethod<State>,
    ) -> Result<bool, ValueRecoveryError> {
        source::SourceValueRecovery::recover(
            method,
            RecoveryMode::Structural,
            &self.source_bindings,
        )
    }
}

impl SemanticTransform<SsaSemantics> for ValueRecovery {
    type Output = ValueSemantics;
    type Error = ValueRecoveryError;

    fn transform(
        &mut self,
        mut method: SemanticMethod<SsaSemantics>,
    ) -> Result<SemanticMethod<Self::Output>, Self::Error> {
        crate::profile_scope!(
            "value.ssa.numbering",
            crate::ir::SemanticSiteNumbering::assign(method.body_mut())
        )?;
        let graph = crate::profile_scope!("value.ssa.gated_graph", {
            ValueFlowGraph::build_gated(method.body(), method.state().values(), &self.ssa_constants)
        })?;
        let recovery = crate::profile_scope!(
            "value.ssa.gated_phis",
            graph.recover_gated_phis(method.state().values(), &self.gated_control)
        )?;
        self.diagnostics = recovery.diagnostics;
        let mut recovered_phis = recovery.eliminated;
        let placement = PhiExpressionPlacement::new(recovery.expressions);
        recovered_phis.extend(placement.recovered());
        let specialization_actions = recovery
            .specializations
            .into_iter()
            .map(|specialization| {
                recovered_phis.insert(specialization.result);
                ValueAction::ReplaceAt {
                    event: 0,
                    key: specialization.result,
                    replacements: specialization.replacements,
                }
            })
            .collect::<Vec<_>>();
        crate::profile_scope!(
            "value.ssa.phi_placement",
            placement.apply(method.body_mut())
        )?;
        let specialization_schedule = crate::profile_scope!(
            "value.ssa.specialization_schedule",
            ValueSchedule::compile(specialization_actions, ValueIdentity::Ssa)
        )?;
        crate::profile_scope!(
            "value.ssa.specialization_apply",
            specialization_schedule.apply(method.body_mut())
        )?;
        let retained =
            crate::profile_scope!("value.ssa.cleanup_roots", cleanup_state_values(&method));
        let constants = SsaValueSolver::new(&recovered_phis, &self.ssa_constants, &retained)
            .solve_profiled(&mut method)?;
        Ok(method.into_values(constants, recovered_phis))
    }
}

fn cleanup_state_values(method: &SemanticMethod<SsaSemantics>) -> BTreeSet<SsaVar> {
    let mut values = method
        .state()
        .regions()
        .cleanup_value_bindings()
        .iter()
        .flat_map(|(handler, normal)| [*handler, *normal])
        .collect::<BTreeSet<_>>();
    let phis = method
        .state()
        .values()
        .phis()
        .iter()
        .map(|phi| (phi.result, phi))
        .collect::<BTreeMap<_, _>>();
    let mut pending = values.iter().copied().collect::<Vec<_>>();
    while let Some(value) = pending.pop() {
        let Some(phi) = phis.get(&value) else {
            continue;
        };
        for input in &phi.inputs {
            if values.insert(input.value) {
                pending.push(input.value);
            }
        }
    }
    values
}

struct SsaValueSolver<'a> {
    recovered_phis: &'a BTreeSet<SsaVar>,
    constants: &'a BTreeMap<SsaVar, crate::ir::InsnArg>,
    retained_values: &'a BTreeSet<SsaVar>,
}

impl<'a> SsaValueSolver<'a> {
    fn new(
        recovered_phis: &'a BTreeSet<SsaVar>,
        constants: &'a BTreeMap<SsaVar, crate::ir::InsnArg>,
        retained_values: &'a BTreeSet<SsaVar>,
    ) -> Self {
        Self {
            recovered_phis,
            constants,
            retained_values,
        }
    }

    fn solve(
        self,
        method: &mut SemanticMethod<SsaSemantics>,
    ) -> Result<BTreeMap<SsaVar, crate::ir::InsnArg>, ValueRecoveryError> {
        let mut constants = BTreeMap::new();
        loop {
            crate::profile_scope!(
                "value.ssa.solve.numbering",
                crate::ir::SemanticSiteNumbering::assign(method.body_mut())
            )?;
            let mut graph = crate::profile_scope!(
                "value.ssa.solve.graph",
                ValueFlowGraph::build(method.body(), method.state().values(), self.constants)
            )?;
            graph.exclude_phis(self.recovered_phis);
            graph.retain_values(self.retained_values.iter().copied());
            let value_plan =
                crate::profile_scope!("value.ssa.solve.plan", graph.schedule(RecoveryMode::Full))?;
            constants.extend(value_plan.constants);
            let schedule = crate::profile_scope!(
                "value.ssa.solve.schedule",
                ValueSchedule::compile(value_plan.actions, ValueIdentity::Ssa)
            )?;
            let changed =
                crate::profile_scope!("value.ssa.solve.apply", schedule.apply(method.body_mut()))?;
            if !changed {
                break;
            }
            crate::profile_scope!(
                "value.ssa.solve.normalize",
                method.normalize_before_phi_lowering()
            )?;
        }
        crate::profile_scope!(
            "value.ssa.solve.numbering",
            crate::ir::SemanticSiteNumbering::assign(method.body_mut())
        )?;
        Ok(constants)
    }

    fn solve_profiled(
        self,
        method: &mut SemanticMethod<SsaSemantics>,
    ) -> Result<BTreeMap<SsaVar, crate::ir::InsnArg>, ValueRecoveryError> {
        crate::profile_scope!("value.ssa.solve", self.solve(method))
    }
}
