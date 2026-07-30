//! Source-identity scheduling after source-variable allocation.
//!
//! Allocation removes phi obligations and assigns stable `code_var` identities.
//! The same control-domain and effect scheduler used for SSA can therefore run
//! again with source identities, without a second propagation or DCE algorithm.

use crate::ir::{SemanticFoldError, SemanticMethod, SourceVariableContext};

use super::{
    flow::{RecoveryMode, ValueFlowGraph, ValueIdentity},
    initialization::SourceInitializationRecovery,
    loops::LoopInvariantMotion,
    predicate_regions::PredicateRegionFormation,
    schedule::ValueSchedule,
    ValueRecoveryError,
};

pub(super) struct SourceValueRecovery;

impl SourceValueRecovery {
    pub(super) fn recover<State: SourceVariableContext>(
        method: &mut SemanticMethod<State>,
        mode: RecoveryMode,
    ) -> Result<bool, ValueRecoveryError> {
        crate::profile_scope!("value.source.normalize", method.normalize_source())?;
        let mut changed = false;
        loop {
            loop {
                let initialization = crate::profile_scope!(
                    "value.source.initialization",
                    SourceInitializationRecovery::apply(method.body_mut())
                )?;
                if initialization {
                    crate::profile_scope!(
                        "value.source.normalize_bindings",
                        method.normalize_source_variables()
                    )?;
                }
                crate::profile_scope!(
                    "value.source.numbering",
                    crate::ir::SemanticSiteNumbering::assign(method.body_mut())
                )?;
                let graph = crate::profile_scope!(
                    "value.source.graph",
                    ValueFlowGraph::build_source(method.body())
                )?;
                let plan = crate::profile_scope!("value.source.plan", graph.schedule(mode))?;
                let before_schedule = crate::profile_scope!(
                    "value.source.topology_before",
                    crate::ir::semantic::SemanticControlTopology::analyze(method.body())
                );
                let schedule = crate::profile_scope!(
                    "value.source.schedule",
                    ValueSchedule::compile(plan.actions, ValueIdentity::Source)
                )?;
                let source =
                    crate::profile_scope!("value.source.apply", schedule.apply(method.body_mut()))?;
                crate::profile_scope!(
                    "value.source.topology_after",
                    Self::verify_topology(method, &before_schedule, "source-value-schedule")
                )?;
                let motion = crate::profile_scope!(
                    "value.source.loop_motion",
                    LoopInvariantMotion::apply(method.body_mut())
                )?;
                changed |= initialization || source || motion;
                if !initialization && !source && !motion {
                    break;
                }
                crate::profile_scope!("value.source.normalize", method.normalize_source())?;
            }
            let predicates = crate::profile_scope!(
                "value.source.predicate_regions",
                PredicateRegionFormation::apply(method.body_mut())
            )?;
            changed |= predicates;
            if !predicates {
                break;
            }
            crate::profile_scope!("value.source.normalize", method.normalize_source())?;
        }
        Ok(changed)
    }

    fn verify_topology<State: SourceVariableContext>(
        method: &SemanticMethod<State>,
        before: &crate::ir::semantic::SemanticControlTopology,
        transform: &'static str,
    ) -> Result<(), ValueRecoveryError> {
        let after = crate::ir::semantic::SemanticControlTopology::analyze(method.body());
        if before != &after {
            return Err(SemanticFoldError::ControlTopologyChanged { transform }.into());
        }
        Ok(())
    }
}
