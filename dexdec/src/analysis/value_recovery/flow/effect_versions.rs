//! Path-sensitive source-observable effect stability.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::ir::analysis::{SemanticFlowPoint, SemanticReachability};

use super::{effects::EffectSummary, ControlDomain, ValueFlowGraph};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum EffectStability {
    Stable,
    IncompleteFlow,
    DoesNotReach,
    Changed,
}

pub(super) struct EffectVersions<'a> {
    graph: &'a ValueFlowGraph<'a>,
    reachability: Option<Arc<SemanticReachability>>,
}

impl<'a> EffectVersions<'a> {
    pub(super) fn new(
        graph: &'a ValueFlowGraph<'a>,
        reachability: Option<Arc<SemanticReachability>>,
    ) -> Self {
        Self {
            graph,
            reachability,
        }
    }

    pub(super) fn unchanged(
        &self,
        effect: &EffectSummary,
        domain: ControlDomain,
        source: SemanticFlowPoint,
        target: SemanticFlowPoint,
    ) -> bool {
        self.stability(effect, domain, source, target) == EffectStability::Stable
    }

    pub(super) fn stability(
        &self,
        effect: &EffectSummary,
        domain: ControlDomain,
        source: SemanticFlowPoint,
        target: SemanticFlowPoint,
    ) -> EffectStability {
        if effect.is_pure() {
            return EffectStability::Stable;
        }
        let Some(flow) = self.graph.semantic_flow() else {
            return EffectStability::IncompleteFlow;
        };
        let Some(reachability) = &self.reachability else {
            return EffectStability::IncompleteFlow;
        };
        if !flow.must_reach(source, target) {
            return EffectStability::DoesNotReach;
        }
        let conflicting = self
            .graph
            .effects
            .iter()
            .filter(|fact| {
                fact.point != source
                    && fact.point != target
                    && effect.conflicts_with(&fact.effect)
                    && !self
                        .graph
                        .logic
                        .disjoint(domain, fact.domain)
                        .unwrap_or(false)
            })
            .map(|fact| fact.point)
            .collect::<BTreeSet<_>>();
        if reachability.reaches_any_between(source, target, &conflicting) {
            EffectStability::Changed
        } else {
            EffectStability::Stable
        }
    }
}
