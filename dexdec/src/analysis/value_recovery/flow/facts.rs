//! Unified sparse facts consumed by value scheduling.
//!
//! Canonical values, value numbering, reaching definitions, and effect
//! versions are computed from one immutable value-flow graph. Scheduling owns
//! no independent analysis state.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::analysis::value_recovery::{
    numbering::{SyntheticUse, ValueAvailability, ValueNumbering, ValueNumberingResult},
    ValueRecoveryError,
};
use crate::ir::{analysis::SsaVar, InsnArg};

use super::{
    effect_versions::{EffectStability, EffectVersions},
    effects::EffectSummary,
    reaching::{ReachingDefinitionFacts, ReachingDefinitions, SemanticReachingAnalysis},
    DefinitionFact, UseFact, ValueFlowGraph, ValueIdentity,
};

pub(super) struct SparseValueFacts<'a> {
    graph: &'a ValueFlowGraph<'a>,
    canonical: BTreeMap<SsaVar, InsnArg>,
    numbering: ValueNumberingResult,
    uses: Cow<'a, BTreeMap<SsaVar, Vec<UseFact>>>,
    required_phi_inputs: BTreeSet<SsaVar>,
    reaching: SemanticReachingAnalysis<'a>,
    effects: EffectVersions<'a>,
}

impl<'a> SparseValueFacts<'a> {
    pub(super) fn analyze(graph: &'a ValueFlowGraph<'a>) -> Result<Self, ValueRecoveryError> {
        let canonical = crate::profile_scope!("value.facts.canonical", graph.canonical_values());
        let reachability = crate::profile_scope!(
            "value.facts.reachability",
            graph
                .semantic_flow()
                .filter(|flow| flow.is_complete())
                .map(|flow| Arc::new(flow.reachability()))
        );
        let reaching = crate::profile_scope!(
            "value.facts.reaching",
            SemanticReachingAnalysis::new(graph, reachability.clone())
        );
        let availability = (graph.identity() == ValueIdentity::Source)
            .then_some(&reaching as &dyn ValueAvailability);
        let numbering = crate::profile_scope!("value.facts.numbering", {
            ValueNumbering::analyze(
                graph.identity(),
                &graph.logic,
                graph
                    .definitions
                    .values()
                    .filter_map(|definitions| match definitions.as_slice() {
                        [definition] => Some(definition),
                        _ => None,
                    }),
                &canonical,
                availability,
            )
        })?;
        let uses = crate::profile_scope!(
            "value.facts.uses",
            Self::effective_uses(graph, &numbering.synthetic_uses)
        );
        let required_phi_inputs = crate::profile_scope!(
            "value.facts.phi_inputs",
            (graph.identity() == ValueIdentity::Ssa)
                .then(|| graph.required_phi_inputs())
                .unwrap_or_default()
        );
        let effects = crate::profile_scope!(
            "value.facts.effects",
            EffectVersions::new(graph, reachability)
        );
        Ok(Self {
            graph,
            canonical,
            numbering,
            uses,
            required_phi_inputs,
            reaching,
            effects,
        })
    }

    fn effective_uses(
        graph: &'a ValueFlowGraph<'a>,
        links: &[SyntheticUse],
    ) -> Cow<'a, BTreeMap<SsaVar, Vec<UseFact>>> {
        if links.is_empty() {
            return Cow::Borrowed(&graph.uses);
        }
        let mut uses = graph.uses.clone();
        for link in links {
            if let Some(eliminated) = graph.uses.get(&link.eliminated) {
                uses.entry(link.representative)
                    .or_default()
                    .extend(eliminated.iter().cloned());
            }
        }
        Cow::Owned(uses)
    }

    pub(super) fn graph(&self) -> &'a ValueFlowGraph<'a> {
        self.graph
    }

    pub(super) fn canonical(&self) -> &BTreeMap<SsaVar, InsnArg> {
        &self.canonical
    }

    pub(super) fn constants(&self) -> BTreeMap<SsaVar, InsnArg> {
        self.canonical
            .iter()
            .filter(|(_, value)| ValueFlowGraph::is_constant(value))
            .map(|(key, value)| (*key, value.clone()))
            .collect()
    }

    pub(super) fn replacement(&self, key: SsaVar) -> Option<&InsnArg> {
        self.canonical
            .get(&key)
            .or_else(|| self.numbering.replacements.get(&key))
    }

    pub(super) fn uses(&self) -> &BTreeMap<SsaVar, Vec<UseFact>> {
        self.uses.as_ref()
    }

    pub(super) fn uses_of(&self, key: SsaVar) -> &[UseFact] {
        self.uses.get(&key).map(Vec::as_slice).unwrap_or_default()
    }

    pub(super) fn required_phi_input(&self, key: SsaVar) -> bool {
        self.required_phi_inputs.contains(&key)
    }

    pub(super) fn reaching_definitions(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<ReachingDefinitionFacts, ValueRecoveryError> {
        ReachingDefinitions::new(self.graph, &self.reaching).analyze(definitions, uses)
    }

    pub(super) fn reaching_candidates(
        &self,
        key: SsaVar,
        point: crate::ir::analysis::SemanticFlowPoint,
    ) -> Result<Vec<usize>, ValueRecoveryError> {
        self.reaching.candidates(key, point)
    }

    pub(super) fn reaching_unchanged(
        &self,
        key: SsaVar,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool {
        self.reaching.unchanged(key, source, target)
    }

    pub(super) fn reaching_supports(
        &self,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool {
        self.reaching.supports(source, target)
    }

    pub(super) fn effect_stability(
        &self,
        effect: &EffectSummary,
        domain: super::ControlDomain,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> EffectStability {
        self.effects.stability(effect, domain, source, target)
    }

    pub(super) fn effects_unchanged(
        &self,
        effect: &EffectSummary,
        domain: super::ControlDomain,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool {
        self.effects.unchanged(effect, domain, source, target)
    }
}

impl ValueAvailability for SemanticReachingAnalysis<'_> {
    fn supports(
        &self,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool {
        SemanticReachingAnalysis::supports(self, source, target)
    }

    fn unchanged(
        &self,
        value: SsaVar,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool {
        SemanticReachingAnalysis::unchanged(self, value, source, target)
    }
}
