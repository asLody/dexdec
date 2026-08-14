use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    BoolExpr, InsnArg, InsnType, SemanticExpression, SemanticExpressionFacts, SemanticOperation,
};

use super::{
    effect_versions::EffectStability,
    effects::EffectSummary,
    facts::SparseValueFacts,
    gated::{
        build_source_selection, equivalent, SelectedValue, SourceSelection, SourceSelectionInput,
    },
};
use super::{
    CanonicalKey, DefinitionFact, RecoveryMode, UseContext, UseFact, UseSite, ValueAction,
    ValueExpression, ValueFlowGraph, ValueIdentity, ValuePlan,
};
use crate::analysis::value_recovery::ValueRecoveryError;
use crate::ir::analysis::SsaVar;

pub(super) struct ValuePlanner<'a> {
    facts: SparseValueFacts<'a>,
    mode: RecoveryMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MovementRejection {
    DefinitionOrder,
    ScopeBoundary,
    ProtectionBoundary,
    LoopBoundary,
    ControlDomain,
    EvaluationOrder,
    MissingFlowPoint,
    OperandVersion,
    EffectVersion,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum DefinitionProvenance {
    Statement(crate::ir::StatementOrigin),
    Value(crate::ir::InstructionId),
}

/// Bounded source-level cost model for duplicating a value at control uses.
///
/// Predicate rematerialization is useful for VM instructions such as `cmp-*`:
/// keeping their integer result materialized hides the relational expression
/// from language syntax recovery. The movement proof remains responsible for
/// semantic safety; this model only prevents source-size expansion.
struct RematerializationModel;

impl RematerializationModel {
    const MAX_NODES: usize = 8;
    const MAX_OPERATIONS: usize = 3;
    const MAX_TRANSPARENT_USES: usize = 4;

    fn accepts(expression: &SemanticExpression) -> bool {
        let mut pending = vec![expression];
        let mut nodes = 0usize;
        let mut operations = 0usize;
        while let Some(expression) = pending.pop() {
            nodes += 1;
            if nodes > Self::MAX_NODES {
                return false;
            }
            match expression {
                SemanticExpression::Register(_) | SemanticExpression::Literal(_) => {}
                SemanticExpression::Operation(operation) => {
                    operations += 1;
                    if operations > Self::MAX_OPERATIONS {
                        return false;
                    }
                    pending.extend(operation.operands());
                    pending.extend(operation.compound_target());
                }
                SemanticExpression::Select { .. } => return false,
            }
        }
        true
    }
}

impl<'a> ValuePlanner<'a> {
    pub(super) fn new(
        graph: &'a ValueFlowGraph<'a>,
        mode: RecoveryMode,
    ) -> Result<Self, ValueRecoveryError> {
        Ok(Self {
            facts: SparseValueFacts::analyze(graph)?,
            mode,
        })
    }

    fn graph(&self) -> &ValueFlowGraph<'_> {
        self.facts.graph()
    }

    pub(super) fn schedule(&self) -> Result<ValuePlan, ValueRecoveryError> {
        let mut actions = self
            .graph()
            .identity_statements
            .iter()
            .map(|(site, event)| ValueAction::EliminateStatements {
                event: *event,
                statements: vec![*site],
            })
            .collect::<Vec<_>>();
        for (key, definitions) in &self.graph().definitions {
            if self.graph().is_retained(*key) || self.graph().is_bound(*key) {
                continue;
            }
            if let Some(action) =
                self.dead_source_definitions_action(definitions, self.facts.uses_of(*key))?
            {
                actions.push(action);
                continue;
            }
            if let Some(action) =
                self.redundant_merge_action(definitions, self.facts.uses_of(*key))?
            {
                actions.push(action);
                continue;
            }
            if definitions.len() > 1
                && !self.facts.uses().contains_key(key)
                && !self.facts.required_phi_input(*key)
                && definitions
                    .iter()
                    .all(|definition| EffectSummary::expression(definition.expression()).is_pure())
            {
                actions.push(ValueAction::Remove {
                    event: definitions
                        .iter()
                        .map(|definition| definition.event)
                        .max()
                        .unwrap_or_default(),
                    key: *key,
                });
                continue;
            }
            if definitions.len() > 1 {
                if let Some(action) = self.constant_class_action(
                    definitions,
                    self.facts.uses_of(*key),
                    self.facts.replacement(*key),
                ) {
                    actions.push(action);
                    continue;
                }
                if let Some(action) =
                    self.congruent_class_action(definitions, self.facts.uses_of(*key))?
                {
                    actions.push(action);
                    continue;
                }
            }
            let [definition] = definitions.as_slice() else {
                if Self::has_replicated_origin(definitions) {
                    if let Some(action) =
                        self.source_selection_action(definitions, self.facts.uses_of(*key))?
                    {
                        actions.push(action);
                    }
                    continue;
                }
                if let Some(action) =
                    self.action_for_class(definitions, self.facts.uses_of(*key))?
                {
                    actions.push(action);
                }
                continue;
            };
            let uses = self.facts.uses_of(definition.key);
            let replacement = self.facts.replacement(definition.key);
            if let Some(action) = self.action_for(definition, uses, replacement)? {
                actions.push(action);
            }
        }
        self.cfg_constant_actions(&mut actions);
        self.cfg_copy_actions(&mut actions);
        self.phi_actions(&mut actions);
        self.retain_replacement_frontier(&mut actions)?;
        actions.sort_by_key(|action| std::cmp::Reverse(action.event()));
        let constants = self.facts.constants();
        Ok(ValuePlan { actions, constants })
    }

    fn constant_class_action(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
        replacement: Option<&InsnArg>,
    ) -> Option<ValueAction> {
        let replacement = replacement.filter(|value| ValueFlowGraph::is_constant(value))?;
        if uses.is_empty()
            || !definitions
                .iter()
                .all(|definition| EffectSummary::expression(definition.expression()).is_pure())
        {
            return None;
        }
        Some(ValueAction::Propagate {
            event: definitions
                .iter()
                .map(|definition| definition.event)
                .max()
                .unwrap_or_default(),
            key: definitions[0].key,
            replacement: replacement.clone(),
        })
    }

    /// Eliminates a source value whose reaching definitions all assign the
    /// same stable value. This is the source-identity form of trivial Phi
    /// elimination: every use may have several reaching definitions, but the
    /// value lattice has one member at that use.
    fn congruent_class_action(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<Option<ValueAction>, ValueRecoveryError> {
        if self.mode != RecoveryMode::Full
            || self.graph().identity() != ValueIdentity::Source
            || definitions.len() < 2
            || uses.is_empty()
        {
            return Ok(None);
        }

        let expression = definitions[0].expression();
        if self.expression_depends_on(expression, definitions[0].key) {
            return Ok(None);
        }
        if definitions
            .iter()
            .any(|definition| !Self::selection_effect(definition).is_pure())
        {
            return Ok(None);
        }
        if definitions
            .iter()
            .skip(1)
            .any(|definition| !self.same_expression(expression, definition.expression()))
        {
            return Ok(None);
        }

        let reaching = self.facts.reaching_definitions(definitions, uses)?;
        for (usage, relation) in uses.iter().zip(&reaching.uses) {
            let (Some(target), false) = (usage.point, relation.candidates.is_empty()) else {
                return Ok(None);
            };
            if !self.expression_visible_at(expression, &usage.scope) {
                return Ok(None);
            }
            for &candidate in &relation.candidates {
                let definition = &definitions[candidate];
                let Some(site) = definition.site else {
                    return Ok(None);
                };
                if !self.operands_unchanged(
                    definition,
                    crate::ir::analysis::SemanticFlowPoint::before(site),
                    target,
                ) {
                    return Ok(None);
                }
            }
        }

        Ok(Some(ValueAction::Inline {
            event: definitions
                .iter()
                .map(|definition| definition.event)
                .max()
                .unwrap_or_default(),
            key: definitions[0].key,
            expression: expression.clone(),
        }))
    }

    /// Commits one dependency frontier per recovery iteration.
    ///
    /// Independent movement proofs are not closed under arbitrary transitive
    /// substitution: an outer value can acquire an inner allocation, field
    /// read, or call after both actions are composed. Applying producer leaves
    /// first preserves use cardinality and lets the next recovery stage rebuild
    /// domains, effects, and use-def facts before moving the expanded consumer.
    /// A single lexical use in a loop is also a repeated dynamic use and may
    /// not acquire an effect evaluated before that loop.
    fn retain_replacement_frontier(
        &self,
        actions: &mut Vec<ValueAction>,
    ) -> Result<(), ValueRecoveryError> {
        let replacement_keys = actions
            .iter()
            .filter_map(Self::replacement_key)
            .collect::<BTreeSet<_>>();
        if replacement_keys.len() < 2 {
            return Ok(());
        }
        let blocking_keys = if self.graph().identity() == ValueIdentity::Source {
            replacement_keys.clone()
        } else {
            let mut keys = BTreeSet::new();
            for action in actions.iter() {
                let Some(key) = Self::replacement_key(action) else {
                    continue;
                };
                if Self::replacement_has_effect(action)? {
                    keys.insert(key);
                }
            }
            loop {
                let mut discovered = BTreeSet::new();
                for action in actions.iter() {
                    let Some(key) = Self::replacement_key(action) else {
                        continue;
                    };
                    if keys.contains(&key) {
                        continue;
                    }
                    let mut dependencies = self.replacement_dependencies(action)?;
                    dependencies.remove(&key);
                    if !dependencies.is_disjoint(&keys) {
                        discovered.insert(key);
                    }
                }
                if discovered.is_empty() {
                    break;
                }
                keys.extend(discovered);
            }
            keys
        };
        if blocking_keys.is_empty() {
            return Ok(());
        }
        let ssa_identity = self.graph().identity() == ValueIdentity::Ssa;
        let mut deferred_keys = BTreeSet::new();
        for action in actions.iter() {
            let Some(key) = Self::replacement_key(action) else {
                continue;
            };
            let mut dependencies = self.replacement_dependencies(action)?;
            dependencies.remove(&key);
            let crosses_repetition =
                self.replacement_enters_repetition(key, &dependencies, &blocking_keys);
            if (!ssa_identity || self.facts.uses_of(key).len() > 1 || crosses_repetition)
                && !dependencies.is_disjoint(&blocking_keys)
            {
                deferred_keys.insert(key);
            }
        }
        if ssa_identity {
            // A canonical replacement may jump over register moves.  If an
            // intermediate alias fans out, composing every replacement in one
            // round would clone the effectful producer at those uses.
            // Carry that boundary through the actual move chain, including
            // aliases whose canonical replacement points straight at the
            // producer.  Do not cross arithmetic or Phi definitions: those
            // are distinct state transitions whose old/new ordering must stay
            // available to the current schedule.
            loop {
                let discovered = actions
                    .iter()
                    .filter_map(Self::replacement_key)
                    .filter(|key| !deferred_keys.contains(key))
                    .filter(|key| {
                        self.graph()
                            .definitions
                            .get(key)
                            .into_iter()
                            .flatten()
                            .filter_map(|definition| self.register_move_source(definition))
                            .any(|dependency| deferred_keys.contains(&dependency))
                    })
                    .collect::<BTreeSet<_>>();
                if discovered.is_empty() {
                    break;
                }
                deferred_keys.extend(discovered);
            }
        }
        let mut retained = Vec::with_capacity(actions.len());
        for action in std::mem::take(actions) {
            let Some(key) = Self::replacement_key(&action) else {
                retained.push(action);
                continue;
            };
            if !deferred_keys.contains(&key) {
                retained.push(action);
            }
        }
        *actions = retained;
        Ok(())
    }

    fn replacement_enters_repetition(
        &self,
        key: SsaVar,
        dependencies: &BTreeSet<SsaVar>,
        blocking_keys: &BTreeSet<SsaVar>,
    ) -> bool {
        self.facts.uses_of(key).iter().any(|usage| {
            usage.repetitive
                && dependencies.iter().any(|dependency| {
                    blocking_keys.contains(dependency)
                        && self
                            .graph()
                            .definitions
                            .get(dependency)
                            .is_some_and(|definitions| {
                                definitions.iter().any(|definition| !definition.repetitive)
                            })
                })
        })
    }

    fn register_move_source(&self, definition: &DefinitionFact) -> Option<SsaVar> {
        let operation = definition.operation()?;
        let [SemanticExpression::Register(register)] = operation.operands() else {
            return None;
        };
        (operation.insn_type == InsnType::Move)
            .then(|| self.graph().key(register))
            .flatten()
    }

    fn replacement_key(action: &ValueAction) -> Option<SsaVar> {
        match action {
            ValueAction::Propagate { key, .. }
            | ValueAction::Inline { key, .. }
            | ValueAction::InlineAt { key, .. }
            | ValueAction::ReplaceAt { key, .. } => Some(*key),
            ValueAction::EliminateStatements { .. }
            | ValueAction::Remove { .. }
            | ValueAction::DiscardResult { .. } => None,
        }
    }

    fn replacement_dependencies(
        &self,
        action: &ValueAction,
    ) -> Result<BTreeSet<SsaVar>, ValueRecoveryError> {
        Ok(Self::replacement_expressions(action)?
            .iter()
            .flat_map(|expression| self.expression_variables(expression))
            .collect())
    }

    fn replacement_has_effect(action: &ValueAction) -> Result<bool, ValueRecoveryError> {
        Ok(Self::replacement_expressions(action)?
            .iter()
            .any(|expression| !EffectSummary::expression(expression).is_pure()))
    }

    fn replacement_expressions(
        action: &ValueAction,
    ) -> Result<Vec<SemanticExpression>, ValueRecoveryError> {
        Ok(match action {
            ValueAction::Propagate { replacement, .. } => {
                vec![SemanticExpression::from_argument(replacement.clone())?]
            }
            ValueAction::Inline { expression, .. } => vec![expression.clone()],
            ValueAction::InlineAt { replacements, .. } => replacements
                .iter()
                .map(|(_, replacement)| replacement.value.clone())
                .collect(),
            ValueAction::ReplaceAt { replacements, .. } => replacements
                .iter()
                .map(|(_, replacement)| SemanticExpression::from_argument(replacement.clone()))
                .collect::<Result<Vec<_>, _>>()?,
            ValueAction::EliminateStatements { .. }
            | ValueAction::Remove { .. }
            | ValueAction::DiscardResult { .. } => Vec::new(),
        })
    }

    /// Removes individual source definitions killed before every feasible use.
    ///
    /// Source identities deliberately group all assignments to one Kotlin local.
    /// Class-wide use counts therefore cannot identify an overwritten
    /// predecessor definition. The occurrence-sensitive reaching model can:
    /// a definition with no candidate use is dead independently of the other
    /// definitions in its source class.
    fn dead_source_definitions_action(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<Option<ValueAction>, ValueRecoveryError> {
        if self.mode != RecoveryMode::Full
            || self.graph().identity() != ValueIdentity::Source
            || definitions.len() < 2
            || uses.is_empty()
        {
            return Ok(None);
        }
        let reaching = self.facts.reaching_definitions(definitions, uses)?;
        let dead = definitions
            .iter()
            .zip(reaching.candidate_uses)
            .filter_map(|(definition, candidate_uses)| {
                (candidate_uses == 0 && Self::selection_effect(definition).is_pure())
                    .then_some((definition.site?, definition.event))
            })
            .collect::<Vec<_>>();
        if dead.is_empty() {
            return Ok(None);
        }
        Ok(Some(ValueAction::EliminateStatements {
            event: dead
                .iter()
                .map(|(_, event)| *event)
                .max()
                .unwrap_or_default(),
            statements: dead.into_iter().map(|(site, _)| site).collect(),
        }))
    }

    fn redundant_merge_action(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<Option<ValueAction>, ValueRecoveryError> {
        if self.mode != RecoveryMode::Full
            || self.graph().identity() != ValueIdentity::Source
            || definitions.len() < 2
        {
            return Ok(None);
        }
        for current in definitions.iter().rev() {
            let Some(site) = current.site else {
                continue;
            };
            let value = Self::canonical_expression(&current.value);
            let SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } = value
            else {
                continue;
            };
            if !EffectSummary::expression(&current.value).is_pure() {
                continue;
            }
            let true_key = self.expression_key(when_true);
            let false_key = self.expression_key(when_false);
            let replacement = match (
                true_key == Some(current.key),
                false_key == Some(current.key),
            ) {
                (true, false) => when_false.as_ref(),
                (false, true) => when_true.as_ref(),
                _ => {
                    continue;
                }
            };
            if self.expression_depends_on(replacement, current.key) {
                continue;
            }
            let selected_uses = uses
                .iter()
                .filter(|usage| {
                    matches!(
                        usage.site,
                        Some(
                            UseSite::SelectedArgument(use_site, _)
                                | UseSite::Statement(use_site)
                        ) if use_site == site
                    )
                })
                .collect::<Vec<_>>();
            let Some(self_use) = selected_uses.first().copied() else {
                continue;
            };
            let mut selected_domains_match = true;
            for usage in selected_uses.iter().skip(1) {
                if !self
                    .graph()
                    .logic
                    .equivalent(self_use.domain, usage.domain)?
                {
                    selected_domains_match = false;
                    break;
                }
            }
            if !selected_domains_match {
                continue;
            }
            let target = crate::ir::analysis::SemanticFlowPoint::before(site);
            let candidates = self.facts.reaching_candidates(current.key, target)?;
            if candidates.is_empty() {
                continue;
            }
            if !self.graph().logic.covered_by(
                current.domain,
                candidates.iter().map(|index| definitions[*index].domain),
            )? {
                continue;
            }
            let mut proven = true;
            for index in candidates {
                let candidate = &definitions[index];
                if candidate.event >= current.event {
                    proven = false;
                    break;
                }
                if self
                    .graph()
                    .logic
                    .implies(candidate.domain, self_use.domain)?
                {
                    continue;
                }
                let Some(candidate_site) = candidate.site else {
                    proven = false;
                    break;
                };
                if !self.same_merge_value(candidate, replacement, current)
                    || !self.operands_unchanged(
                        candidate,
                        crate::ir::analysis::SemanticFlowPoint::before(candidate_site),
                        target,
                    )
                {
                    proven = false;
                    break;
                }
            }
            if !proven {
                continue;
            }
            return Ok(Some(ValueAction::EliminateStatements {
                event: current.event,
                statements: vec![site],
            }));
        }
        Ok(None)
    }

    fn same_merge_value(
        &self,
        candidate: &DefinitionFact,
        replacement: &SemanticExpression,
        current: &DefinitionFact,
    ) -> bool {
        if self.same_expression(&candidate.value, replacement) {
            return true;
        }
        current.result.ty.is_reference()
            && candidate.value.literal_value() == Some(0)
            && replacement.literal_value() == Some(0)
    }

    fn action_for(
        &self,
        definition: &DefinitionFact,
        uses: &[UseFact],
        replacement: Option<&InsnArg>,
    ) -> Result<Option<ValueAction>, ValueRecoveryError> {
        if self.facts.required_phi_input(definition.key)
            && !replacement.is_some_and(ValueFlowGraph::is_constant)
        {
            return Ok(None);
        }
        if let Some(replacement) = replacement {
            if self.can_propagate(definition, uses, replacement)? {
                return Ok(Some(ValueAction::Propagate {
                    event: definition.event,
                    key: definition.key,
                    replacement: replacement.clone(),
                }));
            }
        }
        if uses.is_empty() {
            return Ok(self.unused_action(definition));
        }
        if let Some(action) = self.rematerialization_action(definition, uses)? {
            return Ok(Some(action));
        }
        let inline = match self.mode {
            RecoveryMode::Structural => uses
                .first()
                .is_some_and(|usage| usage.context == UseContext::Predicate),
            RecoveryMode::Full => true,
        };
        if inline && self.can_inline(definition, uses)? {
            return Ok(Some(ValueAction::Inline {
                event: definition.event,
                key: definition.key,
                expression: definition.owned_expression(),
            }));
        }
        Ok(None)
    }

    /// Replicates a cheap pure value into every proven destination.
    ///
    /// Predicate expressions use a bounded tree-cost model. Transparent VM
    /// conversions may also be copied to a small number of ordinary uses;
    /// they carry no source computation and exposing them lets language-level
    /// promotion remove conversions that Kotlin performs implicitly.
    fn rematerialization_action(
        &self,
        definition: &DefinitionFact,
        uses: &[UseFact],
    ) -> Result<Option<ValueAction>, ValueRecoveryError> {
        if self.mode != RecoveryMode::Full {
            return Ok(None);
        }
        if uses.len() < 2 {
            return Ok(None);
        }
        let predicate_only = uses
            .iter()
            .all(|usage| usage.context == UseContext::Predicate);
        let transparent = uses.len() <= RematerializationModel::MAX_TRANSPARENT_USES
            && self.transparent_rematerialization(definition);
        if !predicate_only && !transparent {
            return Ok(None);
        }
        if self.definition_depends_on(definition, definition.key) {
            return Ok(None);
        }
        if !transparent && !RematerializationModel::accepts(definition.expression()) {
            return Ok(None);
        }
        let Some(effect) = Self::relocatable_definition_effect(definition) else {
            return Ok(None);
        };
        if !effect.is_pure() {
            return Ok(None);
        }
        for usage in uses {
            if !self.can_move(definition, usage, effect.clone())? {
                return Ok(None);
            }
        }
        Ok(Some(ValueAction::Inline {
            event: definition.event,
            key: definition.key,
            expression: definition.owned_expression(),
        }))
    }

    /// Proves transparency over the value DAG that the current schedule may
    /// expose, not merely over the outer opcode.
    ///
    /// A cast of a one-use invoke is syntactically cheap but becomes effectful
    /// when the invoke is inlined in the same schedule. Expanding unique
    /// producers here keeps the rematerialization proof closed under that
    /// composition.
    fn transparent_rematerialization(&self, definition: &DefinitionFact) -> bool {
        let mut pending = vec![definition.expression()];
        let mut expanded = BTreeSet::new();
        while let Some(expression) = pending.pop() {
            match expression {
                SemanticExpression::Register(register) => {
                    let Some(key) = self.graph().key(register) else {
                        continue;
                    };
                    if key == definition.key {
                        return false;
                    }
                    let Some([producer]) = self.graph().definitions.get(&key).map(Vec::as_slice)
                    else {
                        continue;
                    };
                    if self.facts.uses_of(key).len() == 1 && expanded.insert(key) {
                        pending.push(producer.expression());
                    }
                }
                SemanticExpression::Literal(_) => {}
                SemanticExpression::Operation(operation)
                    if matches!(
                        operation.insn_type,
                        InsnType::Move | InsnType::Const | InsnType::Cast
                    ) && operation.operands().len() == 1 =>
                {
                    pending.push(&operation.operands()[0]);
                }
                SemanticExpression::Operation(_) | SemanticExpression::Select { .. } => {
                    return false;
                }
            }
        }
        true
    }

    fn action_for_class(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<Option<ValueAction>, ValueRecoveryError> {
        if self.mode != RecoveryMode::Full || definitions.is_empty() || uses.is_empty() {
            return Ok(None);
        }
        if let Some(action) = self.source_selection_action(definitions, uses)? {
            return Ok(Some(action));
        }
        // A region may materialize the same CFG instruction in several
        // lexical occurrences (for example, a shared exception handler).
        // A proven value partition above may safely consume synthetic edge
        // copies; all other class-wide rewrites require distinct provenance.
        if Self::has_replicated_origin(definitions) {
            return Ok(None);
        }
        let Some((matches, definition_uses, candidate_uses)) =
            self.match_definitions(definitions, uses)?
        else {
            return Ok(None);
        };
        let complete = definitions.len() == uses.len()
            && matches.iter().all(Option::is_some)
            && definition_uses.iter().all(|uses| *uses == 1);
        let event = definitions
            .iter()
            .map(|definition| definition.event)
            .max()
            .unwrap_or_default();
        let mut site_uses = BTreeMap::new();
        for site in uses.iter().filter_map(|usage| usage.site) {
            *site_uses.entry(site).or_insert(0usize) += 1;
        }
        let mut replacements = Vec::with_capacity(uses.len());
        let mut remove_definitions = BTreeSet::new();
        let control_only = uses.iter().all(|usage| {
            matches!(
                usage.site,
                Some(
                    super::UseSite::Predicate(_)
                        | super::UseSite::SelectedPredicate(_, _)
                        | super::UseSite::Argument(_)
                )
            )
        });
        for (usage, definition) in uses.iter().zip(matches) {
            let Some(definition) = definition else {
                continue;
            };
            let Some(site) = usage.site else {
                continue;
            };
            let site_count = site_uses.get(&site).copied().unwrap_or_default();
            let self_dependency =
                self.definition_depends_on(&definitions[definition], definitions[0].key);
            if site_count != 1 || self_dependency {
                continue;
            }
            let control_operand = matches!(
                site,
                super::UseSite::Predicate(_)
                    | super::UseSite::SelectedPredicate(_, _)
                    | super::UseSite::Argument(_)
            );
            if control_operand && !control_only {
                continue;
            }
            let reaching_count = candidate_uses[definition];
            let duplicable = self.can_duplicate_definition_at(
                &definitions[definition],
                usage,
                definitions[0].key,
            );
            if reaching_count != 1 && !duplicable {
                continue;
            }
            if definition_uses[definition] == 1
                && candidate_uses[definition] == 1
                && self.can_remove_definition(&definitions[definition], usage)?
            {
                remove_definitions.extend(definitions[definition].site);
            }
            replacements.push((
                site,
                ValueExpression {
                    value: definitions[definition].owned_expression(),
                },
            ));
        }
        if replacements.is_empty() {
            return Ok(None);
        }
        Ok(Some(ValueAction::InlineAt {
            event,
            key: definitions[0].key,
            remove_key: complete && replacements.len() == uses.len(),
            remove_definitions: remove_definitions.into_iter().collect(),
            replacements,
        }))
    }

    fn has_replicated_origin(definitions: &[DefinitionFact]) -> bool {
        let mut proven = BTreeSet::new();
        for definition in definitions {
            let Some(origin) = Self::definition_provenance(definition) else {
                return true;
            };
            if !proven.insert(origin) {
                return true;
            }
        }
        false
    }

    fn definition_provenance(definition: &DefinitionFact) -> Option<DefinitionProvenance> {
        if let Some(origin) = &definition.origin {
            return Some(DefinitionProvenance::Statement((*origin).clone()));
        }
        let mut value = definition.expression();
        loop {
            let SemanticExpression::Operation(operation) = value else {
                return None;
            };
            if operation.insn_type == InsnType::Move && operation.operands().len() == 1 {
                value = &operation.operands()[0];
                continue;
            }
            return operation
                .id
                .is_valid()
                .then_some(DefinitionProvenance::Value(operation.id));
        }
    }

    fn source_selection_action(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<Option<ValueAction>, ValueRecoveryError> {
        const EXPRESSION_NODE_LIMIT: usize = 64;

        if self.graph().identity() != ValueIdentity::Source || definitions.len() < 2 {
            return Ok(None);
        }
        let [usage] = uses else {
            return Ok(None);
        };
        let (Some(use_site), Some(target)) = (usage.site, usage.point) else {
            return Ok(None);
        };
        let reaching = self.facts.reaching_definitions(definitions, uses)?;
        let [relation] = reaching.uses.as_slice() else {
            return Ok(None);
        };
        if relation.candidates.len() != definitions.len() {
            return Ok(None);
        }
        for (index, left) in definitions.iter().enumerate() {
            for right in &definitions[index + 1..] {
                if !self.graph().logic.disjoint(left.domain, right.domain)? {
                    return Ok(None);
                }
            }
        }
        for definition in definitions {
            let effect = Self::selection_effect(definition);
            let reason = if definition.repetitive {
                Some("repetitive-definition")
            } else if definition.event >= usage.event {
                Some("definition-order")
            } else if definition.protections != usage.protections {
                Some("protection-boundary")
            } else if definition.loop_owners != usage.loop_owners {
                Some("loop-boundary")
            } else if !effect.can_predicate() {
                Some("non-predicable")
            } else if self.definition_depends_on(definition, definitions[0].key) {
                Some("cyclic-definition")
            } else {
                None
            };
            if reason.is_some() {
                return Ok(None);
            }
        }
        for definition in definitions {
            let Some(site) = definition.site else {
                return Ok(None);
            };
            let source = crate::ir::analysis::SemanticFlowPoint::after(site);
            if !self
                .graph()
                .semantic_flow()
                .is_some_and(|flow| flow.is_complete() && flow.must_reach(source, target))
            {
                return Ok(None);
            }
            if !self.operands_unchanged(
                definition,
                crate::ir::analysis::SemanticFlowPoint::before(site),
                target,
            ) || !self.expression_visible_at(definition.expression(), &usage.scope)
            {
                return Ok(None);
            }
        }

        let Some(care) = self.graph().logic.expression_under(
            usage.domain,
            self.graph().logic.truth(),
            EXPRESSION_NODE_LIMIT,
        )?
        else {
            return Ok(None);
        };
        let mut candidates = relation.candidates.clone();
        candidates.sort_by_key(|index| definitions[*index].event);
        let mut remaining = care.clone();
        let mut inputs = Vec::with_capacity(candidates.len());
        for index in candidates.into_iter().rev() {
            let definition = &definitions[index];
            let Some(domain) = self.graph().logic.expression_under(
                definition.domain,
                usage.domain,
                EXPRESSION_NODE_LIMIT,
            )?
            else {
                return Ok(None);
            };
            let gate = BoolExpr::and(vec![remaining.clone(), domain.clone()]);
            remaining = BoolExpr::and(vec![remaining, BoolExpr::not(domain.clone())]);
            let effect = Self::selection_effect(definition);
            let Some(site) = definition.site else {
                return Ok(None);
            };
            let active_domain = BoolExpr::and(vec![care.clone(), domain]);
            if !effect.is_pure() && !equivalent(&active_domain, &gate)? {
                return Ok(None);
            }
            let evaluation_prefix = usage.evaluation_prefix.clone().without_control();
            if effect.conflicts_with(&evaluation_prefix) {
                return Ok(None);
            }
            if !effect.is_pure() {
                match self.facts.effect_stability(
                    &effect,
                    definition.domain,
                    crate::ir::analysis::SemanticFlowPoint::after(site),
                    target,
                ) {
                    EffectStability::Stable => {}
                    EffectStability::IncompleteFlow => {
                        return Ok(None);
                    }
                    EffectStability::DoesNotReach => {
                        return Ok(None);
                    }
                    EffectStability::Changed => {
                        return Ok(None);
                    }
                }
            }
            let value = definition.owned_expression();
            inputs.push(SourceSelectionInput {
                key: self.selection_key(&value, index as u32),
                value,
                gate,
            });
        }
        let Some(movable_predicates) =
            self.movable_source_predicates(&care, &inputs, usage, target)?
        else {
            return Ok(None);
        };
        let expression =
            match build_source_selection(self.graph(), &movable_predicates, care, inputs)? {
                SourceSelection::Recovered(expression) => expression,
                SourceSelection::Rejected(_) => {
                    return Ok(None);
                }
            };
        if !self.expression_visible_at(&expression, &usage.scope) {
            return Ok(None);
        }
        if self.expression_depends_on(&expression, definitions[0].key) {
            return Ok(None);
        };
        Ok(Some(ValueAction::InlineAt {
            event: definitions
                .iter()
                .map(|definition| definition.event)
                .max()
                .unwrap_or_default(),
            key: definitions[0].key,
            remove_key: true,
            remove_definitions: definitions
                .iter()
                .filter_map(|definition| definition.site)
                .collect(),
            replacements: vec![(use_site, ValueExpression { value: expression })],
        }))
    }

    fn movable_source_predicates(
        &self,
        care: &BoolExpr,
        inputs: &[SourceSelectionInput],
        usage: &UseFact,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> Result<Option<BTreeSet<crate::ir::InstructionId>>, ValueRecoveryError> {
        let mut symbols = care.symbols();
        for input in inputs {
            symbols.extend(input.gate.symbols());
        }
        let mut movable = BTreeSet::new();
        let mut observable = Vec::new();
        for symbol in symbols {
            let crate::ir::BoolVariable::Instruction(instruction) = symbol else {
                continue;
            };
            let Some(test) = self.graph().predicate_tests.get(&instruction) else {
                return Ok(None);
            };
            let effect = EffectSummary::operation(test).without_control();
            if effect.is_pure() {
                continue;
            }
            if effect.conflicts_with(&usage.evaluation_prefix.clone().without_control()) {
                return Ok(None);
            }
            let Some(occurrences) = self.graph().predicate_uses.get(&instruction) else {
                return Ok(None);
            };
            let relevant = occurrences
                .iter()
                .filter(|occurrence| {
                    self.graph()
                        .logic
                        .disjoint(occurrence.domain, usage.domain)
                        .map(|disjoint| !disjoint)
                        .unwrap_or(false)
                })
                .collect::<Vec<_>>();
            if relevant.len() != 1 {
                return Ok(None);
            }
            let occurrence = relevant[0];
            if !self.predicate_operands_unchanged(test, occurrence.operand_point, target) {
                return Ok(None);
            }
            match self.facts.effect_stability(
                &effect,
                occurrence.domain,
                occurrence.effect_point,
                target,
            ) {
                EffectStability::Stable => {}
                EffectStability::IncompleteFlow => {
                    return Ok(None);
                }
                EffectStability::DoesNotReach => {
                    return Ok(None);
                }
                EffectStability::Changed => {
                    return Ok(None);
                }
            }
            if observable
                .iter()
                .any(|existing: &EffectSummary| effect.conflicts_with(existing))
            {
                return Ok(None);
            }
            observable.push(effect);
            movable.insert(instruction);
        }
        Ok(Some(movable))
    }

    fn predicate_operands_unchanged(
        &self,
        predicate: &SemanticOperation,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool {
        if !self.facts.reaching_supports(source, target) {
            return false;
        }
        let facts = SemanticExpressionFacts::of_operation(predicate);
        match self.graph().identity() {
            ValueIdentity::Ssa => facts
                .used_ssa_variables()
                .all(|key| self.facts.reaching_unchanged(key, source, target)),
            ValueIdentity::Source => facts
                .used_variables()
                .map(|variable| SsaVar::new(variable, 0))
                .all(|key| self.facts.reaching_unchanged(key, source, target)),
        }
    }

    fn match_definitions(
        &self,
        definitions: &[DefinitionFact],
        uses: &[UseFact],
    ) -> Result<Option<(Vec<Option<usize>>, Vec<usize>, Vec<usize>)>, ValueRecoveryError> {
        let reaching = self.facts.reaching_definitions(definitions, uses)?;
        let mut definition_uses = vec![0usize; definitions.len()];
        let mut matches = Vec::with_capacity(uses.len());
        for (usage, relation) in uses.iter().zip(&reaching.uses) {
            let index = relation.selected;
            let Some(index) = index else {
                matches.push(None);
                continue;
            };
            let Some(effect) = Self::relocatable_definition_effect(&definitions[index]) else {
                matches.push(None);
                continue;
            };
            if !self.can_move_to_site(&definitions[index], usage, effect)? {
                matches.push(None);
                continue;
            }
            definition_uses[index] += 1;
            matches.push(Some(index));
        }
        for (definition, uses) in definitions.iter().zip(&definition_uses) {
            if *uses > 1
                && !Self::relocatable_definition_effect(definition)
                    .is_some_and(|effect| effect.is_pure())
            {
                return Ok(None);
            }
        }
        Ok(Some((matches, definition_uses, reaching.candidate_uses)))
    }

    fn can_remove_definition(
        &self,
        definition: &DefinitionFact,
        usage: &UseFact,
    ) -> Result<bool, ValueRecoveryError> {
        Ok(definition.site.is_some()
            && definition.event + 1 == usage.event
            && definition.scope == usage.scope
            && definition.loop_owners == usage.loop_owners
            && self
                .graph()
                .logic
                .equivalent(definition.domain, usage.domain)?)
    }

    fn can_propagate(
        &self,
        definition: &DefinitionFact,
        uses: &[UseFact],
        replacement: &InsnArg,
    ) -> Result<bool, ValueRecoveryError> {
        if uses.is_empty() {
            return Ok(false);
        }
        if ValueFlowGraph::is_constant(replacement) {
            return Ok(true);
        }
        let InsnArg::Reg(register) = replacement else {
            return Ok(false);
        };
        let Some(key) = self.graph().key(register) else {
            return Ok(true);
        };
        let Some(source) = definition
            .site
            .map(crate::ir::analysis::SemanticFlowPoint::before)
        else {
            return Ok(false);
        };
        for usage in uses {
            if definition.event >= usage.event
                || !self
                    .graph()
                    .logic
                    .implies(usage.domain, definition.domain)?
                || !usage.point.is_some_and(|target| {
                    self.facts.reaching_supports(source, target)
                        && self.facts.reaching_unchanged(key, source, target)
                })
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn unused_action(&self, definition: &DefinitionFact) -> Option<ValueAction> {
        if EffectSummary::expression(definition.expression()).is_pure() {
            return Some(ValueAction::Remove {
                event: definition.event,
                key: definition.key,
            });
        }
        definition
            .operation()
            .is_some_and(|operation| {
                matches!(
                    operation.insn_type,
                    InsnType::Invoke | InsnType::Constructor
                )
            })
            .then_some(ValueAction::DiscardResult {
                event: definition.event,
                key: definition.key,
            })
    }

    fn can_inline(
        &self,
        definition: &DefinitionFact,
        uses: &[UseFact],
    ) -> Result<bool, ValueRecoveryError> {
        let [usage] = uses else {
            return Ok(false);
        };
        if self.adjacent_inline(definition, usage)? {
            return Ok(true);
        }
        let same_domain = self
            .graph()
            .logic
            .equivalent(definition.domain, usage.domain)?;
        let Some(effect) = Self::relocatable_definition_effect(definition) else {
            return Ok(false);
        };
        let domain_sink =
            self.is_domain_preserving_sink(definition, usage, &effect, same_domain)?;
        if let Err(_) = self.prove_movement(definition, usage, &effect, same_domain, domain_sink) {
            return Ok(false);
        }
        Ok(true)
    }

    fn adjacent_inline(
        &self,
        definition: &DefinitionFact,
        usage: &UseFact,
    ) -> Result<bool, ValueRecoveryError> {
        if definition.site.is_none()
            || definition.event + 1 != usage.event
            || definition.protections != usage.protections
            || definition.loop_owners != usage.loop_owners
            || !self
                .graph()
                .logic
                .equivalent(definition.domain, usage.domain)?
        {
            return Ok(false);
        }
        if definition.scope == usage.scope && usage.evaluation_prefix.is_pure() {
            return Ok(true);
        }
        let control_use = usage.context == UseContext::Predicate
            || matches!(
                usage.site,
                Some(UseSite::SelectedArgument(_, _) | UseSite::SelectedPredicate(_, _))
            );
        Ok(control_use && usage.evaluation_prefix.clone().without_control().is_pure())
    }

    fn can_move(
        &self,
        definition: &DefinitionFact,
        usage: &UseFact,
        effect: EffectSummary,
    ) -> Result<bool, ValueRecoveryError> {
        let same_domain = self
            .graph()
            .logic
            .equivalent(definition.domain, usage.domain)?;
        let domain_sink =
            self.is_domain_preserving_sink(definition, usage, &effect, same_domain)?;
        match self.prove_movement(definition, usage, &effect, same_domain, domain_sink) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    fn is_domain_preserving_sink(
        &self,
        definition: &DefinitionFact,
        usage: &UseFact,
        effect: &EffectSummary,
        same_domain: bool,
    ) -> Result<bool, ValueRecoveryError> {
        let control_use = usage.context == UseContext::Predicate
            || matches!(
                usage.site,
                Some(UseSite::SelectedArgument(_, _) | UseSite::SelectedPredicate(_, _))
            );
        if !control_use {
            return Ok(false);
        }
        Ok(same_domain
            || (effect.is_pure()
                && self
                    .graph()
                    .logic
                    .implies(usage.domain, definition.domain)?))
    }

    fn can_move_to_site(
        &self,
        definition: &DefinitionFact,
        usage: &UseFact,
        effect: EffectSummary,
    ) -> Result<bool, ValueRecoveryError> {
        self.can_move(definition, usage, effect)
    }

    fn prove_movement(
        &self,
        definition: &DefinitionFact,
        usage: &UseFact,
        effect: &EffectSummary,
        same_domain: bool,
        domain_sink: bool,
    ) -> Result<(), MovementRejection> {
        if definition.event >= usage.event {
            return Err(MovementRejection::DefinitionOrder);
        }
        if definition.scope != usage.scope && !domain_sink {
            return Err(MovementRejection::ScopeBoundary);
        }
        if definition.protections != usage.protections {
            return Err(MovementRejection::ProtectionBoundary);
        }
        if definition.loop_owners != usage.loop_owners {
            return Err(MovementRejection::LoopBoundary);
        }
        if !same_domain && !domain_sink {
            return Err(MovementRejection::ControlDomain);
        }
        let evaluation_prefix = if domain_sink {
            usage.evaluation_prefix.clone().without_control()
        } else {
            usage.evaluation_prefix.clone()
        };
        if effect.conflicts_with(&evaluation_prefix) {
            return Err(MovementRejection::EvaluationOrder);
        }
        let (Some(site), Some(target)) = (definition.site, usage.point) else {
            return Err(MovementRejection::MissingFlowPoint);
        };
        let source = crate::ir::analysis::SemanticFlowPoint::before(site);
        if !self.operands_unchanged(definition, source, target) {
            return Err(MovementRejection::OperandVersion);
        }
        if !effect.is_pure()
            && !self.facts.effects_unchanged(
                effect,
                definition.domain,
                crate::ir::analysis::SemanticFlowPoint::after(site),
                target,
            )
        {
            return Err(MovementRejection::EffectVersion);
        }
        Ok(())
    }

    fn operands_unchanged(
        &self,
        definition: &DefinitionFact,
        source: crate::ir::analysis::SemanticFlowPoint,
        target: crate::ir::analysis::SemanticFlowPoint,
    ) -> bool {
        if !self.facts.reaching_supports(source, target) {
            return false;
        }
        self.expression_variables(definition.expression())
            .into_iter()
            .filter(|key| *key != definition.key)
            .all(|key| self.facts.reaching_unchanged(key, source, target))
    }

    fn same_operation(&self, left: &SemanticOperation, right: &SemanticOperation) -> bool {
        if !left.operation_equivalent(right) {
            return false;
        }
        let (Ok(left), Ok(right)) = (left.evaluation_operands(), right.evaluation_operands())
        else {
            return false;
        };
        left.len() == right.len()
            && left
                .into_iter()
                .zip(right)
                .all(|(left, right)| self.same_argument(left, right))
    }

    fn same_argument(&self, left: &SemanticExpression, right: &SemanticExpression) -> bool {
        let left = Self::canonical_expression(left);
        let right = Self::canonical_expression(right);
        match (left, right) {
            (SemanticExpression::Register(left), SemanticExpression::Register(right)) => {
                self.graph().key(left) == self.graph().key(right)
            }
            (SemanticExpression::Literal(left), SemanticExpression::Literal(right)) => {
                left == right
            }
            (SemanticExpression::Operation(left), SemanticExpression::Operation(right)) => {
                self.same_operation(left, right)
            }
            (
                SemanticExpression::Select {
                    condition: left_condition,
                    when_true: left_true,
                    when_false: left_false,
                },
                SemanticExpression::Select {
                    condition: right_condition,
                    when_true: right_true,
                    when_false: right_false,
                },
            ) => {
                self.same_predicate(left_condition, right_condition)
                    && self.same_argument(left_true, right_true)
                    && self.same_argument(left_false, right_false)
            }
            _ => false,
        }
    }

    fn same_expression(&self, left: &SemanticExpression, right: &SemanticExpression) -> bool {
        self.same_argument(left, right)
    }

    fn expression_key(&self, value: &SemanticExpression) -> Option<SsaVar> {
        Self::canonical_expression(value)
            .as_register()
            .and_then(|register| self.graph().key(register))
    }

    fn canonical_expression(mut value: &SemanticExpression) -> &SemanticExpression {
        while let SemanticExpression::Operation(operation) = value {
            if !matches!(operation.insn_type, InsnType::Const | InsnType::Move)
                || operation.operands().len() != 1
            {
                break;
            }
            value = &operation.operands()[0];
        }
        value
    }

    fn same_predicate(
        &self,
        left: &crate::ir::SemanticPredicate,
        right: &crate::ir::SemanticPredicate,
    ) -> bool {
        use crate::ir::SemanticPredicate;

        match (left, right) {
            (SemanticPredicate::True, SemanticPredicate::True)
            | (SemanticPredicate::False, SemanticPredicate::False) => true,
            (SemanticPredicate::Test(left), SemanticPredicate::Test(right)) => {
                self.same_operation(left, right)
            }
            (SemanticPredicate::Not(left), SemanticPredicate::Not(right)) => {
                self.same_predicate(left, right)
            }
            (SemanticPredicate::And(left), SemanticPredicate::And(right))
            | (SemanticPredicate::Or(left), SemanticPredicate::Or(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| self.same_predicate(left, right))
            }
            _ => false,
        }
    }

    fn selection_key(&self, value: &SemanticExpression, ordinal: u32) -> SelectedValue {
        let mut value = value;
        while let SemanticExpression::Operation(operation) = value {
            if operation.insn_type != InsnType::Move || operation.operands().len() != 1 {
                break;
            }
            value = &operation.operands()[0];
        }
        if let Some(literal) = value.literal_value() {
            return SelectedValue::Literal(literal);
        }
        if let SemanticExpression::Register(register) = value {
            if let Some(key) = self.graph().key(register) {
                return SelectedValue::Variable(key);
            }
        }
        if let SemanticExpression::Operation(operation) = value {
            if operation.insn_type == InsnType::ConstStr {
                if let Some(value) = operation.payload.string_value.clone() {
                    return SelectedValue::String(value);
                }
            }
        }
        SelectedValue::Expression(ordinal)
    }

    fn expression_visible_at(&self, expression: &SemanticExpression, scope: &[u32]) -> bool {
        let mut expressions = vec![expression];
        let mut predicates = Vec::new();
        while let Some(expression) = expressions.pop() {
            match expression {
                SemanticExpression::Register(register) => {
                    if !self.register_visible_at(register, scope) {
                        return false;
                    }
                }
                SemanticExpression::Operation(operation) => {
                    let Ok(operands) = operation.evaluation_operands() else {
                        return false;
                    };
                    expressions.extend(operands);
                }
                SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                } => {
                    predicates.push(condition);
                    expressions.push(when_false);
                    expressions.push(when_true);
                }
                SemanticExpression::Literal(_) => {}
            }
        }
        while let Some(predicate) = predicates.pop() {
            match predicate {
                crate::ir::SemanticPredicate::Test(operation) => {
                    let Ok(operands) = operation.evaluation_operands() else {
                        return false;
                    };
                    expressions.extend(operands);
                }
                crate::ir::SemanticPredicate::Not(inner) => predicates.push(inner),
                crate::ir::SemanticPredicate::And(terms)
                | crate::ir::SemanticPredicate::Or(terms) => predicates.extend(terms),
                crate::ir::SemanticPredicate::True | crate::ir::SemanticPredicate::False => {}
            }
        }
        expressions
            .into_iter()
            .all(|expression| self.expression_visible_at(expression, scope))
    }

    fn register_visible_at(&self, register: &crate::ir::RegisterArg, scope: &[u32]) -> bool {
        let Some(key) = self.graph().key(register) else {
            return true;
        };
        self.graph()
            .definitions
            .get(&key)
            .is_none_or(|definitions| {
                definitions.iter().any(|definition| {
                    definition.scope.len() <= scope.len()
                        && definition
                            .scope
                            .iter()
                            .zip(scope)
                            .all(|(left, right)| left == right)
                })
            })
    }

    fn definition_depends_on(&self, definition: &DefinitionFact, key: SsaVar) -> bool {
        self.expression_depends_on(definition.expression(), key)
    }

    fn can_duplicate_definition_at(
        &self,
        definition: &DefinitionFact,
        usage: &UseFact,
        target: SsaVar,
    ) -> bool {
        let Some(operation) = definition.operation() else {
            return false;
        };
        if operation.insn_type != InsnType::Move
            || operation.operands().len() != 1
            || !matches!(operation.operands()[0], SemanticExpression::Register(_))
        {
            return false;
        }
        let (Some(source), Some(target_point)) = (
            definition
                .site
                .map(crate::ir::analysis::SemanticFlowPoint::before),
            usage.point,
        ) else {
            return false;
        };
        if !self.facts.reaching_supports(source, target_point) {
            return false;
        }
        self.expression_variables(definition.expression())
            .into_iter()
            .all(|key| key != target && self.facts.reaching_unchanged(key, source, target_point))
    }

    fn operation_depends_on(&self, operation: &SemanticOperation, key: SsaVar) -> bool {
        match operation.evaluation_operands() {
            Ok(operands) => operands
                .into_iter()
                .any(|operand| self.expression_depends_on(operand, key)),
            Err(_) => true,
        }
    }

    fn expression_depends_on(&self, expression: &SemanticExpression, key: SsaVar) -> bool {
        let mut expressions = vec![expression];
        let mut predicates = Vec::new();
        while let Some(expression) = expressions.pop() {
            match expression {
                SemanticExpression::Register(register)
                    if self.graph().key(register) == Some(key) =>
                {
                    return true;
                }
                SemanticExpression::Register(_) | SemanticExpression::Literal(_) => {}
                SemanticExpression::Operation(operation) => {
                    let Ok(operands) = operation.evaluation_operands() else {
                        return true;
                    };
                    expressions.extend(operands);
                }
                SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                } => {
                    predicates.push(condition);
                    expressions.push(when_false);
                    expressions.push(when_true);
                }
            }
        }
        predicates
            .into_iter()
            .any(|predicate| self.predicate_depends_on(predicate, key))
    }

    fn expression_variables(&self, expression: &SemanticExpression) -> BTreeSet<SsaVar> {
        let facts = SemanticExpressionFacts::of_expression(expression);
        match self.graph().identity() {
            ValueIdentity::Ssa => facts.used_ssa_variables().collect(),
            ValueIdentity::Source => facts
                .used_variables()
                .map(|variable| SsaVar::new(variable, 0))
                .collect(),
        }
    }

    fn predicate_depends_on(&self, predicate: &crate::ir::SemanticPredicate, key: SsaVar) -> bool {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                crate::ir::SemanticPredicate::Test(instruction) => {
                    if self.operation_depends_on(instruction, key) {
                        return true;
                    }
                }
                crate::ir::SemanticPredicate::Not(inner) => pending.push(inner),
                crate::ir::SemanticPredicate::And(terms)
                | crate::ir::SemanticPredicate::Or(terms) => pending.extend(terms),
                crate::ir::SemanticPredicate::True | crate::ir::SemanticPredicate::False => {}
            }
        }
        false
    }

    fn relocatable_definition_effect(definition: &DefinitionFact) -> Option<EffectSummary> {
        match definition.operation() {
            Some(operation) => Self::relocatable_effect(operation),
            None => {
                let effect = EffectSummary::expression(definition.expression());
                effect.can_relocate().then_some(effect)
            }
        }
    }

    fn selection_effect(definition: &DefinitionFact) -> EffectSummary {
        match definition.operation() {
            Some(operation) if operation.payload.edge_copy => {
                EffectSummary::operation_ignoring_edge_copy(operation)
            }
            _ => EffectSummary::expression(definition.expression()),
        }
    }

    fn relocatable_effect(instruction: &SemanticOperation) -> Option<EffectSummary> {
        if matches!(
            instruction.insn_type,
            InsnType::Phi | InsnType::Ternary | InsnType::NewInstance
        ) {
            return None;
        }
        let effect = if instruction.payload.edge_copy {
            if instruction.insn_type != InsnType::Move || instruction.operands().len() != 1 {
                return None;
            }
            EffectSummary::operation_ignoring_edge_copy(instruction)
        } else {
            EffectSummary::operation(instruction)
        };
        effect.can_relocate().then_some(effect)
    }

    fn phi_actions(&self, actions: &mut Vec<ValueAction>) {
        for phi in &self.graph().phis {
            let Some(replacement) = self.facts.canonical().get(&phi.result).cloned() else {
                continue;
            };
            if !self.facts.uses().contains_key(&phi.result)
                || matches!(self.graph().canonical_key(&replacement), Some(CanonicalKey::Value(value)) if value == phi.result)
            {
                continue;
            }
            actions.push(ValueAction::Propagate {
                event: usize::MAX,
                key: phi.result,
                replacement,
            });
        }
    }

    /// Substitute constants whose defining CFG instruction was intentionally
    /// omitted while constructing Semantic IR. Abrupt continuation folding can
    /// retain a terminal SSA use without retaining a bookkeeping `move`; SCCP
    /// remains the authoritative definition source for that value.
    fn cfg_constant_actions(&self, actions: &mut Vec<ValueAction>) {
        for (&key, replacement) in self.facts.canonical() {
            if self.graph().definitions.contains_key(&key)
                || !self.facts.uses().contains_key(&key)
                || !ValueFlowGraph::is_constant(replacement)
                || matches!(
                    self.graph().canonical_key(replacement),
                    Some(CanonicalKey::Value(value)) if value == key
                )
            {
                continue;
            }
            actions.push(ValueAction::Propagate {
                event: usize::MAX,
                key,
                replacement: replacement.clone(),
            });
        }
    }

    /// Reconnects semantic uses to SSA copy definitions omitted by structuring.
    /// Copy flow is lossless and has no evaluation-order constraints, so the
    /// transitive source is the canonical replacement.
    fn cfg_copy_actions(&self, actions: &mut Vec<ValueAction>) {
        for (result, source) in self.graph().copies.aliases() {
            if !self.graph().uses.contains_key(&result) {
                continue;
            }
            actions.push(ValueAction::Propagate {
                event: usize::MAX,
                key: result,
                replacement: self.graph().copies.argument(source),
            });
        }
    }
}

impl ValueAction {
    fn event(&self) -> usize {
        match self {
            Self::Propagate { event, .. }
            | Self::Inline { event, .. }
            | Self::InlineAt { event, .. }
            | Self::ReplaceAt { event, .. }
            | Self::EliminateStatements { event, .. }
            | Self::Remove { event, .. }
            | Self::DiscardResult { event, .. } => *event,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        analysis::SsaValueGraph, block::Block, ArgType, BlockId, EdgeKind, InsnNode, InvokeType,
        RegionId, RegisterArg, SemanticBlock, SemanticLoopControl, SemanticLoopKind,
        SemanticLoopTest, SemanticNode, SemanticPredicate, SemanticStatement, CFG,
    };

    fn register(value: SsaVar, ty: &ArgType) -> RegisterArg {
        RegisterArg::new_ssa(value.reg_num, value.version, ty.clone())
    }

    fn argument(value: SsaVar, ty: &ArgType) -> InsnArg {
        InsnArg::Reg(register(value, ty))
    }

    fn scheduled_replacements(name: &str, block: Block) -> BTreeSet<SsaVar> {
        let mut cfg = CFG::new(name);
        cfg.add_block(block);
        cfg.identify_instructions();
        let values = SsaValueGraph::build(&cfg).expect("SSA graph");
        let statements = cfg
            .block(BlockId::new(0))
            .expect("entry block")
            .insns
            .iter()
            .cloned()
            .map(|instruction| SemanticStatement::instruction(instruction).expect("semantic op"))
            .collect();
        let mut root = SemanticNode::BasicBlock(SemanticBlock {
            id: BlockId::new(0),
            statements,
        });
        crate::ir::SemanticSiteNumbering::assign(&mut root).expect("semantic sites");

        let graph = ValueFlowGraph::build(&root, &values, &BTreeMap::new()).expect("value graph");
        graph
            .schedule(RecoveryMode::Full)
            .expect("value plan")
            .actions
            .iter()
            .filter_map(ValuePlanner::replacement_key)
            .collect()
    }

    #[test]
    fn defers_transitive_alias_across_effectful_producer() {
        let array_type = ArgType::object_array();
        let allocation = SsaVar::new(10, 0);
        let first_alias = SsaVar::new(14, 0);
        let second_alias = SsaVar::new(9, 0);

        let mut block = Block::new(0u32);
        block.push(InsnNode::new_array(
            register(allocation, &array_type),
            InsnArg::lit(1, ArgType::INT),
            0,
        ));
        block.push(InsnNode::mov(
            register(first_alias, &array_type),
            argument(allocation, &array_type),
        ));
        block.push(InsnNode::aput(
            InsnArg::lit(0, ArgType::object("java/lang/Object")),
            argument(first_alias, &array_type),
            InsnArg::lit(0, ArgType::INT),
        ));
        block.push(InsnNode::mov(
            register(second_alias, &array_type),
            argument(first_alias, &array_type),
        ));
        block.push(InsnNode::invoke(
            InvokeType::Static,
            0,
            vec![argument(second_alias, &array_type)],
        ));

        let scheduled = scheduled_replacements("allocation_alias_fork", block);

        assert!(scheduled.contains(&allocation));
        assert!(!scheduled.contains(&first_alias));
        assert!(!scheduled.contains(&second_alias));
    }

    #[test]
    fn keeps_linear_alias_chain_with_effectful_producer() {
        let array_type = ArgType::object_array();
        let allocation = SsaVar::new(10, 0);
        let first_alias = SsaVar::new(14, 0);
        let second_alias = SsaVar::new(9, 0);

        let mut block = Block::new(0u32);
        block.push(InsnNode::new_array(
            register(allocation, &array_type),
            InsnArg::lit(1, ArgType::INT),
            0,
        ));
        block.push(InsnNode::mov(
            register(first_alias, &array_type),
            argument(allocation, &array_type),
        ));
        block.push(InsnNode::mov(
            register(second_alias, &array_type),
            argument(first_alias, &array_type),
        ));
        block.push(InsnNode::invoke(
            InvokeType::Static,
            0,
            vec![argument(second_alias, &array_type)],
        ));

        let scheduled = scheduled_replacements("allocation_alias_chain", block);

        assert!(scheduled.contains(&allocation));
        assert!(scheduled.contains(&first_alias));
        assert!(scheduled.contains(&second_alias));
    }

    #[test]
    fn defers_effectful_phi_replacement_entering_loop() {
        let array_type = ArgType::object_array();
        let allocation = SsaVar::new(10, 0);
        let initial_alias = SsaVar::new(14, 0);
        let loop_value = SsaVar::new(14, 1);
        let body_alias = SsaVar::new(9, 0);
        let backedge_alias = SsaVar::new(14, 2);

        let mut preheader = Block::new(0u32);
        preheader.push(InsnNode::new_array(
            register(allocation, &array_type),
            InsnArg::lit(1, ArgType::INT),
            0,
        ));
        preheader.push(InsnNode::mov(
            register(initial_alias, &array_type),
            argument(allocation, &array_type),
        ));

        let mut header = Block::new(1u32);
        header.push(InsnNode::phi(
            register(loop_value, &array_type),
            vec![
                (0, argument(initial_alias, &array_type)),
                (2, argument(backedge_alias, &array_type)),
            ],
        ));

        let mut body = Block::new(2u32);
        body.push(InsnNode::mov(
            register(body_alias, &array_type),
            argument(loop_value, &array_type),
        ));
        body.push(InsnNode::invoke(
            InvokeType::Static,
            0,
            vec![argument(body_alias, &array_type)],
        ));
        body.push(InsnNode::mov(
            register(backedge_alias, &array_type),
            argument(body_alias, &array_type),
        ));

        let mut cfg = CFG::new("effectful_loop_invariant");
        cfg.add_block(preheader);
        cfg.add_block(header);
        cfg.add_block(body);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(1), BlockId::new(2), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(2), BlockId::new(1), EdgeKind::Normal);
        cfg.identify_instructions();
        let values = SsaValueGraph::build(&cfg).expect("SSA graph");
        let semantic_block = |id| {
            SemanticNode::BasicBlock(SemanticBlock {
                id,
                statements: cfg
                    .block(id)
                    .expect("semantic block")
                    .insns
                    .iter()
                    .filter(|instruction| instruction.insn_type != InsnType::Phi)
                    .cloned()
                    .map(|instruction| {
                        SemanticStatement::instruction(instruction).expect("semantic op")
                    })
                    .collect(),
            })
        };
        let mut root = SemanticNode::sequence([
            semantic_block(BlockId::new(0)),
            SemanticNode::Loop {
                control: SemanticLoopControl::Region(RegionId::new(1)),
                header: Some(BlockId::new(1)),
                kind: SemanticLoopKind::Endless,
                test: SemanticLoopTest::pure(SemanticPredicate::True),
                body: Box::new(semantic_block(BlockId::new(2))),
            },
        ]);
        crate::ir::SemanticSiteNumbering::assign(&mut root).expect("semantic sites");

        let graph = ValueFlowGraph::build(&root, &values, &BTreeMap::new()).expect("value graph");
        let scheduled = graph
            .schedule(RecoveryMode::Full)
            .expect("value plan")
            .actions
            .iter()
            .filter_map(ValuePlanner::replacement_key)
            .collect::<BTreeSet<_>>();

        assert!(scheduled.contains(&allocation));
        assert!(!scheduled.contains(&loop_value));
    }
}
