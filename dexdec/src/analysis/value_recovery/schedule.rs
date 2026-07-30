use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::SsaVar, IfOp, InsnType, RegisterArg, SemanticExpression, SemanticExpressionTransform,
    SemanticFolder, SemanticInstructions, SemanticNode, SemanticOperation, SemanticPredicate,
    SemanticStatementKind,
};

use super::flow::{UseSite, ValueAction, ValueIdentity};
use super::ValueRecoveryError;

pub(super) struct ValueSchedule {
    identity: ValueIdentity,
    replacements: BTreeMap<SsaVar, SemanticExpression>,
    site_replacements: BTreeMap<UseSite, BTreeMap<SsaVar, SiteReplacement>>,
    removals: BTreeSet<SsaVar>,
    statement_removals: BTreeSet<crate::ir::SemanticSiteId>,
    discarded_results: BTreeSet<SsaVar>,
    changed: bool,
}

struct SiteReplacement {
    value: SemanticExpression,
}

impl ValueSchedule {
    pub(super) fn compile(
        actions: impl IntoIterator<Item = ValueAction>,
        identity: ValueIdentity,
    ) -> Result<Self, ValueRecoveryError> {
        let mut schedule = Self {
            identity,
            replacements: BTreeMap::new(),
            site_replacements: BTreeMap::new(),
            removals: BTreeSet::new(),
            statement_removals: BTreeSet::new(),
            discarded_results: BTreeSet::new(),
            changed: false,
        };
        for action in actions {
            match action {
                ValueAction::Propagate {
                    key, replacement, ..
                } => {
                    schedule
                        .replacements
                        .insert(key, SemanticExpression::from_argument(replacement)?);
                }
                ValueAction::Inline {
                    key, expression, ..
                } => {
                    schedule.replacements.insert(key, expression);
                }
                ValueAction::InlineAt {
                    key,
                    remove_key,
                    remove_definitions,
                    replacements,
                    ..
                } => {
                    if remove_key {
                        schedule.removals.insert(key);
                    }
                    schedule.statement_removals.extend(remove_definitions);
                    for (site, expression) in replacements {
                        schedule.site_replacements.entry(site).or_default().insert(
                            key,
                            SiteReplacement {
                                value: expression.value,
                            },
                        );
                    }
                }
                ValueAction::ReplaceAt {
                    key, replacements, ..
                } => {
                    for (site, value) in replacements {
                        schedule.site_replacements.entry(site).or_default().insert(
                            key,
                            SiteReplacement {
                                value: SemanticExpression::from_argument(value)?,
                            },
                        );
                    }
                }
                ValueAction::EliminateStatements { statements, .. } => {
                    schedule.statement_removals.extend(statements);
                }
                ValueAction::Remove { key, .. } => {
                    schedule.removals.insert(key);
                }
                ValueAction::DiscardResult { key, .. } => {
                    schedule.discarded_results.insert(key);
                }
            }
        }
        schedule.canonicalize()?;
        Ok(schedule)
    }

    pub(super) fn apply(mut self, root: &mut SemanticNode) -> Result<bool, ValueRecoveryError> {
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = self.fold_node(body)?;
        Ok(self.changed)
    }

    fn canonicalize(&mut self) -> Result<(), ValueRecoveryError> {
        let cyclic = ReplacementGraph::new(&self.replacements, self.identity)?.cyclic_values();
        self.replacements.retain(|key, _| !cyclic.contains(key));
        let raw = std::mem::take(&mut self.replacements);
        let keys = raw.keys().copied().collect::<BTreeSet<_>>();
        let dependencies = raw
            .iter()
            .map(|(key, value)| {
                let dependencies = ExpressionDependencies::collect(value, self.identity)?
                    .into_iter()
                    .filter(|dependency| keys.contains(dependency))
                    .collect::<BTreeSet<_>>();
                Ok((*key, dependencies))
            })
            .collect::<Result<BTreeMap<_, _>, ValueRecoveryError>>()?;
        let mut successors = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        let mut indegree = BTreeMap::<SsaVar, usize>::new();
        for key in &keys {
            indegree.insert(*key, dependencies.get(key).map(BTreeSet::len).unwrap_or(0));
        }
        for (key, inputs) in &dependencies {
            for input in inputs {
                successors.entry(*input).or_default().insert(*key);
            }
        }
        let mut ready = indegree
            .iter()
            .filter_map(|(key, degree)| (*degree == 0).then_some(*key))
            .collect::<BTreeSet<_>>();
        let mut canonical = BTreeMap::new();
        while let Some(key) = ready.pop_first() {
            let value = ExpressionDependencies::substitute(
                raw.get(&key)
                    .cloned()
                    .ok_or(ValueRecoveryError::MissingReplacement(key))?,
                &canonical,
                self.identity,
            )?;
            canonical.insert(key, value);
            for successor in successors.get(&key).into_iter().flatten() {
                let degree = indegree
                    .get_mut(successor)
                    .ok_or(ValueRecoveryError::MissingDependency(*successor))?;
                *degree -= 1;
                if *degree == 0 {
                    ready.insert(*successor);
                }
            }
        }
        debug_assert_eq!(canonical.len(), keys.len());
        for replacements in self.site_replacements.values_mut() {
            for replacement in replacements.values_mut() {
                replacement.value = ExpressionDependencies::substitute(
                    replacement.value.clone(),
                    &canonical,
                    self.identity,
                )?;
            }
        }
        let required = canonical
            .values()
            .chain(self.site_replacements.values().flat_map(|replacements| {
                replacements.values().map(|replacement| &replacement.value)
            }))
            .map(|value| ExpressionDependencies::collect(value, self.identity))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .filter(|dependency| !canonical.contains_key(dependency))
            .collect::<BTreeSet<_>>();
        self.removals.retain(|value| !required.contains(value));
        self.discarded_results
            .retain(|value| !required.contains(value));
        self.changed |= !canonical.is_empty();
        self.changed |= !self.site_replacements.is_empty();
        self.removals.extend(canonical.keys().copied());
        self.replacements = canonical;
        Ok(())
    }

    fn apply_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, ValueRecoveryError> {
        let mut substitution = ValueSubstitution {
            replacements: &self.replacements,
            discarded_results: &self.discarded_results,
            identity: self.identity,
            changed: false,
        };
        SemanticInstructions::transform_node(&mut node, &mut substitution)?;
        self.changed |= substitution.changed;
        match &mut node {
            SemanticNode::BasicBlock(block) => {
                for statement in &mut block.statements {
                    self.apply_statement_site(statement)?;
                }
            }
            SemanticNode::For {
                init,
                condition,
                update,
                ..
            } => {
                self.apply_statement_site(init)?;
                self.apply_predicate_site(condition)?;
                self.apply_statement_site(update)?;
            }
            SemanticNode::If { condition, .. } => {
                self.apply_predicate_site(condition)?;
            }
            SemanticNode::Loop { test, .. } => {
                self.apply_predicate_site(&mut test.condition)?;
            }
            SemanticNode::ForEach { iterable, .. } => {
                self.apply_expression_site(iterable)?;
            }
            SemanticNode::Switch { selector, .. } => {
                self.apply_expression_site(selector)?;
            }
            SemanticNode::Synchronized { lock, .. } => {
                self.apply_expression_site(lock)?;
            }
            _ => {}
        }
        if let SemanticNode::Leave(leave) = &mut node {
            if let Some(replacements) = leave
                .site
                .and_then(|site| self.site_replacements.get(&UseSite::Leave(site)))
            {
                if let Some(value) = leave.value_mut() {
                    let mut substitution = SiteSubstitution {
                        replacements,
                        identity: self.identity,
                        changed: false,
                    };
                    SemanticInstructions::transform_expression(value, &mut substitution)?;
                    self.changed |= substitution.changed;
                }
            }
        }
        if let SemanticNode::BasicBlock(block) = &mut node {
            let before = block.statements.len();
            block.statements.retain(|statement| {
                if statement
                    .site
                    .is_some_and(|site| self.statement_removals.contains(&site))
                {
                    return false;
                }
                statement
                    .result()
                    .and_then(|register| self.identity.key(register))
                    .is_none_or(|key| !self.removals.contains(&key))
            });
            self.changed |= block.statements.len() != before;
        }
        Ok(node)
    }

    fn apply_statement_site(
        &mut self,
        statement: &mut crate::ir::SemanticStatement,
    ) -> Result<(), ValueRecoveryError> {
        let Some(site) = statement.site else {
            return Ok(());
        };
        match &mut statement.kind {
            SemanticStatementKind::Instruction(instruction) => {
                let mut expression = SemanticExpression::Operation(Box::new(instruction.clone()));
                if let Some(replacements) = self.site_replacements.get(&UseSite::Statement(site)) {
                    let mut substitution = SiteSubstitution {
                        replacements,
                        identity: self.identity,
                        changed: false,
                    };
                    SemanticInstructions::transform_expression(&mut expression, &mut substitution)?;
                    self.changed |= substitution.changed;
                }
                let (expression, reduced) =
                    SemanticExpressionReduction::new(self.identity).reduce(expression)?;
                let SemanticExpression::Operation(operation) = expression else {
                    return Err(crate::ir::SemanticFoldError::NonOperationStatement.into());
                };
                *instruction = *operation;
                self.changed |= reduced;
            }
            SemanticStatementKind::Definition { value, .. } => {
                self.apply_selected_value_sites(site, value)?;
                let (reduced, changed) =
                    SemanticExpressionReduction::new(self.identity).reduce(value.clone())?;
                *value = reduced;
                self.changed |= changed;
            }
        }
        Ok(())
    }

    fn apply_selected_value_sites(
        &mut self,
        site: crate::ir::SemanticSiteId,
        value: &mut SemanticExpression,
    ) -> Result<(), ValueRecoveryError> {
        let mut pending = vec![value];
        let mut argument_occurrence = 0u32;
        let mut predicate_occurrence = 0u32;
        while let Some(value) = pending.pop() {
            match value {
                SemanticExpression::Register(_)
                | SemanticExpression::Literal(_)
                | SemanticExpression::Operation(_) => {
                    let current = argument_occurrence;
                    argument_occurrence += 1;
                    let Some(replacements) = self
                        .site_replacements
                        .get(&UseSite::SelectedArgument(site, current))
                    else {
                        continue;
                    };
                    let mut substitution = SiteSubstitution {
                        replacements,
                        identity: self.identity,
                        changed: false,
                    };
                    SemanticInstructions::transform_expression(value, &mut substitution)?;
                    self.changed |= substitution.changed;
                }
                SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                } => {
                    let current = predicate_occurrence;
                    predicate_occurrence += 1;
                    if let Some(replacements) = self
                        .site_replacements
                        .get(&UseSite::SelectedPredicate(site, current))
                    {
                        let mut substitution = SiteSubstitution {
                            replacements,
                            identity: self.identity,
                            changed: false,
                        };
                        SemanticInstructions::transform_predicate(condition, &mut substitution)?;
                        self.changed |= substitution.changed;
                    }
                    pending.push(when_false);
                    pending.push(when_true);
                }
            }
        }
        Ok(())
    }

    fn apply_predicate_site(
        &mut self,
        predicate: &mut crate::ir::SemanticOperand<SemanticPredicate>,
    ) -> Result<(), ValueRecoveryError> {
        let Some(replacements) = predicate
            .site
            .and_then(|site| self.site_replacements.get(&UseSite::Predicate(site)))
        else {
            return Ok(());
        };
        let mut substitution = SiteSubstitution {
            replacements,
            identity: self.identity,
            changed: false,
        };
        SemanticInstructions::transform_predicate(predicate, &mut substitution)?;
        self.changed |= substitution.changed;
        Ok(())
    }

    fn apply_expression_site(
        &mut self,
        argument: &mut crate::ir::SemanticOperand<SemanticExpression>,
    ) -> Result<(), ValueRecoveryError> {
        let Some(replacements) = argument
            .site
            .and_then(|site| self.site_replacements.get(&UseSite::Argument(site)))
        else {
            return Ok(());
        };
        let mut substitution = SiteSubstitution {
            replacements,
            identity: self.identity,
            changed: false,
        };
        SemanticInstructions::transform_expression(&mut argument.value, &mut substitution)?;
        self.changed |= substitution.changed;
        Ok(())
    }
}

struct SemanticExpressionReduction {
    identity: ValueIdentity,
}

impl SemanticExpressionReduction {
    fn new(identity: ValueIdentity) -> Self {
        Self { identity }
    }

    fn reduce(
        &self,
        value: SemanticExpression,
    ) -> Result<(SemanticExpression, bool), ValueRecoveryError> {
        let mut pending = vec![ValueReductionTask::Visit(value)];
        let mut results = Vec::<SemanticExpression>::new();
        let mut changed = false;
        while let Some(task) = pending.pop() {
            match task {
                ValueReductionTask::Visit(
                    expression @ (SemanticExpression::Register(_) | SemanticExpression::Literal(_)),
                ) => results.push(expression),
                ValueReductionTask::Visit(SemanticExpression::Operation(operation)) => {
                    let (instruction, operands, compound_target) = operation.into_parts();
                    pending.push(ValueReductionTask::Operation {
                        instruction,
                        operand_count: operands.len(),
                        has_compound_target: compound_target.is_some(),
                    });
                    pending.extend(
                        operands
                            .into_iter()
                            .chain(compound_target)
                            .rev()
                            .map(ValueReductionTask::Visit),
                    );
                }
                ValueReductionTask::Visit(SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                }) => {
                    pending.push(ValueReductionTask::Select(condition));
                    pending.push(ValueReductionTask::Visit(*when_false));
                    pending.push(ValueReductionTask::Visit(*when_true));
                }
                ValueReductionTask::Select(condition) => {
                    let when_false = results
                        .pop()
                        .ok_or(crate::ir::SemanticFoldError::MalformedWorkStack)?;
                    let when_true = results
                        .pop()
                        .ok_or(crate::ir::SemanticFoldError::MalformedWorkStack)?;
                    if let Some(value) = condition.constant_value() {
                        results.push(if value { when_true } else { when_false });
                        changed = true;
                    } else if self.equivalent(&when_true, &when_false) {
                        results.push(when_true);
                        changed = true;
                    } else {
                        results.push(SemanticExpression::select(condition, when_true, when_false));
                    }
                }
                ValueReductionTask::Operation {
                    instruction,
                    operand_count,
                    has_compound_target,
                } => {
                    let count = operand_count + usize::from(has_compound_target);
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(crate::ir::SemanticFoldError::MalformedWorkStack)?;
                    let (operands, compound_target) = {
                        let mut children = results.drain(start..);
                        let operands = children.by_ref().take(operand_count).collect();
                        let compound_target =
                            has_compound_target.then(|| children.next()).flatten();
                        (operands, compound_target)
                    };
                    if has_compound_target && compound_target.is_none() {
                        return Err(crate::ir::SemanticFoldError::MalformedWorkStack.into());
                    }
                    results.push(SemanticExpression::Operation(Box::new(
                        SemanticOperation::from_parts(instruction, operands, compound_target),
                    )));
                }
            }
        }
        if results.len() != 1 {
            return Err(crate::ir::SemanticFoldError::MalformedWorkStack.into());
        }
        Ok((
            results
                .pop()
                .ok_or(crate::ir::SemanticFoldError::MalformedWorkStack)?,
            changed,
        ))
    }

    fn select(
        condition: SemanticPredicate,
        when_true: SemanticExpression,
        when_false: SemanticExpression,
    ) -> (SemanticExpression, bool) {
        match condition.constant_value() {
            Some(true) => (when_true, true),
            Some(false) => (when_false, true),
            None => {
                if let Some(equal_when_true) =
                    Self::stable_equality_selection(&condition, &when_true, &when_false)
                {
                    return if equal_when_true {
                        (when_false, true)
                    } else {
                        (when_true, true)
                    };
                }
                (
                    SemanticExpression::select(condition, when_true, when_false),
                    false,
                )
            }
        }
    }

    fn stable_equality_selection(
        condition: &SemanticPredicate,
        when_true: &SemanticExpression,
        when_false: &SemanticExpression,
    ) -> Option<bool> {
        let (equal_when_true, left, right) = Self::stable_equality_test(condition, true)?;
        let aligned = (when_true.same_stable_value(left) && when_false.same_stable_value(right))
            || (when_true.same_stable_value(right) && when_false.same_stable_value(left));
        aligned.then_some(equal_when_true)
    }

    fn stable_equality_test(
        condition: &SemanticPredicate,
        polarity: bool,
    ) -> Option<(bool, &SemanticExpression, &SemanticExpression)> {
        match condition {
            SemanticPredicate::Not(inner) => Self::stable_equality_test(inner, !polarity),
            SemanticPredicate::Test(test) if test.insn_type == InsnType::If => {
                let equal_when_true = match test.payload.if_op? {
                    IfOp::Eq => polarity,
                    IfOp::Ne => !polarity,
                    IfOp::Lt | IfOp::Ge | IfOp::Gt | IfOp::Le => return None,
                };
                let [left, right] = test.operands() else {
                    return None;
                };
                Some((equal_when_true, left, right))
            }
            SemanticPredicate::True
            | SemanticPredicate::False
            | SemanticPredicate::And(_)
            | SemanticPredicate::Or(_)
            | SemanticPredicate::Test(_) => None,
        }
    }

    fn equivalent(&self, left: &SemanticExpression, right: &SemanticExpression) -> bool {
        let mut pending = vec![(left, right)];
        while let Some((left, right)) = pending.pop() {
            match (left, right) {
                (SemanticExpression::Register(left), SemanticExpression::Register(right)) => {
                    let equivalent = match (self.identity.key(left), self.identity.key(right)) {
                        (Some(left), Some(right)) => left == right,
                        (None, None) => {
                            left.reg_num == right.reg_num
                                && left.ssa_version == right.ssa_version
                                && left.code_var == right.code_var
                        }
                        _ => false,
                    };
                    if !equivalent {
                        return false;
                    }
                }
                (SemanticExpression::Literal(left), SemanticExpression::Literal(right))
                    if left == right => {}
                (SemanticExpression::Operation(left), SemanticExpression::Operation(right)) => {
                    if !left.operation_equivalent(right)
                        || left.operands().len() != right.operands().len()
                        || left.compound_target().is_some() != right.compound_target().is_some()
                    {
                        return false;
                    }
                    pending.extend(left.operands().iter().zip(right.operands()));
                    if let (Some(left), Some(right)) =
                        (left.compound_target(), right.compound_target())
                    {
                        pending.push((left, right));
                    }
                }
                (SemanticExpression::Select { .. }, SemanticExpression::Select { .. }) => {
                    return false;
                }
                _ => return false,
            }
        }
        true
    }
}

enum ValueReductionTask {
    Visit(SemanticExpression),
    Select(SemanticPredicate),
    Operation {
        instruction: crate::ir::InsnNode,
        operand_count: usize,
        has_compound_target: bool,
    },
}

struct ReplacementGraph {
    edges: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
    reverse: BTreeMap<SsaVar, BTreeSet<SsaVar>>,
}

impl ReplacementGraph {
    fn new(
        replacements: &BTreeMap<SsaVar, SemanticExpression>,
        identity: ValueIdentity,
    ) -> Result<Self, ValueRecoveryError> {
        let nodes = replacements.keys().copied().collect::<BTreeSet<_>>();
        let edges = replacements
            .iter()
            .map(|(key, replacement)| {
                let dependencies = ExpressionDependencies::collect(replacement, identity)?
                    .into_iter()
                    .filter(|dependency| nodes.contains(dependency))
                    .collect::<BTreeSet<_>>();
                Ok((*key, dependencies))
            })
            .collect::<Result<BTreeMap<_, _>, ValueRecoveryError>>()?;
        let mut reverse = nodes
            .iter()
            .copied()
            .map(|node| (node, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for (source, targets) in &edges {
            for target in targets {
                reverse.entry(*target).or_default().insert(*source);
            }
        }
        Ok(Self { edges, reverse })
    }

    fn cyclic_values(&self) -> BTreeSet<SsaVar> {
        let mut visited = BTreeSet::new();
        let mut finish = Vec::new();
        for node in self.edges.keys().copied() {
            self.finish_from(node, &mut visited, &mut finish);
        }

        visited.clear();
        let mut cyclic = BTreeSet::new();
        for node in finish.into_iter().rev() {
            if visited.contains(&node) {
                continue;
            }
            let component = self.component_from(node, &mut visited);
            let self_edge = component.len() == 1
                && self
                    .edges
                    .get(&node)
                    .is_some_and(|targets| targets.contains(&node));
            if component.len() > 1 || self_edge {
                cyclic.extend(component);
            }
        }
        cyclic
    }

    fn finish_from(&self, start: SsaVar, visited: &mut BTreeSet<SsaVar>, finish: &mut Vec<SsaVar>) {
        let mut pending = vec![(start, false)];
        while let Some((node, exiting)) = pending.pop() {
            if exiting {
                finish.push(node);
                continue;
            }
            if !visited.insert(node) {
                continue;
            }
            pending.push((node, true));
            pending.extend(
                self.edges
                    .get(&node)
                    .into_iter()
                    .flatten()
                    .rev()
                    .copied()
                    .map(|target| (target, false)),
            );
        }
    }

    fn component_from(&self, start: SsaVar, visited: &mut BTreeSet<SsaVar>) -> BTreeSet<SsaVar> {
        let mut component = BTreeSet::new();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if !visited.insert(node) {
                continue;
            }
            component.insert(node);
            pending.extend(self.reverse.get(&node).into_iter().flatten().rev().copied());
        }
        component
    }
}

impl SemanticFolder for ValueSchedule {
    type Error = ValueRecoveryError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        self.apply_node(node)
    }
}

struct ExpressionDependencies;

impl ExpressionDependencies {
    fn collect(
        value: &SemanticExpression,
        identity: ValueIdentity,
    ) -> Result<BTreeSet<SsaVar>, ValueRecoveryError> {
        let mut values = BTreeSet::new();
        let mut expressions = vec![value];
        let mut predicates = Vec::new();
        while let Some(expression) = expressions.pop() {
            match expression {
                SemanticExpression::Register(register) => {
                    values.extend(identity.key(register));
                }
                SemanticExpression::Operation(operation) => {
                    expressions.extend(operation.evaluation_operands()?);
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
                SemanticPredicate::Test(operation) => {
                    for operand in operation.evaluation_operands()? {
                        values.extend(Self::collect(operand, identity)?);
                    }
                }
                SemanticPredicate::Not(inner) => predicates.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    predicates.extend(terms);
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
        Ok(values)
    }

    fn substitute(
        mut value: SemanticExpression,
        replacements: &BTreeMap<SsaVar, SemanticExpression>,
        identity: ValueIdentity,
    ) -> Result<SemanticExpression, crate::ir::SemanticFoldError> {
        let discarded_results = BTreeSet::new();
        SemanticInstructions::transform_expression(
            &mut value,
            &mut ValueSubstitution {
                replacements,
                discarded_results: &discarded_results,
                identity,
                changed: false,
            },
        )?;
        Ok(value)
    }
}

struct ValueSubstitution<'a> {
    replacements: &'a BTreeMap<SsaVar, SemanticExpression>,
    discarded_results: &'a BTreeSet<SsaVar>,
    identity: ValueIdentity,
    changed: bool,
}

struct SiteSubstitution<'a> {
    replacements: &'a BTreeMap<SsaVar, SiteReplacement>,
    identity: ValueIdentity,
    changed: bool,
}

impl SemanticExpressionTransform for SiteSubstitution<'_> {
    fn transform_register(&mut self, register: RegisterArg) -> SemanticExpression {
        let replacement = self
            .identity
            .key(&register)
            .and_then(|key| self.replacements.get(&key))
            .map(|replacement| replacement.value.clone());
        self.changed |= replacement.is_some();
        replacement.unwrap_or(SemanticExpression::Register(register))
    }

    fn transform_select(
        &mut self,
        condition: SemanticPredicate,
        when_true: SemanticExpression,
        when_false: SemanticExpression,
    ) -> SemanticExpression {
        let (expression, changed) =
            SemanticExpressionReduction::select(condition, when_true, when_false);
        self.changed |= changed;
        expression
    }
}

impl SemanticExpressionTransform for ValueSubstitution<'_> {
    fn transform_register(&mut self, register: RegisterArg) -> SemanticExpression {
        let replacement = self
            .identity
            .key(&register)
            .and_then(|key| self.replacements.get(&key))
            .cloned();
        self.changed |= replacement.is_some();
        replacement.unwrap_or(SemanticExpression::Register(register))
    }

    fn transform_operation(&mut self, mut operation: SemanticOperation) -> SemanticExpression {
        let discard = operation
            .result
            .as_ref()
            .and_then(|register| self.identity.key(register))
            .is_some_and(|key| self.discarded_results.contains(&key));
        if discard {
            operation.discard_result();
            self.changed = true;
        }
        SemanticExpression::Operation(Box::new(operation))
    }

    fn transform_select(
        &mut self,
        condition: SemanticPredicate,
        when_true: SemanticExpression,
        when_false: SemanticExpression,
    ) -> SemanticExpression {
        let (expression, changed) =
            SemanticExpressionReduction::select(condition, when_true, when_false);
        self.changed |= changed;
        expression
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ArgType, InsnArg, InsnNode, InsnType};

    #[test]
    fn strongly_connected_replacements_keep_their_definitions() {
        let first = SsaVar::new(0, 0);
        let second = SsaVar::new(0, 1);
        let dependent = SsaVar::new(1, 0);
        let register = |value: SsaVar| InsnArg::reg_ssa(value.reg_num, value.version, ArgType::INT);
        let schedule = ValueSchedule::compile(
            [
                ValueAction::Propagate {
                    event: 0,
                    key: first,
                    replacement: register(second),
                },
                ValueAction::Propagate {
                    event: 1,
                    key: second,
                    replacement: register(first),
                },
                ValueAction::Propagate {
                    event: 2,
                    key: dependent,
                    replacement: register(first),
                },
            ],
            ValueIdentity::Ssa,
        )
        .unwrap();

        assert!(!schedule.replacements.contains_key(&first));
        assert!(!schedule.replacements.contains_key(&second));
        assert!(!schedule.removals.contains(&first));
        assert!(!schedule.removals.contains(&second));
        assert_eq!(
            schedule
                .replacements
                .get(&dependent)
                .and_then(SemanticExpression::as_register)
                .and_then(SsaVar::from_reg),
            Some(first)
        );
        assert!(schedule.removals.contains(&dependent));
    }

    #[test]
    fn constructor_receiver_is_not_an_expression_dependency() {
        let result = SsaVar::new(0, 0);
        let first = SsaVar::new(1, 0);
        let second = SsaVar::new(2, 0);
        let object = ArgType::object("example/Value");
        let register =
            |value: SsaVar, ty: ArgType| InsnArg::reg_ssa(value.reg_num, value.version, ty);
        let mut constructor = InsnNode::new(InsnType::Constructor, 3);
        constructor.set_result(RegisterArg::new_ssa(
            result.reg_num,
            result.version,
            object.clone(),
        ));
        constructor.add_arg(register(result, object));
        constructor.add_arg(register(first, ArgType::INT));
        constructor.add_arg(register(second, ArgType::INT));

        let expression = SemanticExpression::from_argument(InsnArg::wrap(constructor)).unwrap();
        let dependencies =
            ExpressionDependencies::collect(&expression, ValueIdentity::Ssa).unwrap();

        assert_eq!(dependencies, BTreeSet::from([first, second]));
    }

    #[test]
    fn replacement_dependencies_remain_live() {
        let value = SsaVar::new(0, 0);
        let dependency = SsaVar::new(1, 0);
        let mut expression = InsnNode::mov(
            RegisterArg::new_ssa(value.reg_num, value.version, ArgType::INT),
            InsnArg::reg_ssa(dependency.reg_num, dependency.version, ArgType::INT),
        );
        expression.payload.edge_copy = true;

        let schedule = ValueSchedule::compile(
            [
                ValueAction::Inline {
                    event: 0,
                    key: value,
                    expression: SemanticExpression::Operation(Box::new(
                        SemanticOperation::from_instruction(expression).unwrap(),
                    )),
                },
                ValueAction::DiscardResult {
                    event: 1,
                    key: dependency,
                },
            ],
            ValueIdentity::Ssa,
        )
        .unwrap();

        assert!(!schedule.discarded_results.contains(&dependency));
    }
}
