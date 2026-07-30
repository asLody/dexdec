//! Path-sensitive predicate reduction for Kotlin control syntax.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::bdd::{Bdd, BddContext};
use crate::ir::semantic::{CompletionDomain, CompletionInterpreter, SemanticTransfer};
use crate::ir::{
    analysis::{SourceTypeEnvironment, SsaVar},
    ArgType, BoolExpr, BoolVariable, IfOp, InsnType, InstructionId, SemanticCatch,
    SemanticExpression, SemanticExpressionTransform, SemanticFinally, SemanticFoldError,
    SemanticInstructions, SemanticLabel, SemanticLeave, SemanticLoopControl, SemanticLoopKind,
    SemanticNode, SemanticOperation, SemanticPredicate, SemanticStatementKind, SemanticSwitchCase,
    SemanticVisitor,
};

pub(super) struct PathConditionSyntax;

impl PathConditionSyntax {
    pub(super) fn apply(
        &self,
        root: &mut SemanticNode,
        types: &SourceTypeEnvironment,
    ) -> Result<bool, SemanticFoldError> {
        let catalog = PredicateCatalog::collect(root);
        let domain = PathConditionDomain::new(catalog, types);
        let body = std::mem::replace(root, SemanticNode::Empty);
        let original = body.clone();
        let mut reduction = PathConditionReduction::new(domain);
        match reduction.apply(body) {
            Ok(reduced) => {
                *root = reduced;
                Ok(reduction.changed)
            }
            Err(SemanticFoldError::BooleanDomain(source)) if source.is_resource_limit() => {
                *root = original;
                Ok(false)
            }
            Err(error) => {
                *root = original;
                Err(error)
            }
        }
    }
}

struct PredicateCatalog {
    symbols: BTreeSet<BoolVariable>,
    tests: BTreeMap<InstructionId, crate::ir::SemanticOperation>,
    occurrences: BTreeMap<InstructionId, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ComparisonValue {
    Ssa(SsaVar),
    Literal(i64, ArgType),
}

impl ComparisonValue {
    fn analyze(mut value: &SemanticExpression) -> Option<Self> {
        while let SemanticExpression::Operation(operation) = value {
            if !matches!(operation.insn_type, InsnType::Const | InsnType::Move)
                || operation.operands().len() != 1
            {
                break;
            }
            value = &operation.operands()[0];
        }
        match value {
            SemanticExpression::Register(register) => SsaVar::from_reg(register).map(Self::Ssa),
            SemanticExpression::Literal(literal) => {
                Some(Self::Literal(literal.value, literal.ty.clone()))
            }
            SemanticExpression::Operation(_) | SemanticExpression::Select { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ComparisonRelation {
    Equal,
    LessThan,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ComparisonAtom {
    relation: ComparisonRelation,
    left: ComparisonValue,
    right: ComparisonValue,
}

struct ComparisonTest {
    atom: ComparisonAtom,
    polarity: bool,
}

impl ComparisonTest {
    fn analyze(test: &SemanticOperation) -> Option<Self> {
        (test.insn_type == InsnType::If).then_some(())?;
        let [left, right] = test.operands() else {
            return None;
        };
        if !left.effects().is_pure() || !right.effects().is_pure() {
            return None;
        }
        let left = ComparisonValue::analyze(left)?;
        let right = ComparisonValue::analyze(right)?;
        let (relation, left, right, polarity) = match test.payload.if_op? {
            IfOp::Eq | IfOp::Ne => {
                let (left, right) = if left <= right {
                    (left, right)
                } else {
                    (right, left)
                };
                (
                    ComparisonRelation::Equal,
                    left,
                    right,
                    test.payload.if_op == Some(IfOp::Eq),
                )
            }
            IfOp::Lt => (ComparisonRelation::LessThan, left, right, true),
            IfOp::Ge => (ComparisonRelation::LessThan, left, right, false),
            IfOp::Gt => (ComparisonRelation::LessThan, right, left, true),
            IfOp::Le => (ComparisonRelation::LessThan, right, left, false),
        };
        Some(Self {
            atom: ComparisonAtom {
                relation,
                left,
                right,
            },
            polarity,
        })
    }
}

#[derive(Clone, Copy)]
struct PredicateAlias {
    representative: InstructionId,
    negated: bool,
}

#[derive(Default)]
struct PredicateAliases {
    by_instruction: BTreeMap<InstructionId, PredicateAlias>,
}

impl PredicateAliases {
    fn analyze(tests: &BTreeMap<InstructionId, SemanticOperation>) -> Self {
        let mut representatives = BTreeMap::<ComparisonAtom, (InstructionId, bool)>::new();
        let mut aliases = Self::default();
        for (&instruction, operation) in tests {
            let Some(test) = ComparisonTest::analyze(operation) else {
                continue;
            };
            let (representative, polarity) = *representatives
                .entry(test.atom)
                .or_insert((instruction, test.polarity));
            aliases.by_instruction.insert(
                instruction,
                PredicateAlias {
                    representative,
                    negated: polarity != test.polarity,
                },
            );
        }
        aliases
    }

    fn symbol(&self, symbol: BoolVariable) -> BoolVariable {
        match symbol {
            BoolVariable::Instruction(instruction) => self
                .by_instruction
                .get(&instruction)
                .map(|alias| BoolVariable::Instruction(alias.representative))
                .unwrap_or(symbol),
            _ => symbol,
        }
    }

    fn rewrite(&self, expression: BoolExpr) -> BoolExpr {
        let mut tasks = vec![PredicateAliasTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                PredicateAliasTask::Visit(BoolExpr::Symbol(BoolVariable::Instruction(
                    instruction,
                ))) => {
                    let expression = self.by_instruction.get(&instruction).map_or_else(
                        || BoolExpr::instruction(instruction),
                        |alias| {
                            let symbol = BoolExpr::instruction(alias.representative);
                            if alias.negated {
                                BoolExpr::not(symbol)
                            } else {
                                symbol
                            }
                        },
                    );
                    results.push(expression);
                }
                PredicateAliasTask::Visit(BoolExpr::Symbol(symbol)) => {
                    results.push(BoolExpr::Symbol(symbol));
                }
                PredicateAliasTask::Visit(BoolExpr::True) => results.push(BoolExpr::True),
                PredicateAliasTask::Visit(BoolExpr::False) => results.push(BoolExpr::False),
                PredicateAliasTask::Visit(BoolExpr::Not(inner)) => {
                    tasks.push(PredicateAliasTask::Not);
                    tasks.push(PredicateAliasTask::Visit(*inner));
                }
                PredicateAliasTask::Visit(BoolExpr::And(terms)) => {
                    tasks.push(PredicateAliasTask::Junction {
                        count: terms.len(),
                        conjunction: true,
                    });
                    tasks.extend(terms.into_iter().rev().map(PredicateAliasTask::Visit));
                }
                PredicateAliasTask::Visit(BoolExpr::Or(terms)) => {
                    tasks.push(PredicateAliasTask::Junction {
                        count: terms.len(),
                        conjunction: false,
                    });
                    tasks.extend(terms.into_iter().rev().map(PredicateAliasTask::Visit));
                }
                PredicateAliasTask::Not => {
                    let operand = results.pop().expect("predicate alias operand");
                    results.push(BoolExpr::not(operand));
                }
                PredicateAliasTask::Junction { count, conjunction } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .expect("predicate alias arity");
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        BoolExpr::and(terms)
                    } else {
                        BoolExpr::or(terms)
                    });
                }
            }
        }
        debug_assert_eq!(results.len(), 1);
        results.pop().unwrap_or(BoolExpr::False)
    }
}

enum PredicateAliasTask {
    Visit(BoolExpr),
    Not,
    Junction { count: usize, conjunction: bool },
}

impl PredicateCatalog {
    fn collect(root: &SemanticNode) -> Self {
        let mut catalog = Self {
            symbols: BTreeSet::new(),
            tests: BTreeMap::new(),
            occurrences: BTreeMap::new(),
        };
        catalog.visit_node(root);
        catalog
    }

    fn record(&mut self, predicate: &SemanticPredicate) {
        self.symbols.extend(predicate.symbols());
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(test) => {
                    self.tests.insert(test.id, test.clone());
                    *self.occurrences.entry(test.id).or_default() += 1;
                    self.visit_operation(test);
                }
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms)
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
    }
}

impl SemanticVisitor for PredicateCatalog {
    fn visit_predicate(&mut self, predicate: &SemanticPredicate) {
        self.record(predicate);
    }
}

struct PathConditionDomain {
    bdd: BddContext,
    tests: BTreeMap<InstructionId, crate::ir::SemanticOperation>,
    aliases: PredicateAliases,
    volatile_tests: BTreeSet<InstructionId>,
    boolean_tests: BTreeMap<InstructionId, BooleanTest>,
    boolean_relations: BooleanRelations,
}

impl PathConditionDomain {
    fn new(catalog: PredicateCatalog, types: &SourceTypeEnvironment) -> Self {
        let mut boolean_tests = BTreeMap::new();
        for (&instruction, test) in &catalog.tests {
            let Some(test) = BooleanTest::analyze(test, types) else {
                continue;
            };
            boolean_tests.insert(instruction, test);
        }
        let boolean_relations = BooleanRelations::new(&catalog, &boolean_tests);
        let aliases = PredicateAliases::analyze(&catalog.tests);
        let symbols = catalog
            .symbols
            .iter()
            .cloned()
            .map(|symbol| aliases.symbol(symbol))
            .collect::<BTreeSet<_>>();
        let volatile_tests = catalog
            .occurrences
            .into_iter()
            .filter_map(|(instruction, occurrences)| {
                (occurrences > 1
                    && catalog.tests.get(&instruction).is_some_and(|test| {
                        test.operands()
                            .iter()
                            .any(|operand| !operand.effects().is_pure())
                            || test
                                .compound_target()
                                .is_some_and(|target| !target.effects().is_pure())
                    }))
                .then_some(instruction)
            })
            .collect::<BTreeSet<_>>();
        Self {
            bdd: BddContext::new(&symbols),
            tests: catalog.tests,
            aliases,
            volatile_tests,
            boolean_tests,
            boolean_relations,
        }
    }

    fn truth(&self) -> Bdd {
        self.bdd.truth()
    }

    fn normal_after(&self, root: &SemanticNode, care: Bdd) -> Result<Bdd, SemanticFoldError> {
        let completion = CompletionInterpreter::analyze(root, self)?;
        Ok(self.bdd.and(care, completion.normal)?)
    }

    fn simplify(&self, predicate: SemanticPredicate, care: Bdd) -> PredicateFact {
        if self.is_volatile(&predicate) {
            return PredicateFact::unchanged(predicate);
        }
        let Some(expression) = self.predicate_expression(&predicate).ok() else {
            return PredicateFact::unchanged(predicate);
        };
        let Some(value) = self.bdd.compile(&expression).ok() else {
            return PredicateFact::unchanged(predicate);
        };
        let Some(constrained) = self.bdd.constrain(value, care).ok() else {
            return PredicateFact::known(predicate, value);
        };
        if constrained == value {
            return PredicateFact::known(predicate, value);
        }
        let Some((expression, nodes)) = self.bdd.expression(constrained, 1_024).ok().flatten()
        else {
            return PredicateFact::known(predicate, value);
        };
        if nodes > Self::size(&predicate) {
            return PredicateFact::known(predicate, value);
        }
        let Some(replacement) = self.lower(expression) else {
            return PredicateFact::known(predicate, value);
        };
        PredicateFact {
            predicate: replacement,
            value: Some(value),
            changed: true,
        }
    }

    fn simplify_boolean_relations(
        &self,
        predicate: SemanticPredicate,
        known: &BooleanState,
    ) -> Result<(SemanticPredicate, bool), SemanticFoldError> {
        self.boolean_relations.simplify(predicate, known.relation)
    }

    fn is_volatile(&self, predicate: &SemanticPredicate) -> bool {
        predicate.symbols().iter().any(|symbol| {
            matches!(
                symbol,
                BoolVariable::Instruction(instruction)
                    if self.volatile_tests.contains(instruction)
            )
        })
    }

    fn assume(&self, care: Bdd, value: Option<Bdd>, expected: bool) -> Bdd {
        let Some(value) = value else {
            return care;
        };
        let value = if expected {
            Ok(value)
        } else {
            self.bdd.not(value)
        };
        value
            .and_then(|value| self.bdd.and(care, value))
            .unwrap_or(care)
    }

    fn complements(
        &self,
        left: &SemanticPredicate,
        right: &SemanticPredicate,
    ) -> Result<bool, SemanticFoldError> {
        if self.is_volatile(left) || self.is_volatile(right) {
            return Ok(false);
        }
        let left = self.bdd.compile(&self.predicate_expression(left)?)?;
        let right = self.bdd.compile(&self.predicate_expression(right)?)?;
        Ok(self.bdd.not(left)? == right)
    }

    fn predicate_expression(
        &self,
        predicate: &SemanticPredicate,
    ) -> Result<BoolExpr, SemanticFoldError> {
        Ok(self.aliases.rewrite(predicate.domain()?))
    }

    fn assume_variables(
        &self,
        known: &BooleanState,
        predicate: &SemanticPredicate,
        expected: bool,
    ) -> Result<BooleanState, SemanticFoldError> {
        let mut result = known.clone();
        self.assume_predicate(&mut result, predicate, expected);
        result.relation = self
            .boolean_relations
            .assume(result.relation, predicate, expected)?;
        Ok(result)
    }

    fn assume_predicate(
        &self,
        known: &mut BooleanState,
        predicate: &SemanticPredicate,
        expected: bool,
    ) {
        match predicate {
            SemanticPredicate::Test(test) => {
                let Some(test) = self.boolean_tests.get(&test.id) else {
                    return;
                };
                known
                    .values
                    .insert(test.variable, expected == test.predicate_matches_source);
            }
            SemanticPredicate::Not(inner) => self.assume_predicate(known, inner, !expected),
            SemanticPredicate::And(terms) if expected => {
                for term in terms {
                    self.assume_predicate(known, term, true);
                }
            }
            SemanticPredicate::Or(terms) if !expected => {
                for term in terms {
                    self.assume_predicate(known, term, false);
                }
            }
            SemanticPredicate::True
            | SemanticPredicate::False
            | SemanticPredicate::And(_)
            | SemanticPredicate::Or(_) => {}
        }
    }

    fn invalidate_after(
        &self,
        known: &mut BooleanState,
        node: &SemanticNode,
    ) -> Result<(), SemanticFoldError> {
        let variables = BooleanWrites::collect(node);
        for variable in &variables {
            known.values.remove(&variable);
        }
        known.relation = self.boolean_relations.forget(known.relation, &variables)?;
        Ok(())
    }

    fn invalidate_after_statement(
        &self,
        known: &mut BooleanState,
        statement: &crate::ir::SemanticStatement,
    ) -> Result<(), SemanticFoldError> {
        let variables = statement
            .result()
            .and_then(|result| result.code_var)
            .into_iter()
            .collect::<BTreeSet<_>>();
        for variable in &variables {
            known.values.remove(variable);
        }
        known.relation = self.boolean_relations.forget(known.relation, &variables)?;
        Ok(())
    }

    fn variables_after(
        &self,
        mut known: BooleanState,
        node: &SemanticNode,
    ) -> Result<BooleanState, SemanticFoldError> {
        match node {
            SemanticNode::BasicBlock(block) => {
                for statement in &block.statements {
                    if let Some(assignment) = BooleanAssignment::analyze(statement) {
                        known.values.insert(assignment.variable, assignment.value);
                    } else {
                        known.invalidate(statement.result().and_then(|result| result.code_var));
                    }
                    known.relation = self.boolean_relations.assign(known.relation, statement)?;
                }
            }
            SemanticNode::Sequence(children) => {
                for child in children {
                    known = self.variables_after(known, child)?;
                    if CompletionInterpreter::analyze(child, self)?
                        .normal
                        .is_false()
                    {
                        break;
                    }
                }
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                let then_normal = !CompletionInterpreter::analyze(then_node, self)?
                    .normal
                    .is_false();
                let else_normal = !else_node
                    .as_deref()
                    .map(|node| CompletionInterpreter::analyze(node, self))
                    .transpose()?
                    .is_some_and(|completion| completion.normal.is_false());
                let then_state = self
                    .variables_after(self.assume_variables(&known, condition, true)?, then_node)?;
                let else_state = match else_node.as_deref() {
                    Some(else_node) => self.variables_after(
                        self.assume_variables(&known, condition, false)?,
                        else_node,
                    )?,
                    None => self.assume_variables(&known, condition, false)?,
                };
                known = match (then_normal, else_normal) {
                    (true, true) => self.boolean_relations.join(then_state, else_state)?,
                    (true, false) => then_state,
                    (false, true) => else_state,
                    (false, false) => self.boolean_relations.initial_state(),
                };
            }
            SemanticNode::Synchronized { body, .. } | SemanticNode::Label { body, .. } => {
                known = self.variables_after(known, body)?;
            }
            SemanticNode::Empty | SemanticNode::Leave(_) => {}
            SemanticNode::Loop { .. }
            | SemanticNode::For { .. }
            | SemanticNode::ForEach { .. }
            | SemanticNode::Switch { .. }
            | SemanticNode::Try { .. } => {
                self.invalidate_after(&mut known, node)?;
            }
        }
        Ok(known)
    }

    fn initial_boolean_state(&self) -> BooleanState {
        self.boolean_relations.initial_state()
    }

    fn body_boolean_state(
        &self,
        mut known: BooleanState,
        node: &SemanticNode,
    ) -> Result<BooleanState, SemanticFoldError> {
        self.invalidate_after(&mut known, node)?;
        Ok(known)
    }

    fn simplify_with_facts(
        &self,
        predicate: SemanticPredicate,
        care: Bdd,
        known: &BooleanState,
    ) -> Result<PredicateFact, SemanticFoldError> {
        let mut fact = self.simplify(predicate, care);
        let (predicate, changed) = self.simplify_boolean_relations(fact.predicate, known)?;
        fact.predicate = predicate;
        fact.changed |= changed;
        Ok(fact)
    }

    fn lower(&self, expression: BoolExpr) -> Option<SemanticPredicate> {
        let mut tasks = vec![PredicateTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                PredicateTask::Visit(expression) => match expression {
                    BoolExpr::True => results.push(SemanticPredicate::True),
                    BoolExpr::False => results.push(SemanticPredicate::False),
                    BoolExpr::Symbol(BoolVariable::Instruction(instruction)) => results.push(
                        SemanticPredicate::Test(self.tests.get(&instruction)?.clone()),
                    ),
                    BoolExpr::Symbol(_) => return None,
                    BoolExpr::Not(inner) => {
                        tasks.push(PredicateTask::Not);
                        tasks.push(PredicateTask::Visit(*inner));
                    }
                    BoolExpr::And(terms) => {
                        let count = terms.len();
                        tasks.push(PredicateTask::Junction {
                            count,
                            conjunction: true,
                        });
                        tasks.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                    }
                    BoolExpr::Or(terms) => {
                        let count = terms.len();
                        tasks.push(PredicateTask::Junction {
                            count,
                            conjunction: false,
                        });
                        tasks.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                    }
                },
                PredicateTask::Not => {
                    let inner = results.pop()?;
                    results.push(inner.negate());
                }
                PredicateTask::Junction { count, conjunction } => {
                    let start = results.len().checked_sub(count)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        SemanticPredicate::And(terms)
                    } else {
                        SemanticPredicate::Or(terms)
                    });
                }
            }
        }
        (results.len() == 1).then(|| results.pop()).flatten()
    }

    fn size(predicate: &SemanticPredicate) -> usize {
        let mut size = 0usize;
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            size = size.saturating_add(1);
            match predicate {
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms)
                }
                SemanticPredicate::True | SemanticPredicate::False | SemanticPredicate::Test(_) => {
                }
            }
        }
        size
    }
}

struct BooleanRelations {
    bdd: BddContext,
    tests: BTreeMap<InstructionId, SemanticOperation>,
    boolean_tests: BTreeMap<InstructionId, BooleanTest>,
    variables: BTreeSet<u32>,
}

impl BooleanRelations {
    fn new(
        catalog: &PredicateCatalog,
        boolean_tests: &BTreeMap<InstructionId, BooleanTest>,
    ) -> Self {
        let variables = boolean_tests
            .values()
            .map(|test| test.variable)
            .collect::<BTreeSet<_>>();
        let mut symbols = catalog.symbols.clone();
        symbols.extend(variables.iter().copied().map(BoolVariable::Source));
        Self {
            bdd: BddContext::new(&symbols),
            tests: catalog.tests.clone(),
            boolean_tests: boolean_tests.clone(),
            variables,
        }
    }

    fn truth(&self) -> Bdd {
        self.bdd.truth()
    }

    fn initial_state(&self) -> BooleanState {
        BooleanState {
            values: BTreeMap::new(),
            relation: self.truth(),
        }
    }

    fn forget(&self, relation: Bdd, variables: &BTreeSet<u32>) -> Result<Bdd, SemanticFoldError> {
        let variables = variables
            .intersection(&self.variables)
            .copied()
            .map(BoolVariable::Source)
            .collect::<BTreeSet<_>>();
        if variables.is_empty() {
            return Ok(relation);
        }
        Ok(self.bdd.exists(relation, &variables)?)
    }

    fn join(
        &self,
        mut left: BooleanState,
        right: BooleanState,
    ) -> Result<BooleanState, SemanticFoldError> {
        left.values
            .retain(|variable, value| right.values.get(variable) == Some(value));
        left.relation = self.bdd.or(left.relation, right.relation)?;
        Ok(left)
    }

    fn assume(
        &self,
        relation: Bdd,
        predicate: &SemanticPredicate,
        expected: bool,
    ) -> Result<Bdd, SemanticFoldError> {
        let Some(expression) = self.expression(predicate, true) else {
            return Ok(relation);
        };
        let value = self.bdd.compile(&expression)?;
        let value = if expected {
            value
        } else {
            self.bdd.not(value)?
        };
        Ok(self.bdd.and(relation, value)?)
    }

    fn assign(
        &self,
        relation: Bdd,
        statement: &crate::ir::SemanticStatement,
    ) -> Result<Bdd, SemanticFoldError> {
        let Some(result) = statement.result() else {
            return Ok(relation);
        };
        let Some(variable) = result
            .code_var
            .filter(|value| self.variables.contains(value))
        else {
            return Ok(relation);
        };
        let forgotten = self.forget(relation, &BTreeSet::from([variable]))?;
        let value = match &statement.kind {
            SemanticStatementKind::Definition { value, .. } => self.value_expression(value),
            SemanticStatementKind::Instruction(operation) => self.operation_expression(operation),
        };
        let Some(value) = value else {
            return Ok(forgotten);
        };
        if value.symbols().contains(&BoolVariable::Source(variable)) {
            return Ok(forgotten);
        }
        let target = self.bdd.compile(&BoolExpr::source(variable))?;
        let value = self.bdd.compile(&value)?;
        let equal = self.bdd.or(
            self.bdd.and(target, value)?,
            self.bdd.and(self.bdd.not(target)?, self.bdd.not(value)?)?,
        )?;
        Ok(self.bdd.and(forgotten, equal)?)
    }

    fn operation_expression(&self, operation: &SemanticOperation) -> Option<BoolExpr> {
        if !matches!(operation.insn_type, InsnType::Const | InsnType::Move)
            || operation.operands().len() != 1
        {
            return None;
        }
        self.value_expression(&operation.operands()[0])
    }

    fn value_expression(&self, value: &SemanticExpression) -> Option<BoolExpr> {
        match value {
            SemanticExpression::Register(register) => register
                .code_var
                .filter(|variable| self.variables.contains(variable))
                .map(BoolExpr::source),
            SemanticExpression::Literal(literal) => match literal.value {
                0 => Some(BoolExpr::False),
                1 => Some(BoolExpr::True),
                _ => None,
            },
            SemanticExpression::Operation(operation) => self.operation_expression(operation),
            SemanticExpression::Select {
                condition,
                when_true,
                when_false,
            } => {
                let condition = self.expression(condition, true)?;
                let when_true = self.value_expression(when_true)?;
                let when_false = self.value_expression(when_false)?;
                Some(BoolExpr::or(vec![
                    BoolExpr::and(vec![condition.clone(), when_true]),
                    BoolExpr::and(vec![BoolExpr::not(condition), when_false]),
                ]))
            }
        }
    }

    fn simplify(
        &self,
        predicate: SemanticPredicate,
        relation: Bdd,
    ) -> Result<(SemanticPredicate, bool), SemanticFoldError> {
        if relation.is_false() || !Self::predicate_is_pure(&predicate) {
            return Ok((predicate, false));
        }
        let Some(original) = self.expression(&predicate, false) else {
            return Ok((predicate, false));
        };
        let original_symbols = original.symbols();
        let Some((expression, nodes)) = self.bdd.reduce_under(&original, relation, 1_024)? else {
            return Ok((predicate, false));
        };
        if expression == original {
            return Ok((predicate, false));
        }
        if nodes > PathConditionDomain::size(&predicate)
            || !expression.symbols().is_subset(&original_symbols)
        {
            return Ok((predicate, false));
        }
        let Some(replacement) = self.lower(expression, &predicate) else {
            return Ok((predicate, false));
        };
        Ok((replacement, true))
    }

    fn expression(&self, predicate: &SemanticPredicate, boolean_only: bool) -> Option<BoolExpr> {
        let mut tasks = vec![BooleanExpressionTask::Visit(predicate)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                BooleanExpressionTask::Visit(SemanticPredicate::True) => {
                    results.push(BoolExpr::True)
                }
                BooleanExpressionTask::Visit(SemanticPredicate::False) => {
                    results.push(BoolExpr::False)
                }
                BooleanExpressionTask::Visit(SemanticPredicate::Test(test)) => {
                    if let Some(boolean) = self.boolean_tests.get(&test.id) {
                        let value = BoolExpr::source(boolean.variable);
                        results.push(if boolean.predicate_matches_source {
                            value
                        } else {
                            BoolExpr::not(value)
                        });
                    } else if boolean_only {
                        return None;
                    } else {
                        results.push(BoolExpr::instruction(test.id));
                    }
                }
                BooleanExpressionTask::Visit(SemanticPredicate::Not(inner)) => {
                    tasks.push(BooleanExpressionTask::Not);
                    tasks.push(BooleanExpressionTask::Visit(inner));
                }
                BooleanExpressionTask::Visit(SemanticPredicate::And(terms)) => {
                    tasks.push(BooleanExpressionTask::Junction {
                        count: terms.len(),
                        conjunction: true,
                    });
                    tasks.extend(terms.iter().rev().map(BooleanExpressionTask::Visit));
                }
                BooleanExpressionTask::Visit(SemanticPredicate::Or(terms)) => {
                    tasks.push(BooleanExpressionTask::Junction {
                        count: terms.len(),
                        conjunction: false,
                    });
                    tasks.extend(terms.iter().rev().map(BooleanExpressionTask::Visit));
                }
                BooleanExpressionTask::Not => {
                    let value = results.pop()?;
                    results.push(BoolExpr::not(value));
                }
                BooleanExpressionTask::Junction { count, conjunction } => {
                    let start = results.len().checked_sub(count)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        BoolExpr::and(terms)
                    } else {
                        BoolExpr::or(terms)
                    });
                }
            }
        }
        (results.len() == 1).then(|| results.pop()).flatten()
    }

    fn lower(
        &self,
        expression: BoolExpr,
        original: &SemanticPredicate,
    ) -> Option<SemanticPredicate> {
        let representatives = self.representatives(original);
        let mut tasks = vec![PredicateTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                PredicateTask::Visit(BoolExpr::True) => results.push(SemanticPredicate::True),
                PredicateTask::Visit(BoolExpr::False) => results.push(SemanticPredicate::False),
                PredicateTask::Visit(BoolExpr::Symbol(BoolVariable::Instruction(instruction))) => {
                    results.push(SemanticPredicate::Test(
                        self.tests.get(&instruction)?.clone(),
                    ));
                }
                PredicateTask::Visit(BoolExpr::Symbol(BoolVariable::Source(variable))) => {
                    results.push(representatives.get(&variable)?.clone());
                }
                PredicateTask::Visit(BoolExpr::Symbol(_)) => return None,
                PredicateTask::Visit(BoolExpr::Not(inner)) => {
                    tasks.push(PredicateTask::Not);
                    tasks.push(PredicateTask::Visit(*inner));
                }
                PredicateTask::Visit(BoolExpr::And(terms)) => {
                    tasks.push(PredicateTask::Junction {
                        count: terms.len(),
                        conjunction: true,
                    });
                    tasks.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                }
                PredicateTask::Visit(BoolExpr::Or(terms)) => {
                    tasks.push(PredicateTask::Junction {
                        count: terms.len(),
                        conjunction: false,
                    });
                    tasks.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                }
                PredicateTask::Not => {
                    let inner = results.pop()?;
                    results.push(inner.negate());
                }
                PredicateTask::Junction { count, conjunction } => {
                    let start = results.len().checked_sub(count)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        SemanticPredicate::And(terms)
                    } else {
                        SemanticPredicate::Or(terms)
                    });
                }
            }
        }
        (results.len() == 1).then(|| results.pop()).flatten()
    }

    fn representatives(&self, predicate: &SemanticPredicate) -> BTreeMap<u32, SemanticPredicate> {
        let mut representatives = BTreeMap::new();
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(test) => {
                    let Some(boolean) = self.boolean_tests.get(&test.id) else {
                        continue;
                    };
                    representatives.entry(boolean.variable).or_insert_with(|| {
                        let predicate = SemanticPredicate::Test(test.clone());
                        if boolean.predicate_matches_source {
                            predicate
                        } else {
                            predicate.negate()
                        }
                    });
                }
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms);
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
        representatives
    }

    fn predicate_is_pure(predicate: &SemanticPredicate) -> bool {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(test) => {
                    if !test.effects().without_control().is_pure() {
                        return false;
                    }
                }
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms);
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
        true
    }
}

enum BooleanExpressionTask<'a> {
    Visit(&'a SemanticPredicate),
    Not,
    Junction { count: usize, conjunction: bool },
}

struct SelectConditionReduction<'a> {
    domain: &'a PathConditionDomain,
    known: &'a BooleanState,
    changed: bool,
    error: Option<SemanticFoldError>,
}

impl<'a> SelectConditionReduction<'a> {
    fn new(domain: &'a PathConditionDomain, known: &'a BooleanState) -> Self {
        Self {
            domain,
            known,
            changed: false,
            error: None,
        }
    }

    fn finish(&mut self) -> Result<(), SemanticFoldError> {
        match self.error.take() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

impl SemanticExpressionTransform for SelectConditionReduction<'_> {
    fn transform_select(
        &mut self,
        condition: SemanticPredicate,
        when_true: SemanticExpression,
        when_false: SemanticExpression,
    ) -> SemanticExpression {
        if self.error.is_some() {
            return SemanticExpression::select(condition, when_true, when_false);
        }
        let original = condition.clone();
        let (condition, changed) = match self
            .domain
            .simplify_boolean_relations(condition, self.known)
        {
            Ok(result) => result,
            Err(error) => {
                self.error = Some(error);
                return SemanticExpression::select(original, when_true, when_false);
            }
        };
        self.changed |= changed;
        SemanticExpression::select(condition, when_true, when_false)
    }
}

#[derive(Clone)]
struct BooleanState {
    values: BTreeMap<u32, bool>,
    relation: Bdd,
}

impl BooleanState {
    fn invalidate(&mut self, variable: Option<u32>) {
        if let Some(variable) = variable {
            self.values.remove(&variable);
        }
    }

    fn proves(&self, variable: u32, value: bool) -> bool {
        self.values.get(&variable) == Some(&value)
    }
}

#[derive(Default)]
struct BooleanWrites {
    variables: BTreeSet<u32>,
}

impl BooleanWrites {
    fn collect(node: &SemanticNode) -> BTreeSet<u32> {
        let mut writes = Self::default();
        writes.visit_node(node);
        writes.variables
    }
}

impl SemanticVisitor for BooleanWrites {
    fn visit_statement(&mut self, statement: &crate::ir::SemanticStatement) {
        self.variables
            .extend(statement.result().and_then(|result| result.code_var));
    }
}

#[derive(Clone, Copy)]
struct BooleanTest {
    variable: u32,
    predicate_matches_source: bool,
}

impl BooleanTest {
    fn analyze(test: &SemanticOperation, types: &SourceTypeEnvironment) -> Option<Self> {
        (test.insn_type == InsnType::If).then_some(())?;
        let predicate_matches_source = match test.payload.if_op? {
            IfOp::Ne => true,
            IfOp::Eq => false,
            IfOp::Lt | IfOp::Ge | IfOp::Gt | IfOp::Le => return None,
        };
        let [left, right] = test.operands() else {
            return None;
        };
        let register = if Self::boolean_literal(right) == Some(false) {
            Self::direct_register(left)?
        } else if Self::boolean_literal(left) == Some(false) {
            Self::direct_register(right)?
        } else {
            return None;
        };
        (types.register_type(register).ok() == Some(&ArgType::BOOLEAN)).then_some(Self {
            variable: register.code_var?,
            predicate_matches_source,
        })
    }

    fn direct_register(value: &SemanticExpression) -> Option<&crate::ir::RegisterArg> {
        match Self::canonical(value) {
            SemanticExpression::Register(register) => Some(register),
            SemanticExpression::Literal(_)
            | SemanticExpression::Operation(_)
            | SemanticExpression::Select { .. } => None,
        }
    }

    fn boolean_literal(value: &SemanticExpression) -> Option<bool> {
        match Self::canonical(value) {
            SemanticExpression::Literal(literal) => match literal.value {
                0 => Some(false),
                1 => Some(true),
                _ => None,
            },
            SemanticExpression::Register(_)
            | SemanticExpression::Operation(_)
            | SemanticExpression::Select { .. } => None,
        }
    }

    fn canonical(mut value: &SemanticExpression) -> &SemanticExpression {
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
}

struct BooleanAssignment {
    variable: u32,
    value: bool,
}

impl BooleanAssignment {
    fn analyze(statement: &crate::ir::SemanticStatement) -> Option<Self> {
        let result = statement.result()?;
        let value = match &statement.kind {
            SemanticStatementKind::Definition { value, .. } => BooleanTest::boolean_literal(value)?,
            SemanticStatementKind::Instruction(operation) => {
                if !matches!(operation.insn_type, InsnType::Const | InsnType::Move)
                    || operation.operands().len() != 1
                {
                    return None;
                }
                BooleanTest::boolean_literal(&operation.operands()[0])?
            }
        };
        Some(Self {
            variable: result.code_var?,
            value,
        })
    }
}

#[derive(Clone)]
struct PathCompletion {
    normal: Bdd,
    abrupt: BTreeMap<SemanticTransfer, Bdd>,
}

impl PathCompletion {
    fn normal(domain: &PathConditionDomain) -> Self {
        Self {
            normal: domain.bdd.truth(),
            abrupt: BTreeMap::new(),
        }
    }

    fn abrupt(domain: &PathConditionDomain, transfer: SemanticTransfer) -> Self {
        Self {
            normal: domain.bdd.falsity(),
            abrupt: BTreeMap::from([(transfer, domain.bdd.truth())]),
        }
    }

    fn gate(
        mut self,
        domain: &PathConditionDomain,
        condition: Bdd,
    ) -> Result<Self, SemanticFoldError> {
        self.normal = domain.bdd.and(condition, self.normal)?;
        for value in self.abrupt.values_mut() {
            *value = domain.bdd.and(condition, *value)?;
        }
        self.abrupt.retain(|_, value| !value.is_false());
        Ok(self)
    }

    fn merge_abrupt(
        domain: &PathConditionDomain,
        target: &mut BTreeMap<SemanticTransfer, Bdd>,
        source: BTreeMap<SemanticTransfer, Bdd>,
    ) -> Result<(), SemanticFoldError> {
        for (transfer, condition) in source {
            let merged = match target.get(&transfer).copied() {
                Some(current) => domain.bdd.or(current, condition)?,
                None => condition,
            };
            target.insert(transfer, merged);
        }
        Ok(())
    }

    fn alternatives(
        domain: &PathConditionDomain,
        children: impl IntoIterator<Item = Self>,
    ) -> Result<Self, SemanticFoldError> {
        let mut result = Self {
            normal: domain.bdd.falsity(),
            abrupt: BTreeMap::new(),
        };
        for child in children {
            result.normal = domain.bdd.or(result.normal, child.normal)?;
            Self::merge_abrupt(domain, &mut result.abrupt, child.abrupt)?;
        }
        Ok(result)
    }

    fn consume_loop(
        &mut self,
        domain: &PathConditionDomain,
        control: SemanticLoopControl,
    ) -> Result<(Bdd, Bdd), SemanticFoldError> {
        let (break_transfer, continue_transfer) = match control {
            SemanticLoopControl::Region(region) => (
                SemanticTransfer::Break(region),
                SemanticTransfer::Continue(region),
            ),
            SemanticLoopControl::Label(label) => (
                SemanticTransfer::BreakLabel(label),
                SemanticTransfer::ContinueLabel(label),
            ),
        };
        Ok((
            self.abrupt
                .remove(&break_transfer)
                .unwrap_or_else(|| domain.bdd.falsity()),
            self.abrupt
                .remove(&continue_transfer)
                .unwrap_or_else(|| domain.bdd.falsity()),
        ))
    }
}

impl CompletionDomain for PathConditionDomain {
    type State = PathCompletion;
    type Error = SemanticFoldError;

    fn normal(&self) -> Result<Self::State, Self::Error> {
        Ok(PathCompletion::normal(self))
    }

    fn no_return_call(&self) -> Result<Self::State, Self::Error> {
        Ok(PathCompletion::abrupt(self, SemanticTransfer::Throw))
    }

    fn leave(&self, leave: &SemanticLeave) -> Result<Self::State, Self::Error> {
        Ok(PathCompletion::abrupt(
            self,
            SemanticTransfer::from_leave(leave),
        ))
    }

    fn sequence(&self, children: Vec<Self::State>) -> Result<Self::State, Self::Error> {
        let mut result = PathCompletion::normal(self);
        for child in children {
            let entry = result.normal;
            let child = child.gate(self, entry)?;
            PathCompletion::merge_abrupt(self, &mut result.abrupt, child.abrupt)?;
            result.normal = child.normal;
            if result.normal.is_false() {
                break;
            }
        }
        Ok(result)
    }

    fn branch(
        &self,
        condition: &SemanticPredicate,
        then_state: Self::State,
        else_state: Option<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        if self.is_volatile(condition) {
            return PathCompletion::alternatives(
                self,
                [
                    then_state,
                    else_state.unwrap_or_else(|| PathCompletion::normal(self)),
                ],
            );
        }
        let condition = self.bdd.compile(&self.predicate_expression(condition)?)?;
        let when_false = self.bdd.not(condition)?;
        PathCompletion::alternatives(
            self,
            [
                then_state.gate(self, condition)?,
                else_state
                    .unwrap_or_else(|| PathCompletion::normal(self))
                    .gate(self, when_false)?,
            ],
        )
    }

    fn loop_node(
        &self,
        control: SemanticLoopControl,
        kind: SemanticLoopKind,
        condition: &SemanticPredicate,
        setup: Self::State,
        mut body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        let (break_path, continue_path) = body.consume_loop(self, control)?;
        let condition_true = condition.constant_value() == Some(true);
        let condition_false = condition.constant_value() == Some(false);
        let mut result = PathCompletion {
            normal: self.bdd.falsity(),
            abrupt: BTreeMap::new(),
        };

        if kind == SemanticLoopKind::PostTested {
            PathCompletion::merge_abrupt(self, &mut result.abrupt, body.abrupt)?;
            let reaches_test = self.bdd.or(body.normal, continue_path)?;
            let setup = setup.gate(self, reaches_test)?;
            PathCompletion::merge_abrupt(self, &mut result.abrupt, setup.abrupt)?;
            result.normal = if !break_path.is_false()
                || (!reaches_test.is_false() && !setup.normal.is_false() && !condition_true)
            {
                self.bdd.truth()
            } else {
                self.bdd.falsity()
            };
            return Ok(result);
        }

        PathCompletion::merge_abrupt(self, &mut result.abrupt, setup.abrupt)?;
        if setup.normal.is_false() {
            return Ok(result);
        }
        if kind == SemanticLoopKind::PreTested && condition_false {
            result.normal = setup.normal;
            return Ok(result);
        }
        body = body.gate(self, setup.normal)?;
        PathCompletion::merge_abrupt(self, &mut result.abrupt, body.abrupt)?;
        result.normal = match kind {
            SemanticLoopKind::PreTested if !condition_true || !break_path.is_false() => {
                setup.normal
            }
            SemanticLoopKind::Endless if !break_path.is_false() => setup.normal,
            SemanticLoopKind::PreTested | SemanticLoopKind::Endless => self.bdd.falsity(),
            SemanticLoopKind::PostTested => unreachable!(),
        };
        Ok(result)
    }

    fn for_node(
        &self,
        control: SemanticLoopControl,
        condition: &SemanticPredicate,
        mut body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        let (break_path, _) = body.consume_loop(self, control)?;
        body.normal = if condition.constant_value() != Some(true) || !break_path.is_false() {
            self.bdd.truth()
        } else {
            self.bdd.falsity()
        };
        Ok(body)
    }

    fn for_each_node(
        &self,
        control: SemanticLoopControl,
        mut body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        let _ = body.consume_loop(self, control)?;
        body.normal = self.bdd.truth();
        Ok(body)
    }

    fn switch_node(
        &self,
        region: Option<crate::ir::RegionId>,
        has_default: bool,
        cases: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        let mut result = PathCompletion::alternatives(self, cases)?;
        let break_path = region
            .and_then(|region| result.abrupt.remove(&SemanticTransfer::Break(region)))
            .unwrap_or_else(|| self.bdd.falsity());
        if !has_default || !result.normal.is_false() || !break_path.is_false() {
            result.normal = self.bdd.truth();
        }
        Ok(result)
    }

    fn try_node(
        &self,
        catches: usize,
        has_finally: bool,
        mut children: Vec<Self::State>,
    ) -> Result<Self::State, Self::Error> {
        let finally = has_finally.then(|| children.pop().expect("finally child"));
        let protected = PathCompletion::alternatives(self, children.drain(..=catches))?;
        let Some(finally) = finally else {
            return Ok(protected);
        };
        let mut result = PathCompletion {
            normal: self.bdd.and(protected.normal, finally.normal)?,
            abrupt: finally.abrupt,
        };
        let protected_abrupt = protected
            .abrupt
            .into_iter()
            .map(|(transfer, condition)| Ok((transfer, self.bdd.and(condition, finally.normal)?)))
            .collect::<Result<BTreeMap<_, _>, SemanticFoldError>>()?;
        PathCompletion::merge_abrupt(self, &mut result.abrupt, protected_abrupt)?;
        Ok(result)
    }

    fn synchronized(&self, body: Self::State) -> Result<Self::State, Self::Error> {
        Ok(body)
    }

    fn label(
        &self,
        label: SemanticLabel,
        mut body: Self::State,
    ) -> Result<Self::State, Self::Error> {
        if let Some(break_path) = body.abrupt.remove(&SemanticTransfer::BreakLabel(label)) {
            body.normal = self.bdd.or(body.normal, break_path)?;
        }
        Ok(body)
    }
}

struct PredicateFact {
    predicate: SemanticPredicate,
    value: Option<Bdd>,
    changed: bool,
}

impl PredicateFact {
    fn unchanged(predicate: SemanticPredicate) -> Self {
        Self {
            predicate,
            value: None,
            changed: false,
        }
    }

    fn known(predicate: SemanticPredicate, value: Bdd) -> Self {
        Self {
            predicate,
            value: Some(value),
            changed: false,
        }
    }
}

struct PathConditionReduction {
    domain: PathConditionDomain,
    changed: bool,
}

impl PathConditionReduction {
    fn new(domain: PathConditionDomain) -> Self {
        Self {
            domain,
            changed: false,
        }
    }

    fn apply(&mut self, root: SemanticNode) -> Result<SemanticNode, SemanticFoldError> {
        let mut tasks = vec![ReductionTask::Visit {
            node: root,
            care: self.domain.truth(),
            known: self.domain.initial_boolean_state(),
        }];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ReductionTask::Visit { node, care, known } => match node {
                    SemanticNode::Sequence(children) => {
                        let mut child_cares = Vec::with_capacity(children.len());
                        let mut child_states = Vec::with_capacity(children.len());
                        let mut next_care = care;
                        let mut next_state = known;
                        for child in &children {
                            child_cares.push(next_care);
                            child_states.push(next_state.clone());
                            next_care = self.domain.normal_after(child, next_care)?;
                            next_state = self.domain.variables_after(next_state, child)?;
                        }
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::Sequence(
                            children.len(),
                        )));
                        tasks.extend(
                            children
                                .into_iter()
                                .zip(child_cares)
                                .zip(child_states)
                                .rev()
                                .map(|((node, care), known)| ReductionTask::Visit {
                                    node,
                                    care,
                                    known,
                                }),
                        );
                    }
                    SemanticNode::If {
                        condition,
                        then_node,
                        else_node,
                    } => {
                        let site = condition.site;
                        let condition = condition.into_inner();
                        let when_true_state =
                            self.domain.assume_variables(&known, &condition, true)?;
                        let when_false_state =
                            self.domain.assume_variables(&known, &condition, false)?;
                        let fact = self.domain.simplify_with_facts(condition, care, &known)?;
                        self.changed |= fact.changed;
                        let when_true = self.domain.assume(care, fact.value, true);
                        let when_false = self.domain.assume(care, fact.value, false);
                        let has_else = else_node.is_some();
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::If {
                            condition: crate::ir::SemanticOperand {
                                site,
                                value: fact.predicate,
                            },
                            has_else,
                        }));
                        if let Some(node) = else_node {
                            tasks.push(ReductionTask::Visit {
                                node: *node,
                                care: when_false,
                                known: when_false_state,
                            });
                        }
                        tasks.push(ReductionTask::Visit {
                            node: *then_node,
                            care: when_true,
                            known: when_true_state,
                        });
                    }
                    SemanticNode::Loop {
                        control,
                        header,
                        kind,
                        test,
                        body,
                    } => {
                        let site = test.condition.site;
                        let condition = test.condition.into_inner();
                        let mut header_state = known.clone();
                        self.domain
                            .invalidate_after(&mut header_state, &test.setup)?;
                        self.domain.invalidate_after(&mut header_state, &body)?;
                        let mut body_state = header_state.clone();
                        if kind == SemanticLoopKind::PreTested {
                            body_state =
                                self.domain
                                    .assume_variables(&body_state, &condition, true)?;
                        }
                        let fact =
                            self.domain
                                .simplify_with_facts(condition, care, &header_state)?;
                        self.changed |= fact.changed;
                        let body_care = if kind == SemanticLoopKind::PreTested {
                            self.domain.assume(care, fact.value, true)
                        } else {
                            care
                        };
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::Loop {
                            control,
                            header,
                            kind,
                            condition: crate::ir::SemanticOperand {
                                site,
                                value: fact.predicate,
                            },
                        }));
                        tasks.push(ReductionTask::Visit {
                            node: *body,
                            care: body_care,
                            known: body_state,
                        });
                        tasks.push(ReductionTask::Visit {
                            node: *test.setup,
                            care,
                            known: header_state,
                        });
                    }
                    SemanticNode::For {
                        control,
                        init,
                        condition,
                        update,
                        body,
                    } => {
                        let site = condition.site;
                        let condition = condition.into_inner();
                        let mut header_state = known.clone();
                        self.domain.invalidate_after(&mut header_state, &body)?;
                        self.domain
                            .invalidate_after_statement(&mut header_state, &update)?;
                        let body_state =
                            self.domain
                                .assume_variables(&header_state, &condition, true)?;
                        let fact =
                            self.domain
                                .simplify_with_facts(condition, care, &header_state)?;
                        self.changed |= fact.changed;
                        let body_care = self.domain.assume(care, fact.value, true);
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::For {
                            control,
                            init,
                            condition: crate::ir::SemanticOperand {
                                site,
                                value: fact.predicate,
                            },
                            update,
                        }));
                        tasks.push(ReductionTask::Visit {
                            node: *body,
                            care: body_care,
                            known: body_state,
                        });
                    }
                    SemanticNode::ForEach {
                        control,
                        variable,
                        iterable,
                        body,
                    } => {
                        let body_state = self.domain.body_boolean_state(known, &body)?;
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::ForEach {
                            control,
                            variable,
                            iterable,
                        }));
                        tasks.push(ReductionTask::Visit {
                            node: *body,
                            care,
                            known: body_state,
                        });
                    }
                    SemanticNode::Switch {
                        region,
                        selector,
                        cases,
                    } => {
                        let metadata = cases
                            .iter()
                            .map(|case| (case.values.clone(), case.is_default))
                            .collect::<Vec<_>>();
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::Switch {
                            region,
                            selector,
                            metadata,
                        }));
                        tasks.extend(cases.into_iter().rev().map(|case| ReductionTask::Visit {
                            node: case.body,
                            care,
                            known: known.clone(),
                        }));
                    }
                    SemanticNode::Try {
                        region,
                        body,
                        catches,
                        finally,
                    } => {
                        let catch_metadata = catches
                            .iter()
                            .map(|catch| {
                                (
                                    catch.region,
                                    catch.exception_types.clone(),
                                    catch.exception_value.clone(),
                                )
                            })
                            .collect::<Vec<_>>();
                        let finally_region = finally.as_ref().map(|finally| finally.region);
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::Try {
                            region,
                            catch_metadata,
                            finally_region,
                        }));
                        if let Some(finally) = finally {
                            tasks.push(ReductionTask::Visit {
                                node: *finally.body,
                                care,
                                known: known.clone(),
                            });
                        }
                        tasks.extend(catches.into_iter().rev().map(|catch| ReductionTask::Visit {
                            node: catch.body,
                            care,
                            known: known.clone(),
                        }));
                        tasks.push(ReductionTask::Visit {
                            node: *body,
                            care,
                            known,
                        });
                    }
                    SemanticNode::Synchronized {
                        region,
                        lock,
                        method,
                        body,
                    } => {
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::Synchronized {
                            region,
                            lock,
                            method,
                        }));
                        tasks.push(ReductionTask::Visit {
                            node: *body,
                            care,
                            known,
                        });
                    }
                    SemanticNode::BasicBlock(mut block) => {
                        let before = block.statements.len();
                        let mut retained = Vec::with_capacity(before);
                        let mut known = known;
                        for mut statement in block.statements {
                            let mut reduction = SelectConditionReduction::new(&self.domain, &known);
                            SemanticInstructions::transform_statement(
                                &mut statement,
                                &mut reduction,
                            )?;
                            reduction.finish()?;
                            self.changed |= reduction.changed;
                            let redundant =
                                BooleanAssignment::analyze(&statement).is_some_and(|assignment| {
                                    known.proves(assignment.variable, assignment.value)
                                });
                            let relation = self
                                .domain
                                .boolean_relations
                                .assign(known.relation, &statement)?;
                            if redundant {
                                self.changed = true;
                            } else {
                                match BooleanAssignment::analyze(&statement) {
                                    Some(assignment) => {
                                        known.values.insert(assignment.variable, assignment.value);
                                    }
                                    None => known.invalidate(
                                        statement.result().and_then(|result| result.code_var),
                                    ),
                                }
                                retained.push(statement);
                            }
                            known.relation = relation;
                        }
                        block.statements = retained;
                        results.push(SemanticNode::BasicBlock(block));
                    }
                    SemanticNode::Label { label, body } => {
                        tasks.push(ReductionTask::Rebuild(ReductionFrame::Label(label)));
                        tasks.push(ReductionTask::Visit {
                            node: *body,
                            care,
                            known,
                        });
                    }
                    node => results.push(node),
                },
                ReductionTask::Rebuild(mut frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let mut children = results.drain(start..).collect();
                    if matches!(frame, ReductionFrame::Sequence(_)) {
                        children = self.cluster_conditions(children)?;
                        frame = ReductionFrame::Sequence(children.len());
                    }
                    results.push(frame.rebuild(children)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        results.pop().ok_or(SemanticFoldError::MalformedWorkStack)
    }

    fn cluster_conditions(
        &mut self,
        children: Vec<SemanticNode>,
    ) -> Result<Vec<SemanticNode>, SemanticFoldError> {
        let mut clustered = Vec::with_capacity(children.len());
        for child in children {
            let Some(previous) = clustered.pop() else {
                clustered.push(child);
                continue;
            };
            match GuardedBranch::merge_complement(&self.domain, previous, child)? {
                Ok(merged) => {
                    self.changed = true;
                    clustered.push(merged);
                }
                Err((previous, child)) => {
                    clustered.push(previous);
                    clustered.push(child);
                }
            }
        }
        Ok(clustered)
    }
}

struct GuardedBranch {
    condition: SemanticPredicate,
    body: SemanticNode,
}

impl GuardedBranch {
    fn merge_complement(
        domain: &PathConditionDomain,
        left: SemanticNode,
        right: SemanticNode,
    ) -> Result<Result<SemanticNode, (SemanticNode, SemanticNode)>, SemanticFoldError> {
        let left = match Self::extract(left) {
            Ok(branch) => branch,
            Err(left) => return Ok(Err((left, right))),
        };
        let right = match Self::extract(right) {
            Ok(branch) => branch,
            Err(right) => return Ok(Err((left.into_node(), right))),
        };
        if !domain.complements(&left.condition, &right.condition)? {
            return Ok(Err((left.into_node(), right.into_node())));
        }
        Ok(Ok(SemanticNode::branch(
            left.condition,
            left.body,
            Some(right.body),
        )))
    }

    fn extract(node: SemanticNode) -> Result<Self, SemanticNode> {
        let SemanticNode::If {
            condition,
            then_node,
            else_node: None,
        } = node
        else {
            return Err(node);
        };
        let outer = condition.into_inner();
        match Self::extract(*then_node) {
            Ok(inner) => Ok(Self {
                condition: SemanticPredicate::And(vec![outer, inner.condition]),
                body: inner.body,
            }),
            Err(body) => Ok(Self {
                condition: outer,
                body,
            }),
        }
    }

    fn into_node(self) -> SemanticNode {
        SemanticNode::branch(self.condition, self.body, None)
    }
}

enum PredicateTask {
    Visit(BoolExpr),
    Not,
    Junction { count: usize, conjunction: bool },
}

enum ReductionTask {
    Visit {
        node: SemanticNode,
        care: Bdd,
        known: BooleanState,
    },
    Rebuild(ReductionFrame),
}

enum ReductionFrame {
    Sequence(usize),
    If {
        condition: crate::ir::SemanticOperand<SemanticPredicate>,
        has_else: bool,
    },
    Loop {
        control: crate::ir::SemanticLoopControl,
        header: Option<crate::ir::BlockId>,
        kind: SemanticLoopKind,
        condition: crate::ir::SemanticOperand<SemanticPredicate>,
    },
    For {
        control: crate::ir::SemanticLoopControl,
        init: crate::ir::SemanticStatement,
        condition: crate::ir::SemanticOperand<SemanticPredicate>,
        update: crate::ir::SemanticStatement,
    },
    ForEach {
        control: crate::ir::SemanticLoopControl,
        variable: crate::ir::RegisterArg,
        iterable: crate::ir::SemanticOperand<crate::ir::SemanticExpression>,
    },
    Switch {
        region: Option<crate::ir::RegionId>,
        selector: crate::ir::SemanticOperand<crate::ir::SemanticExpression>,
        metadata: Vec<(Vec<i32>, bool)>,
    },
    Try {
        region: crate::ir::RegionId,
        catch_metadata: Vec<(
            crate::ir::RegionId,
            Vec<crate::ir::ArgType>,
            Option<crate::ir::RegisterArg>,
        )>,
        finally_region: Option<crate::ir::RegionId>,
    },
    Synchronized {
        region: crate::ir::RegionId,
        lock: crate::ir::SemanticOperand<crate::ir::SemanticExpression>,
        method: bool,
    },
    Label(crate::ir::SemanticLabel),
}

impl ReductionFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(count) => *count,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::Loop { .. } => 2,
            Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized { .. }
            | Self::Label(_) => 1,
            Self::Switch { metadata, .. } => metadata.len(),
            Self::Try {
                catch_metadata,
                finally_region,
                ..
            } => 1 + catch_metadata.len() + usize::from(finally_region.is_some()),
        }
    }

    fn rebuild(self, children: Vec<SemanticNode>) -> Result<SemanticNode, SemanticFoldError> {
        if children.len() != self.child_count() {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        let mut children = children.into_iter();
        let node = match self {
            Self::Sequence(_) => SemanticNode::sequence(&mut children),
            Self::If {
                condition,
                has_else,
            } => SemanticNode::branch(
                condition.into_inner(),
                Self::child(&mut children)?,
                has_else.then(|| Self::child(&mut children)).transpose()?,
            ),
            Self::Loop {
                control,
                header,
                kind,
                condition,
            } => SemanticNode::Loop {
                control,
                header,
                kind,
                test: crate::ir::SemanticLoopTest {
                    setup: Box::new(Self::child(&mut children)?),
                    condition,
                },
                body: Box::new(Self::child(&mut children)?),
            },
            Self::For {
                control,
                init,
                condition,
                update,
            } => SemanticNode::For {
                control,
                init,
                condition,
                update,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::ForEach {
                control,
                variable,
                iterable,
            } => SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::Switch {
                region,
                selector,
                metadata,
            } => SemanticNode::Switch {
                region,
                selector,
                cases: metadata
                    .into_iter()
                    .map(|(values, is_default)| {
                        Ok(SemanticSwitchCase {
                            values,
                            is_default,
                            body: Self::child(&mut children)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SemanticFoldError>>()?,
            },
            Self::Try {
                region,
                catch_metadata,
                finally_region,
            } => {
                let body = Self::child(&mut children)?;
                let catches = catch_metadata
                    .into_iter()
                    .map(|(region, exception_types, exception_value)| {
                        Ok(SemanticCatch {
                            region,
                            exception_types,
                            exception_value,
                            body: Self::child(&mut children)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SemanticFoldError>>()?;
                let finally = match finally_region {
                    Some(region) => Some(SemanticFinally {
                        region,
                        body: Box::new(Self::child(&mut children)?),
                    }),
                    None => None,
                };
                SemanticNode::Try {
                    region,
                    body: Box::new(body),
                    catches,
                    finally,
                }
            }
            Self::Synchronized {
                region,
                lock,
                method,
            } => SemanticNode::Synchronized {
                region,
                lock,
                method,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::Label(label) => SemanticNode::Label {
                label,
                body: Box::new(Self::child(&mut children)?),
            },
        };
        if children.next().is_some() {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        Ok(node)
    }

    fn child(
        children: &mut impl Iterator<Item = SemanticNode>,
    ) -> Result<SemanticNode, SemanticFoldError> {
        children.next().ok_or(SemanticFoldError::MalformedWorkStack)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{InsnNode, LiteralArg, RegisterArg, SemanticStatement};

    fn comparison(id: usize, operator: IfOp) -> SemanticOperation {
        let mut instruction = InsnNode::new(InsnType::If, 0);
        instruction.id = InstructionId::new(id);
        instruction.payload.if_op = Some(operator);
        SemanticOperation::from_parts(
            instruction,
            vec![
                SemanticExpression::Register(RegisterArg::new_ssa(3, 1, ArgType::INT)),
                SemanticExpression::Literal(LiteralArg::int(0)),
            ],
            None,
        )
    }

    #[test]
    fn comparison_congruence_normalizes_complementary_relations() {
        let greater = ComparisonTest::analyze(&comparison(1, IfOp::Gt)).unwrap();
        let less_or_equal = ComparisonTest::analyze(&comparison(2, IfOp::Le)).unwrap();

        assert_eq!(greater.atom, less_or_equal.atom);
        assert_ne!(greater.polarity, less_or_equal.polarity);
    }

    fn source_boolean_test(id: usize, variable: u32) -> SemanticOperation {
        let mut register = RegisterArg::new_ssa(variable, 0, ArgType::BOOLEAN);
        register.code_var = Some(variable);
        let mut instruction = InsnNode::new(InsnType::If, 0);
        instruction.id = InstructionId::new(id);
        instruction.payload.if_op = Some(IfOp::Ne);
        SemanticOperation::from_parts(
            instruction,
            vec![
                SemanticExpression::Register(register),
                SemanticExpression::Literal(LiteralArg::new(0, ArgType::BOOLEAN)),
            ],
            None,
        )
    }

    fn source_result(register: u32, version: u32, variable: u32) -> RegisterArg {
        let mut result = RegisterArg::new_ssa(register, version, ArgType::BOOLEAN);
        result.code_var = Some(variable);
        result
    }

    #[test]
    fn predicate_catalog_includes_conditions_nested_in_test_operands() {
        let nested = comparison(2, IfOp::Ne);
        let select = SemanticExpression::select(
            SemanticPredicate::Test(nested.clone()),
            SemanticExpression::Literal(LiteralArg::int(1)),
            SemanticExpression::Literal(LiteralArg::int(0)),
        );
        let mut instruction = InsnNode::new(InsnType::If, 0);
        instruction.id = InstructionId::new(1);
        instruction.payload.if_op = Some(IfOp::Ne);
        let outer = SemanticOperation::from_parts(
            instruction,
            vec![select, SemanticExpression::Literal(LiteralArg::int(0))],
            None,
        );
        let root = SemanticNode::branch(
            SemanticPredicate::Test(outer.clone()),
            SemanticNode::BasicBlock(crate::ir::SemanticBlock {
                id: crate::ir::BlockId::new(0),
                statements: Vec::new(),
            }),
            None,
        );

        let catalog = PredicateCatalog::collect(&root);

        assert_eq!(
            catalog.symbols,
            BTreeSet::from([
                BoolVariable::Instruction(outer.id),
                BoolVariable::Instruction(nested.id),
            ])
        );
        assert_eq!(
            catalog.tests.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([outer.id, nested.id])
        );
    }

    #[test]
    fn relational_boolean_flow_removes_implied_conjuncts() {
        let x = source_boolean_test(1, 1);
        let y = source_boolean_test(2, 2);
        let catalog = PredicateCatalog {
            symbols: BTreeSet::from([
                BoolVariable::Instruction(x.id),
                BoolVariable::Instruction(y.id),
            ]),
            tests: BTreeMap::from([(x.id, x.clone()), (y.id, y.clone())]),
            occurrences: BTreeMap::new(),
        };
        let boolean_tests = BTreeMap::from([
            (
                x.id,
                BooleanTest {
                    variable: 1,
                    predicate_matches_source: true,
                },
            ),
            (
                y.id,
                BooleanTest {
                    variable: 2,
                    predicate_matches_source: true,
                },
            ),
        ]);
        let relations = BooleanRelations::new(&catalog, &boolean_tests);
        let mut entry = relations.initial_state();
        let initialize_y = SemanticStatement::definition(
            InstructionId::new(3),
            source_result(2, 1, 2),
            SemanticExpression::Literal(LiteralArg::new(0, ArgType::BOOLEAN)),
        );
        entry.relation = relations.assign(entry.relation, &initialize_y).unwrap();

        let x_predicate = SemanticPredicate::Test(x.clone());
        let mut when_true = entry.clone();
        when_true.relation = relations
            .assume(when_true.relation, &x_predicate, true)
            .unwrap();
        let assign_unknown_y = SemanticStatement::definition(
            InstructionId::new(4),
            source_result(2, 2, 2),
            SemanticExpression::Register(source_result(9, 0, 9)),
        );
        when_true.relation = relations
            .assign(when_true.relation, &assign_unknown_y)
            .unwrap();

        let mut when_false = entry;
        when_false.relation = relations
            .assume(when_false.relation, &x_predicate, false)
            .unwrap();
        let joined = relations.join(when_true, when_false).unwrap();
        let condition =
            SemanticPredicate::And(vec![x_predicate, SemanticPredicate::Test(y.clone())]);
        let (simplified, changed) = relations.simplify(condition, joined.relation).unwrap();

        assert!(changed);
        assert!(
            matches!(simplified, SemanticPredicate::Test(ref test) if test.id == y.id),
            "expected the stronger y predicate, got {simplified:#?}"
        );
    }
}
