use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    bdd::{Bdd, BddContext},
    BoolExpr, BoolVariable,
};

use super::{
    KotlinAssignOp, KotlinAstRewriter, KotlinAstTransform, KotlinBinaryOp, KotlinExpr,
    KotlinIdentifier, KotlinLiteral, KotlinMethodBody, KotlinPrimitiveType, KotlinStmt, KotlinType,
    KotlinUnaryOp,
};

mod decision_regions;
mod predicate_dag;

use decision_regions::DecisionRegionFormation;
use predicate_dag::PredicateDag;

#[derive(Debug, Default)]
pub struct DefiniteAssignment;

impl KotlinAstTransform for DefiniteAssignment {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        let declarations = Declarations::collect(&body.root);
        let mut changed = false;
        if !declarations.is_empty() {
            let mut analysis = AssignmentAnalysis::new(declarations);
            analysis.analyze(&body.root);
            changed |= analysis.initialize(&mut body.root);
        }

        let boolean_relations = BooleanRelations::collect(&body.root);
        let mut known = KnownValues::new(&boolean_relations);
        changed |= known.rewrite(&mut body.root).changed;
        if PredicateDag::recover(&mut body.root) {
            changed = true;
            let boolean_relations = BooleanRelations::collect(&body.root);
            let mut known = KnownValues::new(&boolean_relations);
            changed |= known.rewrite(&mut body.root).changed;
        }
        Ok(changed)
    }
}

struct KnownValues<'a> {
    values: BTreeMap<KotlinIdentifier, KotlinLiteral>,
    booleans: &'a BooleanRelations,
    relation: Bdd,
}

#[derive(Default)]
struct RewriteResult {
    changed: bool,
    completes: bool,
}

impl<'a> KnownValues<'a> {
    fn new(booleans: &'a BooleanRelations) -> Self {
        Self {
            values: BTreeMap::new(),
            booleans,
            relation: booleans.top(),
        }
    }

    fn rewrite(&mut self, statement: &mut KotlinStmt) -> RewriteResult {
        match statement {
            KotlinStmt::Empty => Self::complete(false),
            KotlinStmt::Block(statements) => self.sequence(statements),
            KotlinStmt::Variable { name, value, .. } => {
                self.values.remove(name);
                if let Some(value) = value {
                    let changed = self.simplify(value);
                    self.invalidate(value);
                    if let KotlinExpr::Literal(literal) = value {
                        self.values.insert(name.clone(), literal.clone());
                    }
                    self.assign_boolean(name, KotlinAssignOp::Assign, value);
                    return Self::complete(changed);
                } else {
                    self.forget_boolean(name);
                }
                Self::complete(false)
            }
            KotlinStmt::Assign { target, op, value } => {
                let changed = self.simplify(value);
                self.invalidate(value);
                self.invalidate(target);
                let KotlinExpr::Name(name) = target else {
                    return Self::complete(changed);
                };
                let operator = *op;
                let literal = (operator == KotlinAssignOp::Assign)
                    .then(|| match value {
                        KotlinExpr::Literal(literal) => Some(literal.clone()),
                        _ => None,
                    })
                    .flatten();
                if literal
                    .as_ref()
                    .is_some_and(|literal| self.values.get(name) == Some(literal))
                {
                    *statement = KotlinStmt::Empty;
                    return Self::complete(true);
                }
                self.values.remove(name);
                self.assign_boolean(name, operator, value);
                if let Some(literal) = literal {
                    self.values.insert(name.clone(), literal);
                }
                Self::complete(changed)
            }
            KotlinStmt::Expression(expression) => {
                let changed = self.simplify(expression);
                self.invalidate(expression);
                Self::complete(changed)
            }
            KotlinStmt::ConstructorInvocation { args, .. } => {
                let mut changed = false;
                for argument in args {
                    changed |= self.simplify(argument);
                    self.invalidate(argument);
                }
                Self::complete(changed)
            }
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                let condition_changed = self.simplify(condition);
                self.invalidate(condition);
                let incoming = self.values.clone();
                let when_true = self.branch(then_stmt, &incoming, self.assume(condition, true));
                let when_false = else_stmt
                    .as_deref_mut()
                    .map(|statement| {
                        self.branch(statement, &incoming, self.assume(condition, false))
                    })
                    .unwrap_or_else(|| {
                        (
                            Self::complete(false),
                            incoming.clone(),
                            self.assume(condition, false),
                        )
                    });
                self.values = Self::join(
                    (when_true.0.completes, when_true.1.clone()),
                    (when_false.0.completes, when_false.1.clone()),
                );
                self.relation = self.join_relations(
                    (when_true.0.completes, when_true.2),
                    (when_false.0.completes, when_false.2),
                );
                RewriteResult {
                    changed: condition_changed || when_true.0.changed || when_false.0.changed,
                    completes: when_true.0.completes || when_false.0.completes,
                }
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                let incoming = self.values.clone();
                let incoming_relation = self.relation;
                let mut writes = StatementWrites::default();
                writes.collect(body);
                for catch in catches.iter() {
                    writes.collect(&catch.body);
                }
                if let Some(finally) = finally.as_deref() {
                    writes.collect(finally);
                }
                let body_result = self.branch(body, &incoming, self.relation).0;
                let mut changed = body_result.changed;
                let mut completes = body_result.completes;
                for catch in catches {
                    let result = self.branch(&mut catch.body, &incoming, self.relation).0;
                    changed |= result.changed;
                    completes |= result.completes;
                }
                if let Some(finally) = finally {
                    let result = self.branch(finally, &incoming, self.relation).0;
                    changed |= result.changed;
                    completes &= result.completes;
                }
                self.values = incoming;
                self.relation = incoming_relation;
                for name in writes.names {
                    self.values.remove(&name);
                    self.forget_boolean(&name);
                }
                RewriteResult { changed, completes }
            }
            KotlinStmt::Synchronized { lock, body } => {
                let changed = self.simplify(lock);
                self.invalidate(lock);
                let mut result = self.rewrite(body);
                result.changed |= changed;
                result
            }
            KotlinStmt::Labeled { body, .. } => {
                let result = self.rewrite(body);
                self.values.clear();
                self.relation = self.booleans.top();
                result
            }
            KotlinStmt::While {
                condition, body, ..
            } => {
                self.forget_statement_writes(body);
                let condition_changed = self.simplify(condition);
                self.invalidate(condition);
                let incoming = self.values.clone();
                let result = self.branch(body, &incoming, self.assume(condition, true)).0;
                self.values.clear();
                self.relation = self.booleans.top();
                RewriteResult {
                    changed: condition_changed || result.changed,
                    completes: true,
                }
            }
            KotlinStmt::DoWhile {
                body, condition, ..
            } => {
                self.forget_statement_writes(body);
                let incoming = self.values.clone();
                let result = self.branch(body, &incoming, self.relation).0;
                let condition_changed = self.simplify(condition);
                self.invalidate(condition);
                self.values.clear();
                self.relation = self.booleans.top();
                RewriteResult {
                    changed: condition_changed || result.changed,
                    completes: true,
                }
            }
            KotlinStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                let mut result = self.sequence(init);
                self.forget_statement_writes(body);
                self.forget_expression_writes(update);
                if let Some(condition) = condition {
                    result.changed |= self.simplify(condition);
                    self.invalidate(condition);
                }
                let incoming = self.values.clone();
                let body_relation = condition
                    .as_ref()
                    .map(|condition| self.assume(condition, true))
                    .unwrap_or(self.relation);
                let body_result = self.branch(body, &incoming, body_relation).0;
                result.changed |= body_result.changed;
                for expression in update {
                    result.changed |= self.simplify(expression);
                    self.invalidate(expression);
                }
                self.values.clear();
                self.relation = self.booleans.top();
                result.completes = true;
                result
            }
            KotlinStmt::ForEach { iterable, body, .. } => {
                self.forget_statement_writes(body);
                let iterable_changed = self.simplify(iterable);
                self.invalidate(iterable);
                let incoming = self.values.clone();
                let result = self.branch(body, &incoming, self.relation).0;
                self.values.clear();
                self.relation = self.booleans.top();
                RewriteResult {
                    changed: iterable_changed || result.changed,
                    completes: true,
                }
            }
            KotlinStmt::Switch {
                selector, cases, ..
            } => {
                let selector_changed = self.simplify(selector);
                self.invalidate(selector);
                let incoming = self.values.clone();
                let mut changed = false;
                for case in cases {
                    let mut branch = Self::with_state(self.booleans, &incoming, self.relation);
                    changed |= branch.sequence(&mut case.body).changed;
                }
                self.values.clear();
                self.relation = self.booleans.top();
                RewriteResult {
                    changed: selector_changed || changed,
                    completes: true,
                }
            }
            KotlinStmt::Return(value) => {
                if let Some(value) = value {
                    let changed = self.simplify(value);
                    self.invalidate(value);
                    return RewriteResult {
                        changed,
                        completes: false,
                    };
                }
                Self::terminal()
            }
            KotlinStmt::Throw(value) => {
                let changed = self.simplify(value);
                self.invalidate(value);
                RewriteResult {
                    changed,
                    completes: false,
                }
            }
            KotlinStmt::Break(_) | KotlinStmt::Continue(_) => Self::terminal(),
        }
    }

    fn sequence(&mut self, statements: &mut Vec<KotlinStmt>) -> RewriteResult {
        let mut result = Self::complete(false);
        for statement in statements.iter_mut() {
            if !result.completes {
                break;
            }
            let next = self.rewrite(statement);
            result.changed |= next.changed;
            result.completes = next.completes;
        }
        if result.changed {
            statements.retain(|statement| !matches!(statement, KotlinStmt::Empty));
        }
        result.changed |= DecisionRegionFormation::new(self.booleans).rewrite(statements);
        result
    }

    fn branch(
        &self,
        statement: &mut KotlinStmt,
        incoming: &BTreeMap<KotlinIdentifier, KotlinLiteral>,
        relation: Bdd,
    ) -> (
        RewriteResult,
        BTreeMap<KotlinIdentifier, KotlinLiteral>,
        Bdd,
    ) {
        let mut branch = Self::with_state(self.booleans, incoming, relation);
        let result = branch.rewrite(statement);
        (result, branch.values, branch.relation)
    }

    fn join(
        left: (bool, BTreeMap<KotlinIdentifier, KotlinLiteral>),
        right: (bool, BTreeMap<KotlinIdentifier, KotlinLiteral>),
    ) -> BTreeMap<KotlinIdentifier, KotlinLiteral> {
        match (left.0, right.0) {
            (true, false) => left.1,
            (false, true) => right.1,
            (false, false) => BTreeMap::new(),
            (true, true) => {
                let mut joined = left.1;
                joined.retain(|name, value| right.1.get(name) == Some(value));
                joined
            }
        }
    }

    fn invalidate(&mut self, expression: &KotlinExpr) {
        let mut writes = ExpressionWrites::default();
        writes.rewrite_expression(expression.clone());
        for name in writes.names {
            self.values.remove(&name);
            self.forget_boolean(&name);
        }
    }

    fn forget_statement_writes(&mut self, statement: &KotlinStmt) {
        let mut writes = StatementWrites::default();
        writes.collect(statement);
        self.forget_names(writes.names);
    }

    fn forget_expression_writes(&mut self, expressions: &[KotlinExpr]) {
        let mut writes = ExpressionWrites::default();
        for expression in expressions {
            writes.rewrite_expression(expression.clone());
        }
        self.forget_names(writes.names);
    }

    fn forget_names(&mut self, names: BTreeSet<KotlinIdentifier>) {
        for name in names {
            self.values.remove(&name);
            self.forget_boolean(&name);
        }
    }

    fn with_state(
        booleans: &'a BooleanRelations,
        values: &BTreeMap<KotlinIdentifier, KotlinLiteral>,
        relation: Bdd,
    ) -> Self {
        Self {
            values: values.clone(),
            booleans,
            relation,
        }
    }

    fn simplify(&self, expression: &mut KotlinExpr) -> bool {
        let mut writes = ExpressionWrites::default();
        writes.rewrite_expression(expression.clone());
        if !writes.names.is_empty() {
            return false;
        }
        let mut simplifier = BooleanExpressionSimplifier {
            booleans: self.booleans,
            relation: self.relation,
            changed: false,
        };
        *expression = simplifier.rewrite_expression(expression.clone());
        simplifier.changed
    }

    fn assume(&self, condition: &KotlinExpr, expected: bool) -> Bdd {
        self.booleans
            .assume(self.relation, condition, expected)
            .unwrap_or(self.relation)
    }

    fn forget_boolean(&mut self, name: &KotlinIdentifier) {
        self.relation = self
            .booleans
            .forget(self.relation, name)
            .unwrap_or_else(|_| self.booleans.top());
    }

    fn assign_boolean(
        &mut self,
        name: &KotlinIdentifier,
        operator: KotlinAssignOp,
        value: &KotlinExpr,
    ) {
        self.relation = self
            .booleans
            .assign(self.relation, name, operator, value)
            .unwrap_or_else(|_| self.booleans.top());
    }

    fn join_relations(&self, left: (bool, Bdd), right: (bool, Bdd)) -> Bdd {
        match (left.0, right.0) {
            (true, false) => left.1,
            (false, true) => right.1,
            (false, false) => self.booleans.top(),
            (true, true) => self
                .booleans
                .join(left.1, right.1)
                .unwrap_or_else(|_| self.booleans.top()),
        }
    }

    fn complete(changed: bool) -> RewriteResult {
        RewriteResult {
            changed,
            completes: true,
        }
    }

    fn terminal() -> RewriteResult {
        RewriteResult {
            changed: false,
            completes: false,
        }
    }
}

struct BooleanRelations {
    bdd: BddContext,
    universe: Bdd,
    expressions: BTreeMap<BoolVariable, KotlinExpr>,
    dependencies: BTreeMap<BoolVariable, BTreeSet<KotlinIdentifier>>,
}

impl BooleanRelations {
    fn collect(root: &KotlinStmt) -> Self {
        let mut names = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(statement) = pending.pop() {
            match statement {
                KotlinStmt::Variable {
                    ty: KotlinType::Primitive(KotlinPrimitiveType::Boolean),
                    name,
                    ..
                } => {
                    names.insert(name.clone());
                }
                KotlinStmt::Block(statements) => pending.extend(statements),
                KotlinStmt::Labeled { body, .. }
                | KotlinStmt::While { body, .. }
                | KotlinStmt::DoWhile { body, .. }
                | KotlinStmt::ForEach { body, .. }
                | KotlinStmt::Synchronized { body, .. } => pending.push(body),
                KotlinStmt::For { init, body, .. } => {
                    pending.extend(init);
                    pending.push(body);
                }
                KotlinStmt::If {
                    then_stmt,
                    else_stmt,
                    ..
                } => {
                    pending.push(then_stmt);
                    pending.extend(else_stmt.as_deref());
                }
                KotlinStmt::Switch { cases, .. } => {
                    pending.extend(cases.iter().flat_map(|case| &case.body));
                }
                KotlinStmt::Try {
                    body,
                    catches,
                    finally,
                } => {
                    pending.push(body);
                    pending.extend(catches.iter().map(|catch| &catch.body));
                    pending.extend(finally.as_deref());
                }
                KotlinStmt::Empty
                | KotlinStmt::Expression(_)
                | KotlinStmt::ConstructorInvocation { .. }
                | KotlinStmt::Assign { .. }
                | KotlinStmt::Return(_)
                | KotlinStmt::Throw(_)
                | KotlinStmt::Break(_)
                | KotlinStmt::Continue(_)
                | KotlinStmt::Variable { .. } => {}
            }
        }
        let mut expressions = names
            .into_iter()
            .map(|name| {
                (
                    BoolVariable::Named(name.as_str().to_owned()),
                    KotlinExpr::Name(name),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut atoms = BooleanAtomCollector::default();
        atoms.rewrite_statement(root.clone());
        let mut dependencies = BTreeMap::new();
        for (index, atom) in atoms.atoms.into_iter().enumerate() {
            let Ok(index) = u32::try_from(index) else {
                break;
            };
            let symbol = BoolVariable::Atom(index);
            dependencies.insert(symbol.clone(), Self::names_in(&atom));
            expressions.insert(symbol, atom);
        }
        let bdd = BddContext::new(&expressions.keys().cloned().collect::<BTreeSet<_>>());
        let universe = Self::equality_theory(&bdd, &expressions).unwrap_or_else(|_| bdd.truth());
        Self {
            bdd,
            universe,
            expressions,
            dependencies,
        }
    }

    fn top(&self) -> Bdd {
        self.universe
    }

    fn symbol(&self, name: &KotlinIdentifier) -> Option<BoolVariable> {
        let symbol = BoolVariable::Named(name.as_str().to_owned());
        self.expressions.contains_key(&symbol).then_some(symbol)
    }

    fn forget(
        &self,
        relation: Bdd,
        name: &KotlinIdentifier,
    ) -> Result<Bdd, crate::ir::bdd::BddError> {
        let mut forgotten = self
            .dependencies
            .iter()
            .filter(|(_, dependencies)| dependencies.contains(name))
            .map(|(symbol, _)| symbol.clone())
            .collect::<BTreeSet<_>>();
        if let Some(symbol) = self.symbol(name) {
            forgotten.insert(symbol);
        }
        if forgotten.is_empty() {
            return Ok(relation);
        }
        let relation = self.bdd.exists(relation, &forgotten)?;
        self.bdd.and(relation, self.universe)
    }

    fn assign(
        &self,
        relation: Bdd,
        name: &KotlinIdentifier,
        operator: KotlinAssignOp,
        value: &KotlinExpr,
    ) -> Result<Bdd, crate::ir::bdd::BddError> {
        let relation = self.forget(relation, name)?;
        let Some(target_symbol) = self.symbol(name) else {
            return Ok(relation);
        };
        if operator != KotlinAssignOp::Assign {
            return Ok(relation);
        }
        let Some(value) = self.expression(value) else {
            return Ok(relation);
        };
        if value.symbols().contains(&target_symbol) {
            return Ok(relation);
        }
        let target = BoolExpr::Symbol(target_symbol);
        let equality = BoolExpr::or(vec![
            BoolExpr::and(vec![target.clone(), value.clone()]),
            BoolExpr::and(vec![BoolExpr::not(target), BoolExpr::not(value)]),
        ]);
        self.bdd.and(relation, self.bdd.compile(&equality)?)
    }

    fn assume(
        &self,
        relation: Bdd,
        condition: &KotlinExpr,
        expected: bool,
    ) -> Result<Bdd, crate::ir::bdd::BddError> {
        let Some(condition) = self.expression(condition) else {
            return Ok(relation);
        };
        let condition = self.bdd.compile(&condition)?;
        let condition = if expected {
            condition
        } else {
            self.bdd.not(condition)?
        };
        self.bdd.and(relation, condition)
    }

    fn join(&self, left: Bdd, right: Bdd) -> Result<Bdd, crate::ir::bdd::BddError> {
        self.bdd.or(left, right)
    }

    fn simplify(&self, expression: KotlinExpr, relation: Bdd) -> KotlinExpr {
        if relation.is_false() {
            return expression;
        }
        let Some(symbolic) = self.expression(&expression) else {
            return expression;
        };
        let original_symbols = symbolic.symbols();
        let reduction_domain = self.reduction_domain(&original_symbols);
        let Some((reduced, nodes)) = self
            .bdd
            .reduce_under_with_support(&symbolic, relation, &reduction_domain, 128)
            .ok()
            .flatten()
        else {
            return expression;
        };
        if nodes > expression.cost() || !reduced.symbols().is_subset(&reduction_domain) {
            return expression;
        }
        self.lower(reduced)
            .filter(|replacement| replacement != &expression)
            .unwrap_or(expression)
    }

    fn simplify_theoretic(&self, expression: KotlinExpr) -> KotlinExpr {
        let Some(symbolic) = self.expression(&expression) else {
            return expression;
        };
        let original_symbols = symbolic.symbols();
        let Some((bdd, theory)) = self.local_domain([&symbolic]) else {
            return expression;
        };
        let Some((reduced, nodes)) = bdd.reduce_under(&symbolic, theory, 128).ok().flatten() else {
            return expression;
        };
        if nodes > expression.cost() || !reduced.symbols().is_subset(&original_symbols) {
            return expression;
        }
        self.lower(reduced)
            .filter(|replacement| replacement != &expression)
            .unwrap_or(expression)
    }

    fn split_value(
        &self,
        value: &KotlinExpr,
        condition: &KotlinExpr,
    ) -> Option<(KotlinExpr, KotlinExpr)> {
        if let KotlinExpr::Conditional {
            condition: nested,
            when_true,
            when_false,
        } = value
        {
            return match self.condition_polarity(nested, condition)? {
                true => Some((when_true.as_ref().clone(), when_false.as_ref().clone())),
                false => Some((when_false.as_ref().clone(), when_true.as_ref().clone())),
            };
        }

        let value = self.expression(value)?;
        let condition = self.expression(condition)?;
        let (bdd, theory) = self.local_domain([&value, &condition])?;
        let condition = bdd.compile(&condition).ok()?;
        let when_true = bdd.and(theory, condition).ok()?;
        let when_false = bdd.and(theory, bdd.not(condition).ok()?).ok()?;
        let when_true = bdd
            .reduce_under(&value, when_true, 128)
            .ok()
            .flatten()
            .and_then(|(value, _)| self.lower(value))?;
        let when_false = bdd
            .reduce_under(&value, when_false, 128)
            .ok()
            .flatten()
            .and_then(|(value, _)| self.lower(value))?;
        (when_true != when_false).then_some((when_true, when_false))
    }

    fn condition_polarity(&self, left: &KotlinExpr, right: &KotlinExpr) -> Option<bool> {
        if left == right {
            return Some(true);
        }
        let left = self.expression(left)?;
        let right = self.expression(right)?;
        let (bdd, theory) = self.local_domain([&left, &right])?;
        let left = bdd.compile(&left).ok()?;
        let right = bdd.compile(&right).ok()?;
        if bdd.equivalent_under(theory, left, right).ok()? {
            return Some(true);
        }
        let negated = bdd.not(right).ok()?;
        bdd.equivalent_under(theory, left, negated)
            .ok()?
            .then_some(false)
    }

    fn local_domain<'a>(
        &self,
        expressions: impl IntoIterator<Item = &'a BoolExpr>,
    ) -> Option<(BddContext, Bdd)> {
        let symbols = expressions
            .into_iter()
            .flat_map(BoolExpr::symbols)
            .collect::<BTreeSet<_>>();
        let bdd = BddContext::new(&symbols);
        let relevant = self
            .expressions
            .iter()
            .filter(|(symbol, _)| symbols.contains(*symbol))
            .map(|(symbol, expression)| (symbol.clone(), expression.clone()))
            .collect::<BTreeMap<_, _>>();
        let theory = Self::equality_theory(&bdd, &relevant).ok()?;
        Some((bdd, theory))
    }

    fn equality_theory(
        bdd: &BddContext,
        expressions: &BTreeMap<BoolVariable, KotlinExpr>,
    ) -> Result<Bdd, crate::ir::bdd::BddError> {
        let equalities = expressions
            .iter()
            .filter_map(|(symbol, expression)| {
                Self::equality_fact(expression)
                    .map(|(subject, constant)| (symbol.clone(), subject, constant))
            })
            .collect::<Vec<_>>();
        let mut clauses = Vec::new();
        for (index, (left_symbol, left_subject, left_constant)) in equalities.iter().enumerate() {
            for (right_symbol, right_subject, right_constant) in &equalities[index + 1..] {
                if left_subject == right_subject
                    && Self::provably_distinct(left_constant, right_constant)
                {
                    clauses.push(BoolExpr::or(vec![
                        BoolExpr::not(BoolExpr::Symbol(left_symbol.clone())),
                        BoolExpr::not(BoolExpr::Symbol(right_symbol.clone())),
                    ]));
                }
            }
        }
        bdd.compile(&BoolExpr::and(clauses))
    }

    fn reduction_domain(&self, original: &BTreeSet<BoolVariable>) -> BTreeSet<BoolVariable> {
        let subjects = original
            .iter()
            .filter_map(|symbol| self.expressions.get(symbol))
            .filter_map(Self::equality_fact)
            .map(|(subject, _)| subject)
            .fold(Vec::new(), |mut subjects, subject| {
                if !subjects.contains(&subject) {
                    subjects.push(subject);
                }
                subjects
            });
        if subjects.is_empty() {
            return original.clone();
        }

        let mut domain = original.clone();
        domain.extend(self.expressions.iter().filter_map(|(symbol, expression)| {
            Self::equality_fact(expression)
                .is_some_and(|(subject, _)| subjects.contains(&subject))
                .then(|| symbol.clone())
        }));
        domain
    }

    fn equality_fact(expression: &KotlinExpr) -> Option<(KotlinExpr, KotlinLiteral)> {
        let KotlinExpr::Binary {
            left,
            op: KotlinBinaryOp::Equal,
            right,
        } = expression
        else {
            return None;
        };
        match (left.as_ref(), right.as_ref()) {
            (subject, KotlinExpr::Literal(constant)) if Self::theory_subject(subject) => {
                Some((subject.clone(), constant.clone()))
            }
            (KotlinExpr::Literal(constant), subject) if Self::theory_subject(subject) => {
                Some((subject.clone(), constant.clone()))
            }
            _ => None,
        }
    }

    fn theory_subject(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::Name(_) => true,
            KotlinExpr::Cast { value, .. } => Self::theory_subject(value),
            _ => false,
        }
    }

    fn provably_distinct(left: &KotlinLiteral, right: &KotlinLiteral) -> bool {
        match (left, right) {
            (KotlinLiteral::Boolean(left), KotlinLiteral::Boolean(right)) => left != right,
            (KotlinLiteral::Integer(left), KotlinLiteral::Integer(right)) => left != right,
            (KotlinLiteral::Long(left), KotlinLiteral::Long(right)) => left != right,
            (KotlinLiteral::Character(left), KotlinLiteral::Character(right)) => left != right,
            _ => false,
        }
    }

    fn expression(&self, expression: &KotlinExpr) -> Option<BoolExpr> {
        match expression {
            KotlinExpr::Name(name) => self.symbol(name).map(BoolExpr::Symbol),
            KotlinExpr::Literal(KotlinLiteral::Boolean(true)) => Some(BoolExpr::True),
            KotlinExpr::Literal(KotlinLiteral::Boolean(false)) => Some(BoolExpr::False),
            KotlinExpr::Unary {
                op: KotlinUnaryOp::LogicalNot,
                operand,
            } => self.expression(operand).map(BoolExpr::not),
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::LogicalAnd,
                right,
            } => Some(BoolExpr::and(vec![
                self.expression(left)?,
                self.expression(right)?,
            ])),
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::LogicalOr,
                right,
            } => Some(BoolExpr::or(vec![
                self.expression(left)?,
                self.expression(right)?,
            ])),
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::Equal,
                right,
            } => match (self.expression(left), self.expression(right)) {
                (Some(left), Some(right)) => Some(BoolExpr::or(vec![
                    BoolExpr::and(vec![left.clone(), right.clone()]),
                    BoolExpr::and(vec![BoolExpr::not(left), BoolExpr::not(right)]),
                ])),
                _ => self.atom(expression),
            },
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::NotEqual,
                right,
            } => match (self.expression(left), self.expression(right)) {
                (Some(left), Some(right)) => Some(BoolExpr::or(vec![
                    BoolExpr::and(vec![left.clone(), BoolExpr::not(right.clone())]),
                    BoolExpr::and(vec![BoolExpr::not(left), right]),
                ])),
                _ => self.atom(expression),
            },
            _ => self.atom(expression),
        }
    }

    fn lower(&self, expression: BoolExpr) -> Option<KotlinExpr> {
        match expression {
            BoolExpr::True => Some(KotlinExpr::Literal(KotlinLiteral::Boolean(true))),
            BoolExpr::False => Some(KotlinExpr::Literal(KotlinLiteral::Boolean(false))),
            BoolExpr::Symbol(symbol) => self.expressions.get(&symbol).cloned(),
            BoolExpr::Not(inner) => Some(self.lower(*inner)?.negated()),
            BoolExpr::And(terms) => self.lower_junction(terms, KotlinBinaryOp::LogicalAnd),
            BoolExpr::Or(terms) => self.lower_junction(terms, KotlinBinaryOp::LogicalOr),
        }
    }

    fn lower_junction(&self, terms: Vec<BoolExpr>, operator: KotlinBinaryOp) -> Option<KotlinExpr> {
        let mut terms = terms.into_iter().map(|term| self.lower(term));
        let first = terms.next()??;
        terms.try_fold(first, |left, right| {
            Some(KotlinExpr::Binary {
                left: Box::new(left),
                op: operator,
                right: Box::new(right?),
            })
        })
    }

    fn atom(&self, expression: &KotlinExpr) -> Option<BoolExpr> {
        let (base, negated) = Self::atomic_base(expression)?;
        let symbol = self
            .expressions
            .iter()
            .find(|(symbol, candidate)| {
                matches!(symbol, BoolVariable::Atom(_)) && Self::same_atom(candidate, &base)
            })
            .map(|(symbol, _)| symbol.clone())?;
        let atom = BoolExpr::Symbol(symbol);
        Some(if negated { BoolExpr::not(atom) } else { atom })
    }

    fn atomic_base(expression: &KotlinExpr) -> Option<(KotlinExpr, bool)> {
        match expression {
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::Equal,
                right,
            } if Self::stable_value(left) && Self::stable_value(right) => {
                Some((expression.clone(), false))
            }
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::NotEqual,
                right,
            } if Self::stable_value(left) && Self::stable_value(right) => Some((
                KotlinExpr::Binary {
                    left: left.clone(),
                    op: KotlinBinaryOp::Equal,
                    right: right.clone(),
                },
                true,
            )),
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::ReferentialEqual,
                right,
            } if Self::stable_value(left) && Self::stable_value(right) => {
                Some((expression.clone(), false))
            }
            KotlinExpr::Binary {
                left,
                op: KotlinBinaryOp::ReferentialNotEqual,
                right,
            } if Self::stable_value(left) && Self::stable_value(right) => Some((
                KotlinExpr::Binary {
                    left: left.clone(),
                    op: KotlinBinaryOp::ReferentialEqual,
                    right: right.clone(),
                },
                true,
            )),
            KotlinExpr::InstanceOf { value, .. } if Self::stable_value(value) => {
                Some((expression.clone(), false))
            }
            _ => None,
        }
    }

    fn stable_value(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Name(_)
            | KotlinExpr::Literal(_)
            | KotlinExpr::ClassLiteral(_)
            | KotlinExpr::ObjectReference(_) => true,
            KotlinExpr::Unary {
                op: KotlinUnaryOp::Negate | KotlinUnaryOp::BitwiseNot,
                operand,
            }
            | KotlinExpr::Cast { value: operand, .. } => Self::stable_value(operand),
            _ => false,
        }
    }

    fn same_atom(left: &KotlinExpr, right: &KotlinExpr) -> bool {
        if left == right {
            return true;
        }
        let (
            KotlinExpr::Binary {
                left: left_a,
                op: left_op,
                right: left_b,
            },
            KotlinExpr::Binary {
                left: right_b,
                op: right_op,
                right: right_a,
            },
        ) = (left, right)
        else {
            return false;
        };
        left_op == right_op
            && matches!(
                left_op,
                KotlinBinaryOp::Equal | KotlinBinaryOp::ReferentialEqual
            )
            && left_a == right_a
            && left_b == right_b
    }

    fn names_in(expression: &KotlinExpr) -> BTreeSet<KotlinIdentifier> {
        let mut collector = ExpressionNames::default();
        collector.rewrite_expression(expression.clone());
        collector.names
    }
}

#[derive(Default)]
struct BooleanAtomCollector {
    atoms: Vec<KotlinExpr>,
}

impl KotlinAstRewriter for BooleanAtomCollector {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let Some((atom, _)) = BooleanRelations::atomic_base(&expression) {
            if !self
                .atoms
                .iter()
                .any(|candidate| BooleanRelations::same_atom(candidate, &atom))
            {
                self.atoms.push(atom);
            }
        }
        expression
    }
}

#[derive(Default)]
struct ExpressionNames {
    names: BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for ExpressionNames {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Name(name) = &expression {
            self.names.insert(name.clone());
        }
        expression
    }
}

struct BooleanExpressionSimplifier<'a> {
    booleans: &'a BooleanRelations,
    relation: Bdd,
    changed: bool,
}

impl KotlinAstRewriter for BooleanExpressionSimplifier<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        let local = self.booleans.simplify_theoretic(expression.clone());
        let reduced = self.booleans.simplify(local, self.relation);
        self.changed |= reduced != expression;
        reduced
    }
}

#[derive(Default)]
struct ExpressionWrites {
    names: BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for ExpressionWrites {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match &expression {
            KotlinExpr::Assignment { target, .. } | KotlinExpr::Update { target, .. } => {
                if let KotlinExpr::Name(name) = target.as_ref() {
                    self.names.insert(name.clone());
                }
            }
            _ => {}
        }
        expression
    }
}

#[derive(Default)]
struct StatementWrites {
    names: BTreeSet<KotlinIdentifier>,
}

impl StatementWrites {
    fn collect(&mut self, statement: &KotlinStmt) {
        self.rewrite_statement(statement.clone());
    }

    fn record_target(&mut self, target: &KotlinExpr) {
        if let KotlinExpr::Name(name) = target {
            self.names.insert(name.clone());
        }
    }
}

impl KotlinAstRewriter for StatementWrites {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Assignment { target, .. } | KotlinExpr::Update { target, .. } =
            &expression
        {
            self.record_target(target);
        }
        expression
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match &statement {
            KotlinStmt::Variable { name, .. } | KotlinStmt::ForEach { variable: name, .. } => {
                self.names.insert(name.clone());
            }
            KotlinStmt::Assign { target, .. } => self.record_target(target),
            KotlinStmt::Empty
            | KotlinStmt::Block(_)
            | KotlinStmt::Labeled { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::If { .. }
            | KotlinStmt::While { .. }
            | KotlinStmt::DoWhile { .. }
            | KotlinStmt::For { .. }
            | KotlinStmt::Switch { .. }
            | KotlinStmt::Try { .. }
            | KotlinStmt::Synchronized { .. }
            | KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => {}
        }
        statement
    }
}

#[derive(Debug, Default)]
struct Declarations(BTreeMap<KotlinIdentifier, KotlinType>);

impl Declarations {
    fn collect(root: &KotlinStmt) -> Self {
        let mut declarations = Self::default();
        let mut pending = vec![root];
        while let Some(statement) = pending.pop() {
            match statement {
                KotlinStmt::Variable {
                    ty,
                    name,
                    value: None,
                    ..
                } => {
                    declarations.0.insert(name.clone(), ty.clone());
                }
                KotlinStmt::Block(children) => pending.extend(children),
                KotlinStmt::Labeled { body, .. }
                | KotlinStmt::While { body, .. }
                | KotlinStmt::DoWhile { body, .. }
                | KotlinStmt::For { body, .. }
                | KotlinStmt::ForEach { body, .. }
                | KotlinStmt::Synchronized { body, .. } => pending.push(body),
                KotlinStmt::If {
                    then_stmt,
                    else_stmt,
                    ..
                } => {
                    pending.push(then_stmt);
                    if let Some(else_stmt) = else_stmt {
                        pending.push(else_stmt);
                    }
                }
                KotlinStmt::Switch { cases, .. } => {
                    pending.extend(cases.iter().flat_map(|case| case.body.iter()));
                }
                KotlinStmt::Try {
                    body,
                    catches,
                    finally,
                } => {
                    pending.push(body);
                    pending.extend(catches.iter().map(|catch| &catch.body));
                    if let Some(finally) = finally {
                        pending.push(finally);
                    }
                }
                KotlinStmt::Empty
                | KotlinStmt::Expression(_)
                | KotlinStmt::ConstructorInvocation { .. }
                | KotlinStmt::Assign { .. }
                | KotlinStmt::Return(_)
                | KotlinStmt::Throw(_)
                | KotlinStmt::Break(_)
                | KotlinStmt::Continue(_)
                | KotlinStmt::Variable { .. } => {}
            }
        }
        declarations
    }

    fn is_candidate(&self, name: &KotlinIdentifier) -> bool {
        self.0.contains_key(name)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Debug, Clone)]
struct Flow {
    assigned: BTreeSet<KotlinIdentifier>,
    completes: bool,
}

impl Default for Flow {
    fn default() -> Self {
        Self {
            assigned: BTreeSet::new(),
            completes: true,
        }
    }
}

impl Flow {
    fn normal_join(flows: impl IntoIterator<Item = Self>) -> Self {
        let mut normal = flows.into_iter().filter(|flow| flow.completes);
        let Some(mut joined) = normal.next() else {
            return Self {
                assigned: BTreeSet::new(),
                completes: false,
            };
        };
        for flow in normal {
            joined.assigned.retain(|name| flow.assigned.contains(name));
        }
        joined
    }
}

#[derive(Debug)]
struct AssignmentAnalysis {
    declarations: Declarations,
    required: BTreeSet<KotlinIdentifier>,
}

impl AssignmentAnalysis {
    fn new(declarations: Declarations) -> Self {
        Self {
            declarations,
            required: BTreeSet::new(),
        }
    }

    fn analyze(&mut self, root: &KotlinStmt) {
        self.statement(root, Flow::default());
    }

    fn statement(&mut self, statement: &KotlinStmt, mut flow: Flow) -> Flow {
        match statement {
            KotlinStmt::Empty => flow,
            KotlinStmt::Block(statements) => self.sequence(statements, flow),
            KotlinStmt::Labeled { body, .. } => {
                let body_flow = self.statement(body, flow.clone());
                Flow::normal_join([flow, body_flow])
            }
            KotlinStmt::Variable { name, value, .. } => {
                flow.assigned.remove(name);
                if let Some(value) = value {
                    self.expression(value, &mut flow.assigned);
                    flow.assigned.insert(name.clone());
                }
                flow
            }
            KotlinStmt::Expression(expression) => {
                self.expression(expression, &mut flow.assigned);
                flow
            }
            KotlinStmt::ConstructorInvocation { args, .. } => {
                self.expressions(args, &mut flow.assigned);
                flow
            }
            KotlinStmt::Assign { target, op, value } => {
                self.assignment(target, *op, value, &mut flow.assigned);
                flow
            }
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                self.expression(condition, &mut flow.assigned);
                let when_true = self.statement(then_stmt, flow.clone());
                let when_false = else_stmt
                    .as_deref()
                    .map(|statement| self.statement(statement, flow.clone()))
                    .unwrap_or(flow);
                Flow::normal_join([when_true, when_false])
            }
            KotlinStmt::While {
                condition, body, ..
            } => {
                self.expression(condition, &mut flow.assigned);
                self.statement(body, flow.clone());
                flow
            }
            KotlinStmt::DoWhile {
                body, condition, ..
            } => {
                let body_flow = self.statement(body, flow.clone());
                let mut condition_flow = if body_flow.completes {
                    body_flow
                } else {
                    flow.clone()
                };
                self.expression(condition, &mut condition_flow.assigned);
                Flow::normal_join([flow, condition_flow])
            }
            KotlinStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                flow = self.sequence(init, flow);
                if !flow.completes {
                    return flow;
                }
                if let Some(condition) = condition {
                    self.expression(condition, &mut flow.assigned);
                }
                let mut iteration = self.statement(body, flow.clone());
                if !iteration.completes {
                    iteration = flow.clone();
                }
                self.expressions(update, &mut iteration.assigned);
                Flow::normal_join([flow, iteration])
            }
            KotlinStmt::ForEach {
                variable,
                iterable,
                body,
                ..
            } => {
                self.expression(iterable, &mut flow.assigned);
                let mut iteration = flow.clone();
                iteration.assigned.insert(variable.clone());
                self.statement(body, iteration);
                flow
            }
            KotlinStmt::Switch {
                selector, cases, ..
            } => {
                self.expression(selector, &mut flow.assigned);
                let branches = std::iter::once(flow.clone()).chain(
                    cases
                        .iter()
                        .map(|case| self.sequence(&case.body, flow.clone())),
                );
                Flow::normal_join(branches)
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                let body_flow = self.statement(body, flow.clone());
                let branches = std::iter::once(body_flow).chain(catches.iter().map(|catch| {
                    let mut catch_flow = flow.clone();
                    catch_flow.assigned.insert(catch.variable.clone());
                    self.statement(&catch.body, catch_flow)
                }));
                let joined = Flow::normal_join(branches);
                let Some(finally) = finally else {
                    return joined;
                };
                // A finally block is also reached by exceptional edges from
                // any point in the protected body or a handler.
                self.statement(finally, flow.clone());
                let joined_completes = joined.completes;
                let finally_flow = self.statement(finally, joined);
                if joined_completes && finally_flow.completes {
                    finally_flow
                } else {
                    Flow {
                        assigned: BTreeSet::new(),
                        completes: false,
                    }
                }
            }
            KotlinStmt::Synchronized { lock, body } => {
                self.expression(lock, &mut flow.assigned);
                self.statement(body, flow)
            }
            KotlinStmt::Return(value) => {
                if let Some(value) = value {
                    self.expression(value, &mut flow.assigned);
                }
                flow.completes = false;
                flow
            }
            KotlinStmt::Throw(value) => {
                self.expression(value, &mut flow.assigned);
                flow.completes = false;
                flow
            }
            KotlinStmt::Break(_) | KotlinStmt::Continue(_) => {
                flow.completes = false;
                flow
            }
        }
    }

    fn sequence(&mut self, statements: &[KotlinStmt], mut flow: Flow) -> Flow {
        for statement in statements {
            if !flow.completes {
                break;
            }
            flow = self.statement(statement, flow);
        }
        flow
    }

    fn expressions(
        &mut self,
        expressions: &[KotlinExpr],
        assigned: &mut BTreeSet<KotlinIdentifier>,
    ) {
        for expression in expressions {
            self.expression(expression, assigned);
        }
    }

    fn expression(&mut self, expression: &KotlinExpr, assigned: &mut BTreeSet<KotlinIdentifier>) {
        match expression {
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::Literal(_)
            | KotlinExpr::ClassLiteral(_)
            | KotlinExpr::ObjectReference(_)
            | KotlinExpr::StaticField { .. } => {}
            KotlinExpr::Name(name) => self.read(name, assigned),
            KotlinExpr::SmartCast(value)
            | KotlinExpr::NonNullAssertion(value)
            | KotlinExpr::JvmIntrinsic {
                expression: value, ..
            } => self.expression(value, assigned),
            KotlinExpr::Field { owner, .. } => self.expression(owner, assigned),
            KotlinExpr::ArrayAccess { array, index } => {
                self.expression(array, assigned);
                self.expression(index, assigned);
            }
            KotlinExpr::Call { receiver, args, .. } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver, assigned);
                }
                self.expressions(args, assigned);
            }
            KotlinExpr::MethodReference { receiver, .. } => {
                self.expression(receiver, assigned);
            }
            KotlinExpr::Lambda { body, .. } => {
                let mut lambda_assigned = assigned.clone();
                self.expression(body, &mut lambda_assigned);
            }
            KotlinExpr::BlockLambda { body, .. } => {
                self.statement(
                    body,
                    Flow {
                        assigned: assigned.clone(),
                        completes: true,
                    },
                );
            }
            KotlinExpr::New {
                enclosing, args, ..
            } => {
                if let Some(enclosing) = enclosing {
                    self.expression(enclosing, assigned);
                }
                self.expressions(args, assigned);
            }
            KotlinExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => {
                self.expressions(dimensions, assigned);
                self.expressions(initializer, assigned);
            }
            KotlinExpr::Unary { operand, .. }
            | KotlinExpr::Cast { value: operand, .. }
            | KotlinExpr::InstanceOf { value: operand, .. } => self.expression(operand, assigned),
            KotlinExpr::Update { target, .. } => {
                match target.as_ref() {
                    KotlinExpr::Name(name) => self.read(name, assigned),
                    target => self.expression(target, assigned),
                }
                if let KotlinExpr::Name(name) = target.as_ref() {
                    assigned.insert(name.clone());
                }
            }
            KotlinExpr::Binary { left, op, right } => {
                self.expression(left, assigned);
                if matches!(op, KotlinBinaryOp::LogicalAnd | KotlinBinaryOp::LogicalOr) {
                    let skipped = assigned.clone();
                    self.expression(right, assigned);
                    assigned.retain(|name| skipped.contains(name));
                } else {
                    self.expression(right, assigned);
                }
            }
            KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => {
                self.expression(condition, assigned);
                let mut true_state = assigned.clone();
                self.expression(when_true, &mut true_state);
                let mut false_state = assigned.clone();
                self.expression(when_false, &mut false_state);
                true_state.retain(|name| false_state.contains(name));
                *assigned = true_state;
            }
            KotlinExpr::Assignment { target, op, value } => {
                self.assignment(target, *op, value, assigned);
            }
        }
    }

    fn assignment(
        &mut self,
        target: &KotlinExpr,
        op: KotlinAssignOp,
        value: &KotlinExpr,
        assigned: &mut BTreeSet<KotlinIdentifier>,
    ) {
        match target {
            KotlinExpr::Name(name) => {
                if op != KotlinAssignOp::Assign {
                    self.read(name, assigned);
                }
            }
            target => self.expression(target, assigned),
        }
        self.expression(value, assigned);
        if let KotlinExpr::Name(name) = target {
            assigned.insert(name.clone());
        }
    }

    fn read(&mut self, name: &KotlinIdentifier, assigned: &BTreeSet<KotlinIdentifier>) {
        if self.declarations.is_candidate(name) && !assigned.contains(name) {
            self.required.insert(name.clone());
        }
    }

    fn initialize(&self, root: &mut KotlinStmt) -> bool {
        let mut changed = false;
        Self::initialize_statement(root, &self.required, &mut changed);
        changed
    }

    fn initialize_statement(
        statement: &mut KotlinStmt,
        required: &BTreeSet<KotlinIdentifier>,
        changed: &mut bool,
    ) {
        match statement {
            KotlinStmt::Variable {
                ty,
                name,
                value: value @ None,
                ..
            } if required.contains(name) => {
                *value = Some(Self::default_value(ty));
                *changed = true;
            }
            KotlinStmt::Block(children) => {
                for child in children {
                    Self::initialize_statement(child, required, changed);
                }
            }
            KotlinStmt::Labeled { body, .. }
            | KotlinStmt::While { body, .. }
            | KotlinStmt::DoWhile { body, .. }
            | KotlinStmt::For { body, .. }
            | KotlinStmt::ForEach { body, .. }
            | KotlinStmt::Synchronized { body, .. } => {
                Self::initialize_statement(body, required, changed);
            }
            KotlinStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                Self::initialize_statement(then_stmt, required, changed);
                if let Some(else_stmt) = else_stmt {
                    Self::initialize_statement(else_stmt, required, changed);
                }
            }
            KotlinStmt::Switch { cases, .. } => {
                for case in cases {
                    for child in &mut case.body {
                        Self::initialize_statement(child, required, changed);
                    }
                }
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                Self::initialize_statement(body, required, changed);
                for catch in catches {
                    Self::initialize_statement(&mut catch.body, required, changed);
                }
                if let Some(finally) = finally {
                    Self::initialize_statement(finally, required, changed);
                }
            }
            KotlinStmt::Empty
            | KotlinStmt::Variable { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::Assign { .. }
            | KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => {}
        }
    }

    fn default_value(ty: &KotlinType) -> KotlinExpr {
        let literal = match ty {
            KotlinType::Primitive(KotlinPrimitiveType::Boolean) => KotlinLiteral::Boolean(false),
            KotlinType::Primitive(KotlinPrimitiveType::Long) => KotlinLiteral::Long(0),
            KotlinType::Primitive(KotlinPrimitiveType::Float) => KotlinLiteral::Float(0.0),
            KotlinType::Primitive(KotlinPrimitiveType::Double) => KotlinLiteral::Double(0.0),
            KotlinType::Primitive(KotlinPrimitiveType::Char) => KotlinLiteral::Character(0),
            KotlinType::Primitive(
                KotlinPrimitiveType::Byte | KotlinPrimitiveType::Short | KotlinPrimitiveType::Int,
            ) => KotlinLiteral::Integer(0),
            KotlinType::Primitive(KotlinPrimitiveType::Void)
            | KotlinType::Class(_)
            | KotlinType::Variable(_)
            | KotlinType::Array(_) => KotlinLiteral::Null,
        };
        KotlinExpr::Literal(literal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(value: &str) -> KotlinIdentifier {
        KotlinIdentifier::from_hint(value)
    }

    fn unknown_boolean(method: &str) -> KotlinExpr {
        KotlinExpr::Call {
            receiver: Some(Box::new(KotlinExpr::This)),
            owner: None,
            type_arguments: Vec::new(),
            method: name(method),
            args: Vec::new().into(),
        }
    }

    #[test]
    fn guarded_boolean_definition_implies_its_guard() {
        let guard = name("guard");
        let gated = name("gated");
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Block(vec![
                KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: KotlinType::Primitive(KotlinPrimitiveType::Boolean),
                    name: guard.clone(),
                    value: Some(unknown_boolean("guardValue")),
                },
                KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: KotlinType::Primitive(KotlinPrimitiveType::Boolean),
                    name: gated.clone(),
                    value: None,
                },
                KotlinStmt::If {
                    condition: KotlinExpr::Name(guard.clone()),
                    then_stmt: Box::new(KotlinStmt::Assign {
                        target: KotlinExpr::Name(gated.clone()),
                        op: KotlinAssignOp::Assign,
                        value: unknown_boolean("gatedValue"),
                    }),
                    else_stmt: None,
                },
                KotlinStmt::Return(Some(KotlinExpr::Binary {
                    left: Box::new(KotlinExpr::Name(guard)),
                    op: KotlinBinaryOp::LogicalAnd,
                    right: Box::new(KotlinExpr::Name(gated.clone())),
                })),
            ]),
        };

        let mut transform = DefiniteAssignment;
        assert!(transform.apply(&mut body).unwrap());
        let KotlinStmt::Block(statements) = body.root else {
            panic!("expected block");
        };
        assert_eq!(
            statements.last(),
            Some(&KotlinStmt::Return(Some(KotlinExpr::Name(gated))))
        );
    }
}
