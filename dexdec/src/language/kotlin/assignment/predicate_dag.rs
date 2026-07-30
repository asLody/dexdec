use std::collections::BTreeSet;

use crate::language::kotlin::{
    KotlinAstRewriter, KotlinBinaryOp, KotlinExpr, KotlinIdentifier, KotlinPrimitiveType,
    KotlinStmt, KotlinType, KotlinUnaryOp,
};

use super::{ExpressionNames, StatementWrites};

pub(super) struct PredicateDag {
    names: BTreeSet<KotlinIdentifier>,
    next_name: usize,
}

impl PredicateDag {
    pub(super) fn recover(root: &mut KotlinStmt) -> bool {
        let mut identifiers = IdentifierCollector::default();
        identifiers.rewrite_statement(root.clone());
        identifiers.collect_catches(root);
        let mut dag = Self {
            names: identifiers.names,
            next_name: 1,
        };
        dag.statement(root)
    }

    fn statement(&mut self, statement: &mut KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Block(statements) => self.block(statements),
            KotlinStmt::Labeled { body, .. }
            | KotlinStmt::While { body, .. }
            | KotlinStmt::DoWhile { body, .. }
            | KotlinStmt::ForEach { body, .. }
            | KotlinStmt::Synchronized { body, .. } => self.statement(body),
            KotlinStmt::For { init, body, .. } => {
                let mut changed = false;
                for statement in init {
                    changed |= self.statement(statement);
                }
                changed | self.statement(body)
            }
            KotlinStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                let mut changed = self.statement(then_stmt);
                if let Some(else_stmt) = else_stmt {
                    changed |= self.statement(else_stmt);
                }
                changed
            }
            KotlinStmt::Switch { cases, .. } => cases
                .iter_mut()
                .fold(false, |changed, case| changed | self.block(&mut case.body)),
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                let mut changed = self.statement(body);
                for catch in catches {
                    changed |= self.statement(&mut catch.body);
                }
                if let Some(finally) = finally {
                    changed |= self.statement(finally);
                }
                changed
            }
            KotlinStmt::Empty
            | KotlinStmt::Variable { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::Assign { .. }
            | KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => false,
        }
    }

    fn block(&mut self, statements: &mut Vec<KotlinStmt>) -> bool {
        let mut changed = false;
        while let Some(shared) = SharedPredicate::best(statements) {
            let name = self.allocate_name();
            for &index in &shared.statements {
                if let Some(condition) = Self::if_condition_mut(&mut statements[index]) {
                    let mut replacement =
                        PredicateReplacement::new(&shared.expression, name.clone());
                    *condition = replacement.rewrite_expression(condition.clone());
                }
            }
            statements.insert(
                shared.first,
                KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: KotlinType::Primitive(KotlinPrimitiveType::Boolean),
                    name,
                    value: Some(shared.expression),
                },
            );
            changed = true;
        }
        for statement in statements {
            changed |= self.statement(statement);
        }
        changed
    }

    fn allocate_name(&mut self) -> KotlinIdentifier {
        loop {
            let hint = if self.next_name == 1 {
                "proceed".to_owned()
            } else {
                format!("proceed{}", self.next_name)
            };
            self.next_name += 1;
            let name = KotlinIdentifier::from_hint(&hint);
            if self.names.insert(name.clone()) {
                return name;
            }
        }
    }

    fn if_condition_mut(statement: &mut KotlinStmt) -> Option<&mut KotlinExpr> {
        match statement {
            KotlinStmt::If { condition, .. } => Some(condition),
            _ => None,
        }
    }
}

struct SharedPredicate {
    expression: KotlinExpr,
    first: usize,
    statements: Vec<usize>,
    savings: usize,
}

impl SharedPredicate {
    fn best(statements: &[KotlinStmt]) -> Option<Self> {
        let mut best = None::<Self>;
        for first in 0..statements.len() {
            let Some(expression) = Self::if_condition(&statements[first]).cloned() else {
                continue;
            };
            let cost = expression.cost();
            if cost < 6 || !Self::is_stable(&expression) {
                continue;
            }
            let dependencies = Self::dependencies(&expression);
            if dependencies.is_empty() {
                continue;
            }

            let mut occurrences = PredicateOccurrences::count(&expression, &expression);
            let mut matching = vec![first];
            for index in first + 1..statements.len() {
                if Self::writes_any(&statements[index - 1], &dependencies) {
                    break;
                }
                let Some(condition) = Self::if_condition(&statements[index]) else {
                    continue;
                };
                let count = PredicateOccurrences::count(condition, &expression);
                if count == 0 {
                    continue;
                }
                occurrences = occurrences.saturating_add(count);
                matching.push(index);
            }
            if matching.len() < 2 {
                continue;
            }

            let old_cost = occurrences.saturating_mul(cost);
            let new_cost = cost.saturating_add(2).saturating_add(occurrences);
            let Some(savings) = old_cost.checked_sub(new_cost).filter(|saving| *saving > 0) else {
                continue;
            };
            let candidate = Self {
                expression,
                first,
                statements: matching,
                savings,
            };
            let replace = best.as_ref().is_none_or(|current| {
                candidate.first < current.first
                    || candidate.first == current.first
                        && (candidate.savings, candidate.expression.cost())
                            > (current.savings, current.expression.cost())
            });
            if replace {
                best = Some(candidate);
            }
        }
        best
    }

    fn if_condition(statement: &KotlinStmt) -> Option<&KotlinExpr> {
        match statement {
            KotlinStmt::If { condition, .. } => Some(condition),
            _ => None,
        }
    }

    fn is_stable(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::This | KotlinExpr::Name(_) | KotlinExpr::Literal(_) => true,
            KotlinExpr::Unary {
                op: KotlinUnaryOp::LogicalNot,
                operand,
            } => Self::is_stable(operand),
            KotlinExpr::Binary { left, op, right }
                if matches!(
                    op,
                    KotlinBinaryOp::Equal
                        | KotlinBinaryOp::NotEqual
                        | KotlinBinaryOp::ReferentialEqual
                        | KotlinBinaryOp::ReferentialNotEqual
                        | KotlinBinaryOp::Less
                        | KotlinBinaryOp::LessEqual
                        | KotlinBinaryOp::Greater
                        | KotlinBinaryOp::GreaterEqual
                        | KotlinBinaryOp::LogicalAnd
                        | KotlinBinaryOp::LogicalOr
                ) =>
            {
                Self::is_stable(left) && Self::is_stable(right)
            }
            KotlinExpr::SmartCast(value)
            | KotlinExpr::NonNullAssertion(value)
            | KotlinExpr::Cast { value, .. }
            | KotlinExpr::InstanceOf { value, .. } => Self::is_stable(value),
            KotlinExpr::JvmIntrinsic { .. } => false,
            KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::ClassLiteral(_)
            | KotlinExpr::ObjectReference(_)
            | KotlinExpr::Field { .. }
            | KotlinExpr::StaticField { .. }
            | KotlinExpr::ArrayAccess { .. }
            | KotlinExpr::Call { .. }
            | KotlinExpr::MethodReference { .. }
            | KotlinExpr::Lambda { .. }
            | KotlinExpr::BlockLambda { .. }
            | KotlinExpr::New { .. }
            | KotlinExpr::NewArray { .. }
            | KotlinExpr::Unary { .. }
            | KotlinExpr::Update { .. }
            | KotlinExpr::Binary { .. }
            | KotlinExpr::Conditional { .. }
            | KotlinExpr::Assignment { .. } => false,
        }
    }

    fn dependencies(expression: &KotlinExpr) -> BTreeSet<KotlinIdentifier> {
        let mut names = ExpressionNames::default();
        names.rewrite_expression(expression.clone());
        names.names
    }

    fn writes_any(statement: &KotlinStmt, dependencies: &BTreeSet<KotlinIdentifier>) -> bool {
        let mut writes = StatementWrites::default();
        writes.collect(statement);
        !writes.names.is_disjoint(dependencies)
    }
}

struct PredicateOccurrences<'a> {
    target: &'a KotlinExpr,
    count: usize,
}

impl PredicateOccurrences<'_> {
    fn count(expression: &KotlinExpr, target: &KotlinExpr) -> usize {
        let mut counter = PredicateOccurrences { target, count: 0 };
        counter.rewrite_expression(expression.clone());
        counter.count
    }
}

impl KotlinAstRewriter for PredicateOccurrences<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if &expression == self.target {
            self.count += 1;
        }
        expression
    }
}

struct PredicateReplacement<'a> {
    target: &'a KotlinExpr,
    name: KotlinIdentifier,
}

impl<'a> PredicateReplacement<'a> {
    fn new(target: &'a KotlinExpr, name: KotlinIdentifier) -> Self {
        Self { target, name }
    }
}

impl KotlinAstRewriter for PredicateReplacement<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if &expression == self.target {
            KotlinExpr::Name(self.name.clone())
        } else {
            expression
        }
    }
}

#[derive(Default)]
struct IdentifierCollector {
    names: BTreeSet<KotlinIdentifier>,
}

impl IdentifierCollector {
    fn collect_catches(&mut self, root: &KotlinStmt) {
        let mut pending = vec![root];
        while let Some(statement) = pending.pop() {
            match statement {
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
                    for catch in catches {
                        self.names.insert(catch.variable.clone());
                        pending.push(&catch.body);
                    }
                    pending.extend(finally.as_deref());
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
    }
}

impl KotlinAstRewriter for IdentifierCollector {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Name(name) = &expression {
            self.names.insert(name.clone());
        }
        expression
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match &statement {
            KotlinStmt::Variable { name, .. } => {
                self.names.insert(name.clone());
            }
            KotlinStmt::ForEach {
                variable, label, ..
            } => {
                self.names.insert(variable.clone());
                if let Some(label) = label {
                    self.names.insert(label.clone());
                }
            }
            KotlinStmt::Labeled { label, .. } => {
                self.names.insert(label.clone());
            }
            KotlinStmt::While {
                label: Some(label), ..
            }
            | KotlinStmt::DoWhile {
                label: Some(label), ..
            }
            | KotlinStmt::For {
                label: Some(label), ..
            }
            | KotlinStmt::Switch {
                label: Some(label), ..
            } => {
                self.names.insert(label.clone());
            }
            _ => {}
        }
        statement
    }
}
