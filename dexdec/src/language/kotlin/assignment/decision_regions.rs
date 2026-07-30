use std::collections::BTreeSet;

use crate::ir::BoolExpr;
use crate::language::kotlin::{
    KotlinAssignOp, KotlinAstRewriter, KotlinExpr, KotlinIdentifier, KotlinStmt,
};

use super::{BooleanRelations, ExpressionWrites};

pub(super) struct DecisionRegionFormation<'a> {
    booleans: &'a BooleanRelations,
}

impl<'a> DecisionRegionFormation<'a> {
    pub(super) fn new(booleans: &'a BooleanRelations) -> Self {
        Self { booleans }
    }

    pub(super) fn rewrite(&self, statements: &mut Vec<KotlinStmt>) -> bool {
        let mut changed = false;
        let mut start = 0;
        while start < statements.len() {
            let Some(mut condition) = Self::candidate(&statements[start]) else {
                start += 1;
                continue;
            };
            if self.booleans.expression(&condition).is_none() {
                start += 1;
                continue;
            }

            let condition_names = BooleanRelations::names_in(&condition);
            let Some((end, branches)) =
                self.collect_branches(statements, start, &condition, &condition_names)
            else {
                start += 1;
                continue;
            };
            let original_true = Self::assignments(&branches, true);
            let mut when_true = original_true.clone();
            let mut when_false = Self::assignments(&branches, false);
            let inverted = original_true.is_empty();
            if inverted {
                std::mem::swap(&mut when_true, &mut when_false);
                condition = condition.negated();
            }
            if when_true.is_empty() {
                start += 1;
                continue;
            }

            condition = self.booleans.simplify_theoretic(condition);
            let mut replacement_start = start;
            if let Some(predecessor) =
                self.absorb_predecessor(statements, start, &condition, &condition_names)
            {
                predecessor
                    .into_iter()
                    .rev()
                    .for_each(|statement| when_true.insert(0, statement));
                replacement_start -= 1;
            }

            let old_cost = statements[replacement_start..end]
                .iter()
                .map(Self::statement_cost)
                .sum::<usize>();
            let new_cost = 1
                + condition.cost()
                + when_true.iter().map(Self::statement_cost).sum::<usize>()
                + when_false.iter().map(Self::statement_cost).sum::<usize>();
            if new_cost >= old_cost {
                start += 1;
                continue;
            }

            statements.splice(
                replacement_start..end,
                [KotlinStmt::If {
                    condition,
                    then_stmt: Box::new(KotlinStmt::Block(when_true)),
                    else_stmt: (!when_false.is_empty())
                        .then(|| Box::new(KotlinStmt::Block(when_false))),
                }],
            );
            changed = true;
            start = replacement_start + 1;
        }
        changed
    }

    fn collect_branches(
        &self,
        statements: &[KotlinStmt],
        start: usize,
        condition: &KotlinExpr,
        condition_names: &BTreeSet<KotlinIdentifier>,
    ) -> Option<(usize, Vec<(KotlinIdentifier, KotlinExpr, KotlinExpr)>)> {
        let mut targets = BTreeSet::new();
        let mut branches = Vec::new();
        let mut end = start;
        while let Some(KotlinStmt::Assign {
            target: KotlinExpr::Name(target),
            op: KotlinAssignOp::Assign,
            value,
        }) = statements.get(end)
        {
            if !targets.insert(target.clone()) || condition_names.contains(target) {
                break;
            }
            let Some((when_true, when_false)) = self.booleans.split_value(value, condition) else {
                break;
            };
            if Self::expression_writes_any(&when_true, condition_names)
                || Self::expression_writes_any(&when_false, condition_names)
            {
                break;
            }
            branches.push((target.clone(), when_true, when_false));
            end += 1;
        }
        (branches.len() >= 2).then_some((end, branches))
    }

    fn absorb_predecessor(
        &self,
        statements: &[KotlinStmt],
        start: usize,
        condition: &KotlinExpr,
        condition_names: &BTreeSet<KotlinIdentifier>,
    ) -> Option<Vec<KotlinStmt>> {
        let predecessor = start
            .checked_sub(1)
            .and_then(|index| statements.get(index))?;
        if Self::statement_writes_any(predecessor, condition_names) {
            return None;
        }
        let when_false =
            DecisionSpecializer::new(self.booleans, condition, false)?.specialize(predecessor);
        if !Self::is_empty(&when_false) {
            return None;
        }
        let when_true =
            DecisionSpecializer::new(self.booleans, condition, true)?.specialize(predecessor);
        Some(Self::into_statements(when_true))
    }

    fn candidate(statement: &KotlinStmt) -> Option<KotlinExpr> {
        let KotlinStmt::Assign {
            op: KotlinAssignOp::Assign,
            value: KotlinExpr::Conditional { condition, .. },
            ..
        } = statement
        else {
            return None;
        };
        Some(condition.as_ref().clone())
    }

    fn assignments(
        branches: &[(KotlinIdentifier, KotlinExpr, KotlinExpr)],
        when_true: bool,
    ) -> Vec<KotlinStmt> {
        branches
            .iter()
            .filter_map(|(target, true_value, false_value)| {
                let value = if when_true { true_value } else { false_value };
                let target_expression = KotlinExpr::Name(target.clone());
                (value != &target_expression).then(|| KotlinStmt::Assign {
                    target: target_expression,
                    op: KotlinAssignOp::Assign,
                    value: value.clone(),
                })
            })
            .collect()
    }

    fn expression_writes_any(expression: &KotlinExpr, names: &BTreeSet<KotlinIdentifier>) -> bool {
        let mut writes = ExpressionWrites::default();
        writes.rewrite_expression(expression.clone());
        !writes.names.is_disjoint(names)
    }

    fn statement_writes_any(statement: &KotlinStmt, names: &BTreeSet<KotlinIdentifier>) -> bool {
        match statement {
            KotlinStmt::Empty => false,
            KotlinStmt::Block(statements) => statements
                .iter()
                .any(|statement| Self::statement_writes_any(statement, names)),
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                Self::expression_writes_any(condition, names)
                    || Self::statement_writes_any(then_stmt, names)
                    || else_stmt
                        .as_deref()
                        .is_some_and(|statement| Self::statement_writes_any(statement, names))
            }
            KotlinStmt::Assign { target, value, .. } => {
                matches!(target, KotlinExpr::Name(name) if names.contains(name))
                    || Self::expression_writes_any(target, names)
                    || Self::expression_writes_any(value, names)
            }
            KotlinStmt::Variable { name, value, .. } => {
                names.contains(name)
                    || value
                        .as_ref()
                        .is_some_and(|value| Self::expression_writes_any(value, names))
            }
            KotlinStmt::Expression(expression) => Self::expression_writes_any(expression, names),
            _ => true,
        }
    }

    fn is_empty(statement: &KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Empty => true,
            KotlinStmt::Block(statements) => statements.iter().all(Self::is_empty),
            _ => false,
        }
    }

    fn into_statements(statement: KotlinStmt) -> Vec<KotlinStmt> {
        match statement {
            KotlinStmt::Empty => Vec::new(),
            KotlinStmt::Block(statements) => statements,
            statement => vec![statement],
        }
    }

    fn statement_cost(statement: &KotlinStmt) -> usize {
        match statement {
            KotlinStmt::Empty => 0,
            KotlinStmt::Block(statements) => statements.iter().map(Self::statement_cost).sum(),
            KotlinStmt::Assign { target, value, .. } => 1 + target.cost() + value.cost(),
            KotlinStmt::Variable { value, .. } => {
                2 + value.as_ref().map(KotlinExpr::cost).unwrap_or_default()
            }
            KotlinStmt::Expression(expression) => 1 + expression.cost(),
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                1 + condition.cost()
                    + Self::statement_cost(then_stmt)
                    + else_stmt
                        .as_deref()
                        .map(Self::statement_cost)
                        .unwrap_or_default()
            }
            _ => 64,
        }
    }
}

struct DecisionSpecializer<'a> {
    booleans: &'a BooleanRelations,
    assumption: BoolExpr,
}

impl<'a> DecisionSpecializer<'a> {
    fn new(
        booleans: &'a BooleanRelations,
        assumption: &KotlinExpr,
        expected: bool,
    ) -> Option<Self> {
        let assumption = booleans.expression(assumption)?;
        Some(Self {
            booleans,
            assumption: if expected {
                assumption
            } else {
                BoolExpr::not(assumption)
            },
        })
    }

    fn specialize(&self, statement: &KotlinStmt) -> KotlinStmt {
        match statement {
            KotlinStmt::Empty => KotlinStmt::Empty,
            KotlinStmt::Block(statements) => KotlinStmt::Block(
                statements
                    .iter()
                    .map(|statement| self.specialize(statement))
                    .filter(|statement| !DecisionRegionFormation::is_empty(statement))
                    .collect(),
            ),
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => match self.condition_value(condition) {
                Some(true) => self.specialize(then_stmt),
                Some(false) => else_stmt
                    .as_deref()
                    .map(|statement| self.specialize(statement))
                    .unwrap_or(KotlinStmt::Empty),
                None => {
                    let condition = self.simplify_condition(condition.clone());
                    let then_stmt = self
                        .with_condition(&condition, true)
                        .map(|specializer| specializer.specialize(then_stmt))
                        .unwrap_or_else(|| self.specialize(then_stmt));
                    let else_stmt = else_stmt
                        .as_deref()
                        .map(|statement| {
                            self.with_condition(&condition, false)
                                .map(|specializer| specializer.specialize(statement))
                                .unwrap_or_else(|| self.specialize(statement))
                        })
                        .filter(|statement| !DecisionRegionFormation::is_empty(statement));
                    if DecisionRegionFormation::is_empty(&then_stmt) {
                        return else_stmt
                            .map(|statement| KotlinStmt::If {
                                condition: condition.negated(),
                                then_stmt: Box::new(statement),
                                else_stmt: None,
                            })
                            .unwrap_or(KotlinStmt::Empty);
                    }
                    KotlinStmt::If {
                        condition,
                        then_stmt: Box::new(then_stmt),
                        else_stmt: else_stmt.map(Box::new),
                    }
                }
            },
            statement => statement.clone(),
        }
    }

    fn condition_value(&self, expression: &KotlinExpr) -> Option<bool> {
        let condition = self.booleans.expression(expression)?;
        let (bdd, theory) = self.booleans.local_domain([&condition, &self.assumption])?;
        let assumption = bdd.compile(&self.assumption).ok()?;
        let care = bdd.and(theory, assumption).ok()?;
        if care.is_false() {
            return None;
        }
        let condition = bdd.compile(&condition).ok()?;
        if bdd.equivalent_under(care, condition, bdd.truth()).ok()? {
            return Some(true);
        }
        bdd.equivalent_under(care, condition, bdd.falsity())
            .ok()?
            .then_some(false)
    }

    fn simplify_condition(&self, expression: KotlinExpr) -> KotlinExpr {
        let Some(condition) = self.booleans.expression(&expression) else {
            return expression;
        };
        let original_symbols = condition.symbols();
        let Some((bdd, theory)) = self.booleans.local_domain([&condition, &self.assumption]) else {
            return expression;
        };
        let Ok(assumption) = bdd.compile(&self.assumption) else {
            return expression;
        };
        let Ok(care) = bdd.and(theory, assumption) else {
            return expression;
        };
        let Some((reduced, nodes)) = bdd.reduce_under(&condition, care, 128).ok().flatten() else {
            return expression;
        };
        if nodes > expression.cost() || !reduced.symbols().is_subset(&original_symbols) {
            return expression;
        }
        self.booleans
            .lower(reduced)
            .filter(|replacement| replacement != &expression)
            .unwrap_or(expression)
    }

    fn with_condition(&self, condition: &KotlinExpr, expected: bool) -> Option<Self> {
        let condition = self.booleans.expression(condition)?;
        Some(Self {
            booleans: self.booleans,
            assumption: BoolExpr::and(vec![
                self.assumption.clone(),
                if expected {
                    condition
                } else {
                    BoolExpr::not(condition)
                },
            ]),
        })
    }
}
