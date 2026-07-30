use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    analysis::SsaVar,
    bdd::{Bdd, BddContext, BddError},
    semantic::SemanticCompletion,
    BoolExpr, BoolVariable, InstructionId, SemanticFoldError, SemanticNode, SemanticOperand,
    SemanticOperation, SemanticPredicate,
};

pub(super) struct GuardDistribution;

impl GuardDistribution {
    const MAX_COPIES: usize = 8;
    const MAX_TAIL_STATEMENTS: usize = 4;

    pub(super) fn apply(
        prefix: SemanticNode,
        guard: &SemanticOperand<SemanticPredicate>,
        tail: &SemanticNode,
    ) -> Result<(SemanticNode, bool), SemanticFoldError> {
        let guard_cost = Self::predicate_cost(guard);
        if matches!(prefix, SemanticNode::Empty)
            || !super::PredicateRegionFormation::predicate_is_pure(guard)
            || Self::linear_tail_size(tail).is_none()
            || guard_cost < 3
        {
            return Ok((prefix, false));
        }

        let original = prefix;
        let domain = PredicateDomain::collect(&original, guard)?;
        let guard_domain = match domain.compile(guard) {
            Ok(domain) => domain,
            Err(error) if error.is_resource_limit() => return Ok((original, false)),
            Err(error) => return Err(error.into()),
        };
        let injected = match PathInjector::new(&domain, guard_domain, tail).inject(original.clone())
        {
            Ok(injected) => injected,
            Err(error) if error.is_resource_limit() => return Ok((original, false)),
            Err(error) => return Err(error.into()),
        };
        if !(1..=Self::MAX_COPIES).contains(&injected.copies) {
            return Ok((original, false));
        }
        let covered = match domain.bdd.equivalent(injected.covered, guard_domain) {
            Ok(covered) => covered,
            Err(error) if error.is_resource_limit() => return Ok((original, false)),
            Err(error) => return Err(error.into()),
        };
        if !covered {
            return Ok((original, false));
        }

        let old_cost = Self::node_cost(&original)
            .saturating_add(guard_cost)
            .saturating_add(Self::node_cost(tail))
            .saturating_add(1);
        let new_cost = Self::node_cost(&injected.node);
        if new_cost >= old_cost {
            return Ok((original, false));
        }
        Ok((injected.node, true))
    }

    fn linear_tail_size(node: &SemanticNode) -> Option<usize> {
        let mut statements = 0usize;
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Empty => {}
                SemanticNode::BasicBlock(block) => {
                    statements = statements.saturating_add(block.statements.len());
                    if statements > Self::MAX_TAIL_STATEMENTS {
                        return None;
                    }
                }
                SemanticNode::Sequence(children) => pending.extend(children),
                _ => return None,
            }
        }
        Some(statements)
    }

    fn predicate_cost(predicate: &SemanticPredicate) -> usize {
        predicate
            .domain()
            .map(|value| value.node_count())
            .unwrap_or(usize::MAX / 4)
    }

    fn node_cost(node: &SemanticNode) -> usize {
        let mut cost = 0usize;
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            cost = cost.saturating_add(1);
            match node {
                SemanticNode::Empty | SemanticNode::Leave(_) => {}
                SemanticNode::BasicBlock(block) => {
                    cost = cost.saturating_add(block.statements.len().saturating_mul(2));
                }
                SemanticNode::Sequence(children) => pending.extend(children),
                SemanticNode::If {
                    condition,
                    then_node,
                    else_node,
                } => {
                    cost = cost.saturating_add(Self::predicate_cost(condition));
                    pending.push(then_node);
                    pending.extend(else_node.as_deref());
                }
                _ => cost = cost.saturating_add(32),
            }
        }
        cost
    }
}

struct PredicateDomain {
    bdd: BddContext,
    symbols: BTreeMap<InstructionId, BoolVariable>,
}

impl PredicateDomain {
    fn collect(root: &SemanticNode, guard: &SemanticPredicate) -> Result<Self, SemanticFoldError> {
        let mut atoms = Vec::<SemanticOperation>::new();
        let mut symbols = BTreeMap::new();
        Self::collect_predicate(guard, &mut atoms, &mut symbols)?;
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Sequence(children) => pending.extend(children),
                SemanticNode::If {
                    condition,
                    then_node,
                    else_node,
                } => {
                    Self::collect_predicate(condition, &mut atoms, &mut symbols)?;
                    pending.push(then_node);
                    pending.extend(else_node.as_deref());
                }
                _ => {}
            }
        }
        let bdd = BddContext::new(&symbols.values().cloned().collect::<BTreeSet<_>>());
        Ok(Self { bdd, symbols })
    }

    fn collect_predicate(
        predicate: &SemanticPredicate,
        atoms: &mut Vec<SemanticOperation>,
        symbols: &mut BTreeMap<InstructionId, BoolVariable>,
    ) -> Result<(), SemanticFoldError> {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                SemanticPredicate::Test(instruction) => {
                    let index = atoms
                        .iter()
                        .position(|atom| Self::same_operation(atom, instruction))
                        .unwrap_or_else(|| {
                            atoms.push(instruction.clone());
                            atoms.len() - 1
                        });
                    let index =
                        u32::try_from(index).map_err(|_| SemanticFoldError::MalformedWorkStack)?;
                    symbols.insert(instruction.id, BoolVariable::Atom(index));
                }
                SemanticPredicate::Not(inner) => pending.push(inner),
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    pending.extend(terms);
                }
                SemanticPredicate::True | SemanticPredicate::False => {}
            }
        }
        Ok(())
    }

    fn same_operation(left: &SemanticOperation, right: &SemanticOperation) -> bool {
        if left.id == right.id {
            return true;
        }
        if !left.operation_equivalent(right)
            || left.operands().len() != right.operands().len()
            || left.compound_target().is_some() != right.compound_target().is_some()
        {
            return false;
        }
        let mut pending = left
            .operands()
            .iter()
            .zip(right.operands())
            .collect::<Vec<_>>();
        if let (Some(left), Some(right)) = (left.compound_target(), right.compound_target()) {
            pending.push((left, right));
        }
        while let Some((left, right)) = pending.pop() {
            match (left, right) {
                (
                    crate::ir::SemanticExpression::Register(left),
                    crate::ir::SemanticExpression::Register(right),
                ) => {
                    let same = match (SsaVar::from_reg(left), SsaVar::from_reg(right)) {
                        (Some(left), Some(right)) => left == right,
                        (None, None) => {
                            left.reg_num == right.reg_num && left.code_var == right.code_var
                        }
                        _ => false,
                    };
                    if !same {
                        return false;
                    }
                }
                (
                    crate::ir::SemanticExpression::Literal(left),
                    crate::ir::SemanticExpression::Literal(right),
                ) if left == right => {}
                (
                    crate::ir::SemanticExpression::Operation(left),
                    crate::ir::SemanticExpression::Operation(right),
                ) => {
                    if !left.operation_equivalent(right)
                        || left.operands().len() != right.operands().len()
                    {
                        return false;
                    }
                    pending.extend(left.operands().iter().zip(right.operands()));
                }
                _ => return false,
            }
        }
        true
    }

    fn compile(&self, predicate: &SemanticPredicate) -> Result<Bdd, BddError> {
        let expression = self
            .expression(
                predicate
                    .domain()
                    .map_err(|_| BddError::MalformedEvaluation)?,
            )
            .ok_or(BddError::MalformedEvaluation)?;
        self.bdd.compile(&expression)
    }

    fn expression(&self, expression: BoolExpr) -> Option<BoolExpr> {
        let mut pending = vec![ExpressionTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpressionTask::Visit(expression) => match expression {
                    BoolExpr::Symbol(BoolVariable::Instruction(instruction)) => {
                        results.push(BoolExpr::Symbol(self.symbols.get(&instruction)?.clone()));
                    }
                    BoolExpr::Not(inner) => {
                        pending.push(ExpressionTask::Not);
                        pending.push(ExpressionTask::Visit(*inner));
                    }
                    BoolExpr::And(terms) => {
                        pending.push(ExpressionTask::Junction {
                            count: terms.len(),
                            conjunction: true,
                        });
                        pending.extend(terms.into_iter().rev().map(ExpressionTask::Visit));
                    }
                    BoolExpr::Or(terms) => {
                        pending.push(ExpressionTask::Junction {
                            count: terms.len(),
                            conjunction: false,
                        });
                        pending.extend(terms.into_iter().rev().map(ExpressionTask::Visit));
                    }
                    expression => results.push(expression),
                },
                ExpressionTask::Not => {
                    let inner = results.pop()?;
                    results.push(BoolExpr::not(inner));
                }
                ExpressionTask::Junction { count, conjunction } => {
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
}

enum ExpressionTask {
    Visit(BoolExpr),
    Not,
    Junction { count: usize, conjunction: bool },
}

struct PathInjector<'a> {
    domain: &'a PredicateDomain,
    guard: Bdd,
    tail: &'a SemanticNode,
}

impl<'a> PathInjector<'a> {
    fn new(domain: &'a PredicateDomain, guard: Bdd, tail: &'a SemanticNode) -> Self {
        Self {
            domain,
            guard,
            tail,
        }
    }

    fn inject(&self, root: SemanticNode) -> Result<Injection, BddError> {
        let mut tasks = vec![InjectionTask::Visit {
            node: root,
            path: self.domain.bdd.truth(),
        }];
        let mut results = Vec::<InjectionResult>::new();
        while let Some(task) = tasks.pop() {
            match task {
                InjectionTask::Visit { node, path } => match node {
                    SemanticNode::Sequence(mut children) if !children.is_empty() => {
                        let last = children.pop().ok_or(BddError::MalformedEvaluation)?;
                        tasks.push(InjectionTask::Sequence(children));
                        tasks.push(InjectionTask::Visit { node: last, path });
                    }
                    SemanticNode::If {
                        condition,
                        then_node,
                        else_node,
                    } => {
                        let condition_domain = self.domain.compile(&condition)?;
                        let true_path = self.domain.bdd.and(path, condition_domain)?;
                        let false_path = self
                            .domain
                            .bdd
                            .and(path, self.domain.bdd.not(condition_domain)?)?;
                        tasks.push(InjectionTask::If {
                            condition: condition.into_inner(),
                        });
                        tasks.push(InjectionTask::Visit {
                            node: else_node.map(|node| *node).unwrap_or(SemanticNode::Empty),
                            path: false_path,
                        });
                        tasks.push(InjectionTask::Visit {
                            node: *then_node,
                            path: true_path,
                        });
                    }
                    node => {
                        let inject = SemanticCompletion::analyze(&node).can_complete_normally()
                            && self.domain.bdd.implies_bdd(path, self.guard)?;
                        results.push(InjectionResult {
                            node: if inject {
                                SemanticNode::sequence([node, self.tail.clone()])
                            } else {
                                node
                            },
                            covered: if inject {
                                path
                            } else {
                                self.domain.bdd.falsity()
                            },
                            copies: usize::from(inject),
                        });
                    }
                },
                InjectionTask::Sequence(prefix) => {
                    let result = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    results.push(InjectionResult {
                        node: SemanticNode::sequence(
                            prefix.into_iter().chain(std::iter::once(result.node)),
                        ),
                        ..result
                    });
                }
                InjectionTask::If { condition } => {
                    let when_false = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let when_true = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    results.push(InjectionResult {
                        node: SemanticNode::branch(
                            condition,
                            when_true.node,
                            (!matches!(&when_false.node, SemanticNode::Empty))
                                .then_some(when_false.node),
                        ),
                        covered: self.domain.bdd.or(when_true.covered, when_false.covered)?,
                        copies: when_true.copies.saturating_add(when_false.copies),
                    });
                }
            }
        }
        let result = results.pop().ok_or(BddError::MalformedEvaluation)?;
        if !results.is_empty() {
            return Err(BddError::MalformedEvaluation);
        }
        Ok(Injection {
            node: result.node,
            covered: result.covered,
            copies: result.copies,
        })
    }
}

struct Injection {
    node: SemanticNode,
    covered: Bdd,
    copies: usize,
}

struct InjectionResult {
    node: SemanticNode,
    covered: Bdd,
    copies: usize,
}

enum InjectionTask {
    Visit { node: SemanticNode, path: Bdd },
    Sequence(Vec<SemanticNode>),
    If { condition: SemanticPredicate },
}
