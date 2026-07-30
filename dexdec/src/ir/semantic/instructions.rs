//! Expression transformation across Semantic IR.

use crate::ir::{RegisterArg, SemanticFoldError, SemanticFolder};

use super::{
    SemanticExpression, SemanticNode, SemanticOperation, SemanticPredicate, SemanticStatement,
    SemanticStatementKind,
};

/// Typed callbacks for bottom-up Semantic IR expression transformations.
pub trait SemanticExpressionTransform {
    fn transform_register(&mut self, register: RegisterArg) -> SemanticExpression {
        SemanticExpression::Register(register)
    }

    fn transform_operation(&mut self, operation: SemanticOperation) -> SemanticExpression {
        SemanticExpression::Operation(Box::new(operation))
    }

    fn transform_select(
        &mut self,
        condition: SemanticPredicate,
        when_true: SemanticExpression,
        when_false: SemanticExpression,
    ) -> SemanticExpression {
        SemanticExpression::select(condition, when_true, when_false)
    }

    fn transform_result(&mut self, result: RegisterArg) -> RegisterArg {
        result
    }

    fn transform_binding(&mut self, binding: RegisterArg) -> RegisterArg {
        self.transform_result(binding)
    }
}

pub struct SemanticInstructions;

impl SemanticInstructions {
    pub fn transform<T>(root: &mut SemanticNode, transform: &mut T) -> Result<(), SemanticFoldError>
    where
        T: SemanticExpressionTransform + ?Sized,
    {
        let body = std::mem::replace(root, SemanticNode::Empty);
        let mut folder = ExpressionFolder { transform };
        *root = folder.fold_node(body)?;
        Ok(())
    }

    pub fn transform_node<T>(
        node: &mut SemanticNode,
        transform: &mut T,
    ) -> Result<(), SemanticFoldError>
    where
        T: SemanticExpressionTransform + ?Sized,
    {
        match node {
            SemanticNode::BasicBlock(block) => {
                for statement in &mut block.statements {
                    Self::transform_statement(statement, transform)?;
                }
            }
            SemanticNode::If { condition, .. } => {
                Self::transform_predicate(condition, transform)?;
            }
            SemanticNode::Loop { test, .. } => {
                Self::transform_predicate(&mut test.condition, transform)?;
            }
            SemanticNode::For {
                init,
                condition,
                update,
                ..
            } => {
                Self::transform_statement(init, transform)?;
                Self::transform_predicate(condition, transform)?;
                Self::transform_statement(update, transform)?;
            }
            SemanticNode::ForEach {
                variable, iterable, ..
            } => {
                Self::transform_register_binding(variable, transform)?;
                Self::transform_expression(iterable, transform)?;
            }
            SemanticNode::Switch { selector, .. }
            | SemanticNode::Synchronized { lock: selector, .. } => {
                Self::transform_expression(selector, transform)?;
            }
            SemanticNode::Try { catches, .. } => {
                for catch in catches {
                    if let Some(value) = &mut catch.exception_value {
                        Self::transform_register_binding(value, transform)?;
                    }
                }
            }
            SemanticNode::Leave(leave) => {
                if let Some(condition) = &mut leave.condition {
                    Self::transform_predicate(condition, transform)?;
                }
                if let Some(value) = leave.value_mut() {
                    Self::transform_expression(value, transform)?;
                }
            }
            SemanticNode::Empty | SemanticNode::Sequence(_) | SemanticNode::Label { .. } => {}
        }
        Ok(())
    }

    pub fn transform_statement<T>(
        statement: &mut SemanticStatement,
        transform: &mut T,
    ) -> Result<(), SemanticFoldError>
    where
        T: SemanticExpressionTransform + ?Sized,
    {
        match &mut statement.kind {
            SemanticStatementKind::Instruction(operation) => {
                let expression = Self::transform_owned_expression(
                    SemanticExpression::Operation(Box::new(operation.clone())),
                    transform,
                )?;
                let SemanticExpression::Operation(transformed) = expression else {
                    return Err(SemanticFoldError::NonOperationStatement);
                };
                *operation = *transformed;
            }
            SemanticStatementKind::Definition { result, value, .. } => {
                *result = transform.transform_result(result.clone());
                Self::transform_expression(value, transform)?;
            }
        }
        Ok(())
    }

    pub fn transform_expression<T>(
        expression: &mut SemanticExpression,
        transform: &mut T,
    ) -> Result<(), SemanticFoldError>
    where
        T: SemanticExpressionTransform + ?Sized,
    {
        let root = std::mem::replace(
            expression,
            SemanticExpression::Literal(crate::ir::LiteralArg::int(0)),
        );
        *expression = Self::transform_owned_expression(root, transform)?;
        Ok(())
    }

    fn transform_owned_expression<T>(
        root: SemanticExpression,
        transform: &mut T,
    ) -> Result<SemanticExpression, SemanticFoldError>
    where
        T: SemanticExpressionTransform + ?Sized,
    {
        let mut pending = vec![ExpressionTask::Visit(root)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpressionTask::Visit(SemanticExpression::Register(register)) => {
                    results.push(transform.transform_register(register));
                }
                ExpressionTask::Visit(SemanticExpression::Literal(literal)) => {
                    results.push(SemanticExpression::Literal(literal));
                }
                ExpressionTask::Visit(SemanticExpression::Operation(operation)) => {
                    let (instruction, operands, compound_target) = operation.into_parts();
                    pending.push(ExpressionTask::Operation {
                        instruction,
                        operand_count: operands.len(),
                        has_compound_target: compound_target.is_some(),
                    });
                    pending.extend(
                        operands
                            .into_iter()
                            .chain(compound_target)
                            .rev()
                            .map(ExpressionTask::Visit),
                    );
                }
                ExpressionTask::Visit(SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                }) => {
                    pending.push(ExpressionTask::Select(condition));
                    pending.push(ExpressionTask::Visit(*when_false));
                    pending.push(ExpressionTask::Visit(*when_true));
                }
                ExpressionTask::Operation {
                    mut instruction,
                    operand_count,
                    has_compound_target,
                } => {
                    let count = operand_count + usize::from(has_compound_target);
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let (operands, compound_target) = {
                        let mut children = results.drain(start..);
                        let operands = children.by_ref().take(operand_count).collect();
                        let compound_target =
                            has_compound_target.then(|| children.next()).flatten();
                        (operands, compound_target)
                    };
                    if has_compound_target && compound_target.is_none() {
                        return Err(SemanticFoldError::MalformedWorkStack);
                    }
                    instruction.result = instruction
                        .result
                        .map(|result| transform.transform_result(result));
                    results.push(transform.transform_operation(SemanticOperation::from_parts(
                        instruction,
                        operands,
                        compound_target,
                    )));
                }
                ExpressionTask::Select(mut condition) => {
                    let when_false = results.pop().ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let when_true = results.pop().ok_or(SemanticFoldError::MalformedWorkStack)?;
                    Self::transform_predicate(&mut condition, transform)?;
                    results.push(transform.transform_select(condition, when_true, when_false));
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        results.pop().ok_or(SemanticFoldError::MalformedWorkStack)
    }

    pub fn transform_predicate<T>(
        predicate: &mut SemanticPredicate,
        transform: &mut T,
    ) -> Result<(), SemanticFoldError>
    where
        T: SemanticExpressionTransform + ?Sized,
    {
        let root = std::mem::replace(predicate, SemanticPredicate::True);
        let mut pending = vec![PredicateTask::Visit(root)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                PredicateTask::Visit(SemanticPredicate::Test(operation)) => {
                    let expression = Self::transform_owned_expression(
                        SemanticExpression::Operation(Box::new(operation)),
                        transform,
                    )?;
                    let SemanticExpression::Operation(operation) = expression else {
                        return Err(SemanticFoldError::NonOperationPredicate);
                    };
                    results.push(SemanticPredicate::Test(*operation));
                }
                PredicateTask::Visit(SemanticPredicate::Not(inner)) => {
                    pending.push(PredicateTask::Not);
                    pending.push(PredicateTask::Visit(*inner));
                }
                PredicateTask::Visit(SemanticPredicate::And(terms)) => {
                    pending.push(PredicateTask::Junction {
                        count: terms.len(),
                        conjunction: true,
                    });
                    pending.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                }
                PredicateTask::Visit(SemanticPredicate::Or(terms)) => {
                    pending.push(PredicateTask::Junction {
                        count: terms.len(),
                        conjunction: false,
                    });
                    pending.extend(terms.into_iter().rev().map(PredicateTask::Visit));
                }
                PredicateTask::Visit(leaf) => results.push(leaf),
                PredicateTask::Not => {
                    let inner = results.pop().ok_or(SemanticFoldError::MalformedWorkStack)?;
                    results.push(SemanticPredicate::Not(Box::new(inner)));
                }
                PredicateTask::Junction { count, conjunction } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(SemanticFoldError::MalformedWorkStack)?;
                    let terms = results.drain(start..).collect();
                    results.push(if conjunction {
                        SemanticPredicate::And(terms)
                    } else {
                        SemanticPredicate::Or(terms)
                    });
                }
            }
        }
        if results.len() != 1 {
            return Err(SemanticFoldError::MalformedWorkStack);
        }
        *predicate = results.pop().ok_or(SemanticFoldError::MalformedWorkStack)?;
        Ok(())
    }

    fn transform_register_binding<T>(
        register: &mut RegisterArg,
        transform: &mut T,
    ) -> Result<(), SemanticFoldError>
    where
        T: SemanticExpressionTransform + ?Sized,
    {
        *register = transform.transform_binding(register.clone());
        Ok(())
    }
}

struct ExpressionFolder<'a, T: ?Sized> {
    transform: &'a mut T,
}

impl<T> SemanticFolder for ExpressionFolder<'_, T>
where
    T: SemanticExpressionTransform + ?Sized,
{
    type Error = SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        SemanticInstructions::transform_node(&mut node, self.transform)?;
        Ok(node)
    }
}

enum ExpressionTask {
    Visit(SemanticExpression),
    Operation {
        instruction: crate::ir::InsnNode,
        operand_count: usize,
        has_compound_target: bool,
    },
    Select(SemanticPredicate),
}

enum PredicateTask {
    Visit(SemanticPredicate),
    Not,
    Junction { count: usize, conjunction: bool },
}
