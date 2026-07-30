use crate::ir::{
    SemanticExpression, SemanticLeaveKind, SemanticLoopKind, SemanticNode, SemanticPredicate,
    SemanticStatement,
};

mod control;
mod protection;

use control::ControlLayout;
use protection::ProtectionLowering;

use super::ast::{
    JavaAssignOp, JavaCatch, JavaExpr, JavaIdentifier, JavaLiteral, JavaMethodBody, JavaStmt,
    JavaSwitchCase, JavaType, JavaUnaryOp,
};

#[derive(Debug, Clone)]
pub enum JavaStructuralError {
    MalformedWorkStack,
    MissingControlScope,
    UnknownControlTarget(crate::ir::RegionId),
    UnboundContinuation {
        scope: crate::ir::RegionId,
        target: crate::ir::BlockId,
    },
    EmptyCatchTypes,
    ChildArity {
        expected: usize,
        actual: usize,
    },
    InvalidForInitializer,
    InvalidForUpdate,
}

impl std::fmt::Display for JavaStructuralError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedWorkStack => formatter.write_str("malformed Java lowering stack"),
            Self::MissingControlScope => {
                formatter.write_str("Java lowering exited a missing control scope")
            }
            Self::UnknownControlTarget(region) => {
                write!(formatter, "leave targets inactive control region {region}")
            }
            Self::UnboundContinuation { scope, target } => {
                write!(
                    formatter,
                    "unbound continuation {scope} -> {target} reached Java lowering"
                )
            }
            Self::EmptyCatchTypes => formatter.write_str("semantic catch has no exception type"),
            Self::ChildArity { expected, actual } => write!(
                formatter,
                "Java lowering frame has {actual} children, expected {expected}"
            ),
            Self::InvalidForInitializer => {
                formatter.write_str("for initializer is not an inline Java statement")
            }
            Self::InvalidForUpdate => formatter.write_str("for update is not a Java expression"),
        }
    }
}

impl std::error::Error for JavaStructuralError {}

pub trait JavaDialect {
    type Error;

    fn condition(&mut self, condition: &SemanticPredicate) -> Result<JavaExpr, Self::Error>;

    fn negated_condition(
        &mut self,
        condition: &SemanticPredicate,
    ) -> Result<JavaExpr, Self::Error> {
        Ok(JavaExpr::Unary {
            op: JavaUnaryOp::LogicalNot,
            operand: Box::new(self.condition(condition)?),
        })
    }

    fn expression(&mut self, value: &SemanticExpression) -> Result<JavaExpr, Self::Error>;

    fn iterable_expression(
        &mut self,
        _element_type: &JavaType,
        value: &SemanticExpression,
    ) -> Result<JavaExpr, Self::Error> {
        self.expression(value)
    }

    fn return_expression(
        &mut self,
        value: &SemanticExpression,
        _condition: Option<&SemanticPredicate>,
    ) -> Result<JavaExpr, Self::Error> {
        self.expression(value)
    }

    fn throw_expression(&mut self, value: &SemanticExpression) -> Result<JavaExpr, Self::Error> {
        self.expression(value)
    }

    fn statement(&mut self, statement: &SemanticStatement) -> Result<JavaStmt, Self::Error>;

    fn catch_binding(
        &mut self,
        register: Option<&crate::ir::RegisterArg>,
    ) -> Result<JavaCatchBinding, Self::Error>;

    fn type_name(&mut self, ty: &crate::ir::ArgType) -> Result<JavaType, Self::Error>;

    fn take_declarations(&mut self) -> Vec<JavaStmt> {
        Vec::new()
    }

    fn prepare(&mut self, _root: &SemanticNode) -> Result<(), Self::Error> {
        Ok(())
    }

    fn loop_variable(
        &mut self,
        register: &crate::ir::RegisterArg,
    ) -> Result<(JavaType, JavaIdentifier), Self::Error>;

    fn synthetic_variable(&mut self, hint: &str) -> JavaIdentifier;
}

pub struct JavaCatchBinding {
    parameter: JavaIdentifier,
    storage: Option<JavaIdentifier>,
}

impl JavaCatchBinding {
    pub fn local(parameter: JavaIdentifier) -> Self {
        Self {
            parameter,
            storage: None,
        }
    }

    pub fn stored(parameter: JavaIdentifier, storage: JavaIdentifier) -> Self {
        Self {
            parameter,
            storage: Some(storage),
        }
    }

    fn lower(self, types: Vec<JavaType>, body: JavaStmt) -> JavaCatch {
        let body = match self.storage {
            Some(storage) => {
                let assignment = JavaStmt::Assign {
                    target: JavaExpr::Name(storage),
                    op: super::ast::JavaAssignOp::Assign,
                    value: JavaExpr::Name(self.parameter.clone()),
                };
                match body {
                    JavaStmt::Block(mut statements) => {
                        statements.insert(0, assignment);
                        JavaStmt::Block(statements)
                    }
                    JavaStmt::Empty => JavaStmt::Block(vec![assignment]),
                    statement => JavaStmt::Block(vec![assignment, statement]),
                }
            }
            None => body,
        };
        JavaCatch {
            types,
            variable: self.parameter,
            body,
        }
    }
}

pub struct JavaLowerer<R> {
    dialect: R,
    controls: ControlLayout,
}

impl<R> JavaLowerer<R>
where
    R: JavaDialect,
    R::Error: From<JavaStructuralError>,
{
    pub fn new(dialect: R) -> Self {
        Self {
            dialect,
            controls: ControlLayout::default(),
        }
    }

    pub fn lower(mut self, root: &SemanticNode) -> Result<JavaMethodBody, R::Error> {
        crate::profile_scope!("java_lower.prepare", self.dialect.prepare(root))?;
        self.controls = crate::profile_scope!("java_lower.controls", ControlLayout::analyze(root))?;
        let body = crate::profile_scope!("java_lower.body", self.node(root))?;
        let mut statements = self.dialect.take_declarations();
        statements.extend(Self::block_statements(body));
        Ok(JavaMethodBody {
            root: JavaStmt::Block(statements),
        })
    }

    fn node(&mut self, root: &SemanticNode) -> Result<JavaStmt, R::Error> {
        let mut pending = vec![LowerTask::Visit(root)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                LowerTask::Visit(node) => self.schedule_node(node, &mut pending, &mut results)?,
                LowerTask::Rebuild(frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(JavaStructuralError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect();
                    results.push(self.rebuild(frame, children)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(JavaStructuralError::MalformedWorkStack.into());
        }
        results
            .pop()
            .ok_or_else(|| JavaStructuralError::MalformedWorkStack.into())
    }

    fn schedule_node<'a>(
        &mut self,
        node: &'a SemanticNode,
        pending: &mut Vec<LowerTask<'a>>,
        results: &mut Vec<JavaStmt>,
    ) -> Result<(), R::Error> {
        match node {
            SemanticNode::Empty => results.push(JavaStmt::Empty),
            SemanticNode::BasicBlock(block) => {
                let statements = block
                    .statements
                    .iter()
                    .map(|statement| self.dialect.statement(statement))
                    .collect::<Result<Vec<_>, _>>()?;
                results.push(JavaStmt::Block(statements));
            }
            SemanticNode::Sequence(children) => {
                pending.push(LowerTask::Rebuild(LowerFrame::Sequence(children.len())));
                pending.extend(children.iter().rev().map(LowerTask::Visit));
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                pending.push(LowerTask::Rebuild(LowerFrame::If {
                    condition,
                    has_else: else_node.is_some(),
                }));
                if let Some(else_node) = else_node {
                    pending.push(LowerTask::Visit(else_node));
                }
                pending.push(LowerTask::Visit(then_node));
            }
            SemanticNode::Loop {
                control,
                kind,
                test,
                body,
                ..
            } => {
                pending.push(LowerTask::Rebuild(LowerFrame::Loop {
                    control: *control,
                    kind: *kind,
                    condition: &test.condition,
                }));
                pending.push(LowerTask::Visit(body));
                pending.push(LowerTask::Visit(&test.setup));
            }
            SemanticNode::For {
                control,
                init,
                condition,
                update,
                body,
            } => {
                pending.push(LowerTask::Rebuild(LowerFrame::For {
                    control: *control,
                    init,
                    condition,
                    update,
                }));
                pending.push(LowerTask::Visit(body));
            }
            SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body,
            } => {
                pending.push(LowerTask::Rebuild(LowerFrame::ForEach {
                    control: *control,
                    variable,
                    iterable,
                }));
                pending.push(LowerTask::Visit(body));
            }
            SemanticNode::Switch {
                region,
                selector,
                cases,
            } => {
                pending.push(LowerTask::Rebuild(LowerFrame::Switch {
                    region: *region,
                    selector,
                    cases,
                }));
                pending.extend(cases.iter().rev().map(|case| LowerTask::Visit(&case.body)));
            }
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                pending.push(LowerTask::Rebuild(LowerFrame::Try {
                    catches,
                    has_finally: finally.is_some(),
                }));
                if let Some(finally) = finally {
                    pending.push(LowerTask::Visit(&finally.body));
                }
                pending.extend(
                    catches
                        .iter()
                        .rev()
                        .map(|catch| LowerTask::Visit(&catch.body)),
                );
                pending.push(LowerTask::Visit(body));
            }
            SemanticNode::Synchronized {
                lock, method, body, ..
            } => {
                pending.push(LowerTask::Rebuild(LowerFrame::Synchronized {
                    lock,
                    method: *method,
                }));
                pending.push(LowerTask::Visit(body));
            }
            SemanticNode::Label { label, body } => {
                pending.push(LowerTask::Rebuild(LowerFrame::Label(*label)));
                pending.push(LowerTask::Visit(body));
            }
            SemanticNode::Leave(leave) => {
                results.push(match &leave.kind {
                    SemanticLeaveKind::FallThrough(target) | SemanticLeaveKind::Jump(target) => {
                        return Err(JavaStructuralError::UnboundContinuation {
                            scope: leave.target,
                            target: *target,
                        }
                        .into());
                    }
                    SemanticLeaveKind::BreakLabel(label) => {
                        JavaStmt::Break(self.controls.label_for(*label))
                    }
                    SemanticLeaveKind::ContinueLabel(label) => {
                        JavaStmt::Continue(self.controls.label_for(*label))
                    }
                    SemanticLeaveKind::Return(value) => JavaStmt::Return(
                        value
                            .as_ref()
                            .map(|value| {
                                self.dialect
                                    .return_expression(value, leave.condition.as_ref())
                            })
                            .transpose()?,
                    ),
                    SemanticLeaveKind::Throw(value) => {
                        JavaStmt::Throw(self.dialect.throw_expression(value)?)
                    }
                    SemanticLeaveKind::Break => JavaStmt::Break(self.leave_label(leave.target)),
                    SemanticLeaveKind::Continue => {
                        JavaStmt::Continue(self.leave_label(leave.target))
                    }
                });
            }
        }
        Ok(())
    }

    fn rebuild(
        &mut self,
        frame: LowerFrame<'_>,
        children: Vec<JavaStmt>,
    ) -> Result<JavaStmt, R::Error> {
        let expected = frame.child_count();
        if children.len() != expected {
            return Err(JavaStructuralError::ChildArity {
                expected,
                actual: children.len(),
            }
            .into());
        }
        let mut children = children.into_iter();
        Ok(match frame {
            LowerFrame::Sequence(_) => {
                JavaStmt::Block(children.flat_map(Self::block_statements).collect())
            }
            LowerFrame::If {
                condition,
                has_else,
            } => {
                let mut then_stmt = Self::child(&mut children)?;
                let mut else_stmt = if has_else {
                    Some(Self::child(&mut children)?)
                } else {
                    None
                };
                let mut expression = self.dialect.condition(condition)?;
                if else_stmt.is_some() {
                    let negated = self.dialect.negated_condition(condition)?;
                    if negated.cost() < expression.cost() {
                        expression = negated;
                        std::mem::swap(&mut then_stmt, else_stmt.as_mut().expect("checked above"));
                    }
                }
                JavaStmt::If {
                    condition: expression,
                    then_stmt: Box::new(then_stmt),
                    else_stmt: else_stmt.map(Box::new),
                }
            }
            LowerFrame::Loop {
                control,
                kind,
                condition,
            } => {
                let setup = Self::child(&mut children)?;
                let body = Self::child(&mut children)?;
                let label = self.loop_control_label(control);
                let setup = Self::block_statements(setup);
                match kind {
                    SemanticLoopKind::PreTested if setup.is_empty() => {
                        let condition = self.dialect.condition(condition)?;
                        JavaStmt::While {
                            label,
                            condition,
                            body: Box::new(body),
                        }
                    }
                    SemanticLoopKind::PreTested => {
                        let lowered_condition = self.dialect.condition(condition)?;
                        match LoopConditionBinding::recover(setup, lowered_condition) {
                            BoundLoopCondition::Expression(condition) => JavaStmt::While {
                                label,
                                condition,
                                body: Box::new(body),
                            },
                            BoundLoopCondition::Separate { mut setup } => {
                                setup.push(JavaStmt::If {
                                    condition: self.dialect.negated_condition(condition)?,
                                    then_stmt: Box::new(JavaStmt::Break(None)),
                                    else_stmt: None,
                                });
                                setup.extend(Self::block_statements(body));
                                JavaStmt::While {
                                    label,
                                    condition: JavaExpr::Literal(JavaLiteral::Boolean(true)),
                                    body: Box::new(JavaStmt::Block(setup)),
                                }
                            }
                        }
                    }
                    SemanticLoopKind::PostTested => {
                        let condition = self.dialect.condition(condition)?;
                        let mut statements = Self::block_statements(body);
                        statements.extend(setup);
                        JavaStmt::DoWhile {
                            label,
                            body: Box::new(JavaStmt::Block(statements)),
                            condition,
                        }
                    }
                    SemanticLoopKind::Endless => JavaStmt::While {
                        label,
                        condition: JavaExpr::Literal(JavaLiteral::Boolean(true)),
                        body: Box::new(JavaStmt::Block(
                            setup
                                .into_iter()
                                .chain(Self::block_statements(body))
                                .collect(),
                        )),
                    },
                }
            }
            LowerFrame::For {
                control,
                init,
                condition,
                update,
            } => JavaStmt::For {
                label: self.loop_control_label(control),
                init: vec![Self::for_initializer(self.dialect.statement(init)?)?],
                condition: Some(self.dialect.condition(condition)?),
                update: vec![Self::update_expression(self.dialect.statement(update)?)?],
                body: Box::new(Self::child(&mut children)?),
            },
            LowerFrame::ForEach {
                control,
                variable,
                iterable,
            } => {
                let (ty, variable) = self.dialect.loop_variable(variable)?;
                let iterable = self.dialect.iterable_expression(&ty, iterable)?;
                JavaStmt::ForEach {
                    label: self.loop_control_label(control),
                    ty,
                    variable,
                    iterable,
                    body: Box::new(Self::child(&mut children)?),
                }
            }
            LowerFrame::Switch {
                region,
                selector,
                cases,
            } => JavaStmt::Switch {
                label: self.controls.label(region),
                selector: self.dialect.expression(selector)?,
                cases: cases
                    .iter()
                    .zip(children)
                    .map(|(case, body)| JavaSwitchCase {
                        labels: case
                            .values
                            .iter()
                            .map(|value| JavaExpr::Literal(JavaLiteral::Integer(*value)))
                            .collect(),
                        body: Self::block_statements(body),
                        is_default: case.is_default,
                    })
                    .collect(),
            },
            LowerFrame::Try {
                catches,
                has_finally,
            } => {
                let body = Self::child(&mut children)?;
                let catch_bodies = (0..catches.len())
                    .map(|_| Self::child(&mut children))
                    .collect::<Result<Vec<_>, _>>()?;
                let finally = has_finally
                    .then(|| Self::child(&mut children))
                    .transpose()?;
                ProtectionLowering::new(&mut self.dialect).lower(
                    body,
                    catches,
                    catch_bodies,
                    finally,
                )?
            }
            LowerFrame::Synchronized { lock, method } => {
                let body = Self::child(&mut children)?;
                if method {
                    body
                } else {
                    JavaStmt::Synchronized {
                        lock: self.dialect.expression(lock)?,
                        body: Box::new(body),
                    }
                }
            }
            LowerFrame::Label(label) => JavaStmt::Labeled {
                label: ControlLayout::label_identifier(label),
                body: Box::new(Self::child(&mut children)?),
            },
        })
    }

    fn loop_control_label(
        &self,
        control: crate::ir::SemanticLoopControl,
    ) -> Option<JavaIdentifier> {
        self.controls.loop_label(control)
    }

    fn leave_label(&self, target: crate::ir::RegionId) -> Option<JavaIdentifier> {
        self.controls.leave_label(target)
    }

    fn for_initializer(statement: JavaStmt) -> Result<JavaStmt, JavaStructuralError> {
        match statement {
            JavaStmt::Variable { .. } | JavaStmt::Expression(_) | JavaStmt::Assign { .. } => {
                Ok(statement)
            }
            _ => Err(JavaStructuralError::InvalidForInitializer),
        }
    }

    fn update_expression(statement: JavaStmt) -> Result<JavaExpr, JavaStructuralError> {
        match statement {
            JavaStmt::Expression(expression) => Ok(expression),
            JavaStmt::Assign { target, op, value } => Ok(JavaExpr::Assignment {
                target: Box::new(target),
                op,
                value: Box::new(value),
            }),
            _ => Err(JavaStructuralError::InvalidForUpdate),
        }
    }

    fn block_statements(stmt: JavaStmt) -> Vec<JavaStmt> {
        match stmt {
            JavaStmt::Block(statements) => statements,
            JavaStmt::Empty => Vec::new(),
            other => vec![other],
        }
    }

    fn child(children: &mut impl Iterator<Item = JavaStmt>) -> Result<JavaStmt, R::Error> {
        children
            .next()
            .ok_or_else(|| JavaStructuralError::MalformedWorkStack.into())
    }
}

enum BoundLoopCondition {
    Expression(JavaExpr),
    Separate { setup: Vec<JavaStmt> },
}

struct LoopConditionBinding;

impl LoopConditionBinding {
    fn recover(setup: Vec<JavaStmt>, condition: JavaExpr) -> BoundLoopCondition {
        let [JavaStmt::Assign {
            target,
            op: JavaAssignOp::Assign,
            value,
        }] = setup.as_slice()
        else {
            return BoundLoopCondition::Separate { setup };
        };
        let JavaExpr::Name(name) = target else {
            return BoundLoopCondition::Separate { setup };
        };
        let assignment = JavaExpr::Assignment {
            target: Box::new(target.clone()),
            op: JavaAssignOp::Assign,
            value: Box::new(value.clone()),
        };
        match Self::bind_first_evaluation(condition, name, assignment) {
            Some(condition) => BoundLoopCondition::Expression(condition),
            None => BoundLoopCondition::Separate { setup },
        }
    }

    /// The setup may move into the condition only at its first mandatory
    /// evaluation point. This preserves Java's left-to-right evaluation,
    /// short-circuit behavior, exceptions, and side effects.
    fn bind_first_evaluation(
        expression: JavaExpr,
        name: &JavaIdentifier,
        assignment: JavaExpr,
    ) -> Option<JavaExpr> {
        Some(match expression {
            JavaExpr::Name(candidate) if &candidate == name => assignment,
            JavaExpr::Unary { op, operand } => JavaExpr::Unary {
                op,
                operand: Box::new(Self::bind_first_evaluation(*operand, name, assignment)?),
            },
            JavaExpr::Binary { left, op, right } => JavaExpr::Binary {
                left: Box::new(Self::bind_first_evaluation(*left, name, assignment)?),
                op,
                right,
            },
            JavaExpr::Cast { ty, value } => JavaExpr::Cast {
                ty,
                value: Box::new(Self::bind_first_evaluation(*value, name, assignment)?),
            },
            JavaExpr::InstanceOf { value, ty } => JavaExpr::InstanceOf {
                value: Box::new(Self::bind_first_evaluation(*value, name, assignment)?),
                ty,
            },
            JavaExpr::Field { owner, name: field } => JavaExpr::Field {
                owner: Box::new(Self::bind_first_evaluation(*owner, name, assignment)?),
                name: field,
            },
            JavaExpr::ArrayAccess { array, index } => JavaExpr::ArrayAccess {
                array: Box::new(Self::bind_first_evaluation(*array, name, assignment)?),
                index,
            },
            JavaExpr::Call {
                receiver: Some(receiver),
                owner,
                type_arguments,
                method,
                args,
            } => JavaExpr::Call {
                receiver: Some(Box::new(Self::bind_first_evaluation(
                    *receiver, name, assignment,
                )?)),
                owner,
                type_arguments,
                method,
                args,
            },
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => JavaExpr::Conditional {
                condition: Box::new(Self::bind_first_evaluation(*condition, name, assignment)?),
                when_true,
                when_false,
            },
            _ => return None,
        })
    }
}

enum LowerTask<'a> {
    Visit(&'a SemanticNode),
    Rebuild(LowerFrame<'a>),
}

#[derive(Debug, Clone)]
enum LowerFrame<'a> {
    Sequence(usize),
    If {
        condition: &'a SemanticPredicate,
        has_else: bool,
    },
    Loop {
        control: crate::ir::SemanticLoopControl,
        kind: SemanticLoopKind,
        condition: &'a SemanticPredicate,
    },
    For {
        control: crate::ir::SemanticLoopControl,
        init: &'a SemanticStatement,
        condition: &'a SemanticPredicate,
        update: &'a SemanticStatement,
    },
    ForEach {
        control: crate::ir::SemanticLoopControl,
        variable: &'a crate::ir::RegisterArg,
        iterable: &'a SemanticExpression,
    },
    Switch {
        region: Option<crate::ir::RegionId>,
        selector: &'a SemanticExpression,
        cases: &'a [crate::ir::SemanticSwitchCase],
    },
    Try {
        catches: &'a [crate::ir::SemanticCatch],
        has_finally: bool,
    },
    Synchronized {
        lock: &'a SemanticExpression,
        method: bool,
    },
    Label(crate::ir::SemanticLabel),
}

impl LowerFrame<'_> {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(count) => *count,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::Loop { .. } => 2,
            Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized { .. }
            | Self::Label(_) => 1,
            Self::Switch { cases, .. } => cases.len(),
            Self::Try {
                catches,
                has_finally,
            } => 1 + catches.len() + usize::from(*has_finally),
        }
    }
}
