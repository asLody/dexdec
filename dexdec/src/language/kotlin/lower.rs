use crate::ir::{
    SemanticExpression, SemanticLeaveKind, SemanticLoopKind, SemanticNode, SemanticPredicate,
    SemanticStatement,
};

mod control;
mod protection;

use control::ControlLayout;
use protection::ProtectionLowering;

use super::ast::{
    KotlinAssignOp, KotlinCatch, KotlinExpr, KotlinIdentifier, KotlinLiteral, KotlinMethodBody,
    KotlinStmt, KotlinSwitchCase, KotlinType, KotlinUnaryOp,
};

#[derive(Debug, Clone)]
pub enum KotlinStructuralError {
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

impl std::fmt::Display for KotlinStructuralError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedWorkStack => formatter.write_str("malformed Kotlin lowering stack"),
            Self::MissingControlScope => {
                formatter.write_str("Kotlin lowering exited a missing control scope")
            }
            Self::UnknownControlTarget(region) => {
                write!(formatter, "leave targets inactive control region {region}")
            }
            Self::UnboundContinuation { scope, target } => {
                write!(
                    formatter,
                    "unbound continuation {scope} -> {target} reached Kotlin lowering"
                )
            }
            Self::EmptyCatchTypes => formatter.write_str("semantic catch has no exception type"),
            Self::ChildArity { expected, actual } => write!(
                formatter,
                "Kotlin lowering frame has {actual} children, expected {expected}"
            ),
            Self::InvalidForInitializer => {
                formatter.write_str("for initializer is not an inline Kotlin statement")
            }
            Self::InvalidForUpdate => formatter.write_str("for update is not a Kotlin expression"),
        }
    }
}

impl std::error::Error for KotlinStructuralError {}

pub trait KotlinDialect {
    type Error;

    fn condition(&mut self, condition: &SemanticPredicate) -> Result<KotlinExpr, Self::Error>;

    fn negated_condition(
        &mut self,
        condition: &SemanticPredicate,
    ) -> Result<KotlinExpr, Self::Error> {
        Ok(KotlinExpr::Unary {
            op: KotlinUnaryOp::LogicalNot,
            operand: Box::new(self.condition(condition)?),
        })
    }

    fn expression(&mut self, value: &SemanticExpression) -> Result<KotlinExpr, Self::Error>;

    fn iterable_expression(
        &mut self,
        _element_type: &KotlinType,
        value: &SemanticExpression,
    ) -> Result<KotlinExpr, Self::Error> {
        self.expression(value)
    }

    fn return_expression(
        &mut self,
        value: &SemanticExpression,
        _condition: Option<&SemanticPredicate>,
    ) -> Result<KotlinExpr, Self::Error> {
        self.expression(value)
    }

    fn throw_expression(&mut self, value: &SemanticExpression) -> Result<KotlinExpr, Self::Error> {
        self.expression(value)
    }

    fn statement(&mut self, statement: &SemanticStatement) -> Result<KotlinStmt, Self::Error>;

    fn catch_binding(
        &mut self,
        register: Option<&crate::ir::RegisterArg>,
    ) -> Result<KotlinCatchBinding, Self::Error>;

    fn type_name(&mut self, ty: &crate::ir::ArgType) -> Result<KotlinType, Self::Error>;

    fn take_declarations(&mut self) -> Vec<KotlinStmt> {
        Vec::new()
    }

    fn prepare(&mut self, _root: &SemanticNode) -> Result<(), Self::Error> {
        Ok(())
    }

    fn loop_variable(
        &mut self,
        register: &crate::ir::RegisterArg,
    ) -> Result<(KotlinType, KotlinIdentifier), Self::Error>;

    fn synthetic_variable(&mut self, hint: &str) -> KotlinIdentifier;
}

pub struct KotlinCatchBinding {
    parameter: KotlinIdentifier,
    storage: Option<KotlinIdentifier>,
}

impl KotlinCatchBinding {
    pub fn local(parameter: KotlinIdentifier) -> Self {
        Self {
            parameter,
            storage: None,
        }
    }

    pub fn stored(parameter: KotlinIdentifier, storage: KotlinIdentifier) -> Self {
        Self {
            parameter,
            storage: Some(storage),
        }
    }

    fn lower(self, types: Vec<KotlinType>, body: KotlinStmt) -> KotlinCatch {
        let body = match self.storage {
            Some(storage) => {
                let assignment = KotlinStmt::Assign {
                    target: KotlinExpr::Name(storage),
                    op: super::ast::KotlinAssignOp::Assign,
                    value: KotlinExpr::Name(self.parameter.clone()),
                };
                match body {
                    KotlinStmt::Block(mut statements) => {
                        statements.insert(0, assignment);
                        KotlinStmt::Block(statements)
                    }
                    KotlinStmt::Empty => KotlinStmt::Block(vec![assignment]),
                    statement => KotlinStmt::Block(vec![assignment, statement]),
                }
            }
            None => body,
        };
        KotlinCatch {
            types,
            variable: self.parameter,
            body,
        }
    }
}

pub struct KotlinLowerer<R> {
    dialect: R,
    controls: ControlLayout,
}

impl<R> KotlinLowerer<R>
where
    R: KotlinDialect,
    R::Error: From<KotlinStructuralError>,
{
    pub fn new(dialect: R) -> Self {
        Self {
            dialect,
            controls: ControlLayout::default(),
        }
    }

    pub fn lower(mut self, root: &SemanticNode) -> Result<KotlinMethodBody, R::Error> {
        crate::profile_scope!("kotlin_lower.prepare", self.dialect.prepare(root))?;
        self.controls =
            crate::profile_scope!("kotlin_lower.controls", ControlLayout::analyze(root))?;
        let body = crate::profile_scope!("kotlin_lower.body", self.node(root))?;
        let mut statements = self.dialect.take_declarations();
        statements.extend(Self::block_statements(body));
        Ok(KotlinMethodBody {
            root: KotlinStmt::Block(statements),
        })
    }

    fn node(&mut self, root: &SemanticNode) -> Result<KotlinStmt, R::Error> {
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
                        .ok_or(KotlinStructuralError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect();
                    results.push(self.rebuild(frame, children)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(KotlinStructuralError::MalformedWorkStack.into());
        }
        results
            .pop()
            .ok_or_else(|| KotlinStructuralError::MalformedWorkStack.into())
    }

    fn schedule_node<'a>(
        &mut self,
        node: &'a SemanticNode,
        pending: &mut Vec<LowerTask<'a>>,
        results: &mut Vec<KotlinStmt>,
    ) -> Result<(), R::Error> {
        match node {
            SemanticNode::Empty => results.push(KotlinStmt::Empty),
            SemanticNode::BasicBlock(block) => {
                let statements = block
                    .statements
                    .iter()
                    .map(|statement| self.dialect.statement(statement))
                    .collect::<Result<Vec<_>, _>>()?;
                results.push(KotlinStmt::Block(statements));
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
                        return Err(KotlinStructuralError::UnboundContinuation {
                            scope: leave.target,
                            target: *target,
                        }
                        .into());
                    }
                    SemanticLeaveKind::BreakLabel(label) => {
                        KotlinStmt::Break(self.controls.label_for(*label))
                    }
                    SemanticLeaveKind::ContinueLabel(label) => {
                        KotlinStmt::Continue(self.controls.label_for(*label))
                    }
                    SemanticLeaveKind::Return(value) => KotlinStmt::Return(
                        value
                            .as_ref()
                            .map(|value| {
                                self.dialect
                                    .return_expression(value, leave.condition.as_ref())
                            })
                            .transpose()?,
                    ),
                    SemanticLeaveKind::Throw(value) => {
                        KotlinStmt::Throw(self.dialect.throw_expression(value)?)
                    }
                    SemanticLeaveKind::Break => KotlinStmt::Break(self.leave_label(leave.target)),
                    SemanticLeaveKind::Continue => {
                        KotlinStmt::Continue(self.leave_label(leave.target))
                    }
                });
            }
        }
        Ok(())
    }

    fn rebuild(
        &mut self,
        frame: LowerFrame<'_>,
        children: Vec<KotlinStmt>,
    ) -> Result<KotlinStmt, R::Error> {
        let expected = frame.child_count();
        if children.len() != expected {
            return Err(KotlinStructuralError::ChildArity {
                expected,
                actual: children.len(),
            }
            .into());
        }
        let mut children = children.into_iter();
        Ok(match frame {
            LowerFrame::Sequence(_) => {
                KotlinStmt::Block(children.flat_map(Self::block_statements).collect())
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
                KotlinStmt::If {
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
                        KotlinStmt::While {
                            label,
                            condition,
                            body: Box::new(body),
                        }
                    }
                    SemanticLoopKind::PreTested => {
                        let lowered_condition = self.dialect.condition(condition)?;
                        match LoopConditionBinding::recover(setup, lowered_condition) {
                            BoundLoopCondition::Expression(condition) => KotlinStmt::While {
                                label,
                                condition,
                                body: Box::new(body),
                            },
                            BoundLoopCondition::Separate { mut setup } => {
                                setup.push(KotlinStmt::If {
                                    condition: self.dialect.negated_condition(condition)?,
                                    then_stmt: Box::new(KotlinStmt::Break(None)),
                                    else_stmt: None,
                                });
                                setup.extend(Self::block_statements(body));
                                KotlinStmt::While {
                                    label,
                                    condition: KotlinExpr::Literal(KotlinLiteral::Boolean(true)),
                                    body: Box::new(KotlinStmt::Block(setup)),
                                }
                            }
                        }
                    }
                    SemanticLoopKind::PostTested => {
                        let condition = self.dialect.condition(condition)?;
                        let mut statements = Self::block_statements(body);
                        statements.extend(setup);
                        KotlinStmt::DoWhile {
                            label,
                            body: Box::new(KotlinStmt::Block(statements)),
                            condition,
                        }
                    }
                    SemanticLoopKind::Endless => KotlinStmt::While {
                        label,
                        condition: KotlinExpr::Literal(KotlinLiteral::Boolean(true)),
                        body: Box::new(KotlinStmt::Block(
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
            } => KotlinStmt::For {
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
                KotlinStmt::ForEach {
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
            } => KotlinStmt::Switch {
                label: self.controls.label(region),
                selector: self.dialect.expression(selector)?,
                cases: cases
                    .iter()
                    .zip(children)
                    .map(|(case, body)| KotlinSwitchCase {
                        labels: case
                            .values
                            .iter()
                            .map(|value| KotlinExpr::Literal(KotlinLiteral::Integer(*value)))
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
                    KotlinStmt::Synchronized {
                        lock: self.dialect.expression(lock)?,
                        body: Box::new(body),
                    }
                }
            }
            LowerFrame::Label(label) => KotlinStmt::Labeled {
                label: ControlLayout::label_identifier(label),
                body: Box::new(Self::child(&mut children)?),
            },
        })
    }

    fn loop_control_label(
        &self,
        control: crate::ir::SemanticLoopControl,
    ) -> Option<KotlinIdentifier> {
        self.controls.loop_label(control)
    }

    fn leave_label(&self, target: crate::ir::RegionId) -> Option<KotlinIdentifier> {
        self.controls.leave_label(target)
    }

    fn for_initializer(statement: KotlinStmt) -> Result<KotlinStmt, KotlinStructuralError> {
        match statement {
            KotlinStmt::Variable { .. } | KotlinStmt::Expression(_) | KotlinStmt::Assign { .. } => {
                Ok(statement)
            }
            _ => Err(KotlinStructuralError::InvalidForInitializer),
        }
    }

    fn update_expression(statement: KotlinStmt) -> Result<KotlinExpr, KotlinStructuralError> {
        match statement {
            KotlinStmt::Expression(expression) => Ok(expression),
            KotlinStmt::Assign { target, op, value } => Ok(KotlinExpr::Assignment {
                target: Box::new(target),
                op,
                value: Box::new(value),
            }),
            _ => Err(KotlinStructuralError::InvalidForUpdate),
        }
    }

    fn block_statements(stmt: KotlinStmt) -> Vec<KotlinStmt> {
        match stmt {
            KotlinStmt::Block(statements) => statements,
            KotlinStmt::Empty => Vec::new(),
            other => vec![other],
        }
    }

    fn child(children: &mut impl Iterator<Item = KotlinStmt>) -> Result<KotlinStmt, R::Error> {
        children
            .next()
            .ok_or_else(|| KotlinStructuralError::MalformedWorkStack.into())
    }
}

enum BoundLoopCondition {
    Expression(KotlinExpr),
    Separate { setup: Vec<KotlinStmt> },
}

struct LoopConditionBinding;

impl LoopConditionBinding {
    fn recover(setup: Vec<KotlinStmt>, condition: KotlinExpr) -> BoundLoopCondition {
        let [KotlinStmt::Assign {
            target,
            op: KotlinAssignOp::Assign,
            value,
        }] = setup.as_slice()
        else {
            return BoundLoopCondition::Separate { setup };
        };
        let KotlinExpr::Name(name) = target else {
            return BoundLoopCondition::Separate { setup };
        };
        let assignment = KotlinExpr::Assignment {
            target: Box::new(target.clone()),
            op: KotlinAssignOp::Assign,
            value: Box::new(value.clone()),
        };
        match Self::bind_first_evaluation(condition, name, assignment) {
            Some(condition) => BoundLoopCondition::Expression(condition),
            None => BoundLoopCondition::Separate { setup },
        }
    }

    /// The setup may move into the condition only at its first mandatory
    /// evaluation point. This preserves Kotlin's left-to-right evaluation,
    /// short-circuit behavior, exceptions, and side effects.
    fn bind_first_evaluation(
        expression: KotlinExpr,
        name: &KotlinIdentifier,
        assignment: KotlinExpr,
    ) -> Option<KotlinExpr> {
        Some(match expression {
            KotlinExpr::Name(candidate) if &candidate == name => assignment,
            KotlinExpr::Unary { op, operand } => KotlinExpr::Unary {
                op,
                operand: Box::new(Self::bind_first_evaluation(*operand, name, assignment)?),
            },
            KotlinExpr::Binary { left, op, right } => KotlinExpr::Binary {
                left: Box::new(Self::bind_first_evaluation(*left, name, assignment)?),
                op,
                right,
            },
            KotlinExpr::Cast { ty, value } => KotlinExpr::Cast {
                ty,
                value: Box::new(Self::bind_first_evaluation(*value, name, assignment)?),
            },
            KotlinExpr::InstanceOf { value, ty } => KotlinExpr::InstanceOf {
                value: Box::new(Self::bind_first_evaluation(*value, name, assignment)?),
                ty,
            },
            KotlinExpr::Field { owner, name: field } => KotlinExpr::Field {
                owner: Box::new(Self::bind_first_evaluation(*owner, name, assignment)?),
                name: field,
            },
            KotlinExpr::ArrayAccess { array, index } => KotlinExpr::ArrayAccess {
                array: Box::new(Self::bind_first_evaluation(*array, name, assignment)?),
                index,
            },
            KotlinExpr::Call {
                receiver: Some(receiver),
                owner,
                type_arguments,
                method,
                args,
            } => KotlinExpr::Call {
                receiver: Some(Box::new(Self::bind_first_evaluation(
                    *receiver, name, assignment,
                )?)),
                owner,
                type_arguments,
                method,
                args,
            },
            KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => KotlinExpr::Conditional {
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
