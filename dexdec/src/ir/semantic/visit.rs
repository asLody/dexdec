//! Central traversal contracts for Semantic IR.
//!
//! Analyses and transformations customize typed callbacks instead of
//! duplicating the complete `SemanticNode` recursion in every component.

use crate::ir::RegisterArg;

use super::{
    SemanticExpression, SemanticNode, SemanticOperand, SemanticOperation, SemanticPredicate,
    SemanticStatement, SemanticStatementKind,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticBindingKind {
    Catch,
    ForEach,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticFoldError {
    MalformedWorkStack,
    ChildArity { expected: usize, actual: usize },
    InstructionTree(crate::ir::InstructionTreeError),
    BooleanDomain(crate::ir::bdd::BddError),
    NonOperationStatement,
    NonOperationPredicate,
    CompletionChanged { transform: &'static str },
    BlockIdentityChanged { transform: &'static str },
    CfgIdentityChanged { transform: &'static str },
    ControlTopologyChanged { transform: &'static str },
}

impl std::fmt::Display for SemanticFoldError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedWorkStack => formatter.write_str("malformed semantic fold stack"),
            Self::ChildArity { expected, actual } => write!(
                formatter,
                "semantic fold frame has {actual} children, expected {expected}"
            ),
            Self::InstructionTree(source) => {
                write!(formatter, "instruction tree transform failed: {source}")
            }
            Self::BooleanDomain(source) => {
                write!(formatter, "semantic Boolean domain failed: {source}")
            }
            Self::NonOperationStatement => {
                formatter.write_str("semantic effect statement was transformed into a value")
            }
            Self::NonOperationPredicate => formatter
                .write_str("semantic predicate test was transformed into a non-operation value"),
            Self::CompletionChanged { transform } => write!(
                formatter,
                "semantic transform {transform} changed observable control completion"
            ),
            Self::BlockIdentityChanged { transform } => write!(
                formatter,
                "semantic transform {transform} changed a required CFG block identity"
            ),
            Self::CfgIdentityChanged { transform } => write!(
                formatter,
                "semantic transform {transform} changed required CFG block or edge identity"
            ),
            Self::ControlTopologyChanged { transform } => write!(
                formatter,
                "semantic transform {transform} changed the structured control topology"
            ),
        }
    }
}

impl std::error::Error for SemanticFoldError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InstructionTree(source) => Some(source),
            Self::BooleanDomain(source) => Some(source),
            _ => None,
        }
    }
}

impl From<crate::ir::InstructionTreeError> for SemanticFoldError {
    fn from(source: crate::ir::InstructionTreeError) -> Self {
        Self::InstructionTree(source)
    }
}

impl From<crate::ir::bdd::BddError> for SemanticFoldError {
    fn from(source: crate::ir::bdd::BddError) -> Self {
        Self::BooleanDomain(source)
    }
}

/// Controls whether an owning semantic fold descends into a node's children.
///
/// `Emit` is useful for proven subtree rewrites whose replacement is already
/// complete. It prevents transforms from rebuilding their own recursive tree
/// walkers merely to stop at an ownership boundary.
pub enum SemanticFoldControl {
    Descend(SemanticNode),
    Emit(SemanticNode),
}

pub trait SemanticVisitor {
    fn visit_node(&mut self, node: &SemanticNode) {
        walk_node(self, node);
    }

    fn enter_node(&mut self, _node: &SemanticNode) {}

    fn exit_node(&mut self, _node: &SemanticNode) {}

    fn visit_statement(&mut self, statement: &SemanticStatement) {
        walk_statement(self, statement);
    }

    fn visit_predicate(&mut self, predicate: &SemanticPredicate) {
        walk_predicate(self, predicate);
    }

    fn visit_expression(&mut self, expression: &SemanticExpression) {
        walk_expression(self, expression);
    }

    fn visit_operation(&mut self, operation: &SemanticOperation) {
        walk_operation(self, operation);
    }

    fn enter_operation(&mut self, _operation: &SemanticOperation) {}

    fn exit_operation(&mut self, _operation: &SemanticOperation) {}

    fn visit_register(&mut self, _register: &RegisterArg) {}

    fn visit_binding(&mut self, _kind: SemanticBindingKind, register: &RegisterArg) {
        self.visit_register(register);
    }
}

pub trait SemanticFolder {
    type Error: std::error::Error + From<SemanticFoldError>;

    fn enter_node(&mut self, _node: &SemanticNode) {}

    fn begin_node(&mut self, node: SemanticNode) -> Result<SemanticFoldControl, Self::Error> {
        Ok(SemanticFoldControl::Descend(node))
    }

    fn fold_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        fold_node(self, node)
    }

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(node)
    }
}

pub fn walk_node<V: SemanticVisitor + ?Sized>(visitor: &mut V, node: &SemanticNode) {
    let mut pending = vec![VisitTask::Enter(node)];
    while let Some(task) = pending.pop() {
        let node = match task {
            VisitTask::Exit(node) => {
                visitor.exit_node(node);
                continue;
            }
            VisitTask::Statement(statement) => {
                visitor.visit_statement(statement);
                continue;
            }
            VisitTask::Predicate(predicate) => {
                visitor.visit_predicate(predicate);
                continue;
            }
            VisitTask::Expression(expression) => {
                visitor.visit_expression(expression);
                continue;
            }
            VisitTask::Binding(kind, register) => {
                visitor.visit_binding(kind, register);
                continue;
            }
            VisitTask::Enter(node) => node,
        };
        visitor.enter_node(node);
        pending.push(VisitTask::Exit(node));
        match node {
            SemanticNode::Empty => {}
            SemanticNode::BasicBlock(block) => {
                pending.extend(block.statements.iter().rev().map(VisitTask::Statement))
            }
            SemanticNode::Sequence(children) => {
                pending.extend(children.iter().rev().map(|child| VisitTask::Enter(child)))
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                if let Some(node) = else_node {
                    pending.push(VisitTask::Enter(node));
                }
                pending.push(VisitTask::Enter(then_node));
                pending.push(VisitTask::Predicate(condition));
            }
            SemanticNode::Loop {
                kind, test, body, ..
            } => match kind {
                super::SemanticLoopKind::PreTested => {
                    pending.push(VisitTask::Enter(body));
                    pending.push(VisitTask::Predicate(&test.condition));
                    pending.push(VisitTask::Enter(&test.setup));
                }
                super::SemanticLoopKind::PostTested => {
                    pending.push(VisitTask::Predicate(&test.condition));
                    pending.push(VisitTask::Enter(&test.setup));
                    pending.push(VisitTask::Enter(body));
                }
                super::SemanticLoopKind::Endless => {
                    pending.push(VisitTask::Enter(body));
                    pending.push(VisitTask::Enter(&test.setup));
                }
            },
            SemanticNode::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                pending.push(VisitTask::Statement(update));
                pending.push(VisitTask::Enter(body));
                pending.push(VisitTask::Predicate(condition));
                pending.push(VisitTask::Statement(init));
            }
            SemanticNode::ForEach {
                variable,
                iterable,
                body,
                ..
            } => {
                pending.push(VisitTask::Enter(body));
                pending.push(VisitTask::Expression(iterable));
                pending.push(VisitTask::Binding(SemanticBindingKind::ForEach, variable));
            }
            SemanticNode::Switch {
                selector, cases, ..
            } => {
                pending.extend(cases.iter().rev().map(|case| VisitTask::Enter(&case.body)));
                pending.push(VisitTask::Expression(selector));
            }
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                if let Some(finally) = finally {
                    pending.push(VisitTask::Enter(&finally.body));
                }
                pending.extend(catches.iter().rev().flat_map(|catch| {
                    [
                        Some(VisitTask::Enter(&catch.body)),
                        catch.exception_value.as_ref().map(|register| {
                            VisitTask::Binding(SemanticBindingKind::Catch, register)
                        }),
                    ]
                    .into_iter()
                    .flatten()
                }));
                pending.push(VisitTask::Enter(body));
            }
            SemanticNode::Synchronized { lock, body, .. } => {
                pending.push(VisitTask::Enter(body));
                pending.push(VisitTask::Expression(lock));
            }
            SemanticNode::Label { body, .. } => {
                pending.push(VisitTask::Enter(body));
            }
            SemanticNode::Leave(leave) => {
                if let Some(condition) = &leave.condition {
                    pending.push(VisitTask::Predicate(condition));
                }
                if let Some(value) = leave.value() {
                    pending.push(VisitTask::Expression(value));
                }
            }
        }
    }
}

enum VisitTask<'a> {
    Enter(&'a SemanticNode),
    Exit(&'a SemanticNode),
    Statement(&'a SemanticStatement),
    Predicate(&'a SemanticPredicate),
    Expression(&'a SemanticExpression),
    Binding(SemanticBindingKind, &'a RegisterArg),
}

pub fn fold_node<F: SemanticFolder + ?Sized>(
    folder: &mut F,
    node: SemanticNode,
) -> Result<SemanticNode, F::Error> {
    let mut pending = vec![FoldTask::Visit(node)];
    let mut results = Vec::new();
    while let Some(task) = pending.pop() {
        match task {
            FoldTask::Visit(node) => {
                folder.enter_node(&node);
                let node = match folder.begin_node(node)? {
                    SemanticFoldControl::Descend(node) => node,
                    SemanticFoldControl::Emit(node) => {
                        results.push(node);
                        continue;
                    }
                };
                match node {
                    SemanticNode::Sequence(children) => {
                        let len = children.len();
                        pending.push(FoldTask::Rebuild(FoldFrame::Sequence(len)));
                        pending.extend(children.into_iter().rev().map(FoldTask::Visit));
                    }
                    SemanticNode::If {
                        condition,
                        then_node,
                        else_node,
                    } => {
                        let has_else = else_node.is_some();
                        pending.push(FoldTask::Rebuild(FoldFrame::If {
                            condition,
                            has_else,
                        }));
                        if let Some(node) = else_node {
                            pending.push(FoldTask::Visit(*node));
                        }
                        pending.push(FoldTask::Visit(*then_node));
                    }
                    SemanticNode::Loop {
                        control,
                        header,
                        kind,
                        test,
                        body,
                    } => {
                        pending.push(FoldTask::Rebuild(FoldFrame::Loop {
                            control,
                            header,
                            kind,
                            condition: test.condition,
                        }));
                        pending.push(FoldTask::Visit(*body));
                        pending.push(FoldTask::Visit(*test.setup));
                    }
                    SemanticNode::For {
                        control,
                        init,
                        condition,
                        update,
                        body,
                    } => {
                        pending.push(FoldTask::Rebuild(FoldFrame::For {
                            control,
                            init,
                            condition,
                            update,
                        }));
                        pending.push(FoldTask::Visit(*body));
                    }
                    SemanticNode::ForEach {
                        control,
                        variable,
                        iterable,
                        body,
                    } => {
                        pending.push(FoldTask::Rebuild(FoldFrame::ForEach {
                            control,
                            variable,
                            iterable,
                        }));
                        pending.push(FoldTask::Visit(*body));
                    }
                    SemanticNode::Switch {
                        region,
                        selector,
                        mut cases,
                    } => {
                        let bodies = cases
                            .iter_mut()
                            .map(|case| std::mem::replace(&mut case.body, SemanticNode::Empty))
                            .collect::<Vec<_>>();
                        pending.push(FoldTask::Rebuild(FoldFrame::Switch {
                            region,
                            selector,
                            cases,
                        }));
                        pending.extend(bodies.into_iter().rev().map(FoldTask::Visit));
                    }
                    SemanticNode::Try {
                        region,
                        body,
                        mut catches,
                        mut finally,
                    } => {
                        let mut bodies =
                            Vec::with_capacity(1 + catches.len() + usize::from(finally.is_some()));
                        bodies.push(*body);
                        bodies.extend(
                            catches.iter_mut().map(|catch| {
                                std::mem::replace(&mut catch.body, SemanticNode::Empty)
                            }),
                        );
                        if let Some(finally) = &mut finally {
                            bodies.push(std::mem::replace(
                                finally.body.as_mut(),
                                SemanticNode::Empty,
                            ));
                        }
                        pending.push(FoldTask::Rebuild(FoldFrame::Try {
                            region,
                            catches,
                            finally,
                        }));
                        pending.extend(bodies.into_iter().rev().map(FoldTask::Visit));
                    }
                    SemanticNode::Synchronized {
                        region,
                        lock,
                        method,
                        body,
                    } => {
                        pending.push(FoldTask::Rebuild(FoldFrame::Synchronized {
                            region,
                            lock,
                            method,
                        }));
                        pending.push(FoldTask::Visit(*body));
                    }
                    SemanticNode::Label { label, body } => {
                        pending.push(FoldTask::Rebuild(FoldFrame::Label(label)));
                        pending.push(FoldTask::Visit(*body));
                    }
                    leaf => results.push(folder.finish_node(leaf)?),
                }
            }
            FoldTask::Rebuild(frame) => {
                let child_count = frame.child_count();
                let start = results
                    .len()
                    .checked_sub(child_count)
                    .ok_or(SemanticFoldError::MalformedWorkStack)
                    .map_err(F::Error::from)?;
                let children = results.drain(start..).collect::<Vec<_>>();
                let node = frame.rebuild(children).map_err(F::Error::from)?;
                results.push(folder.finish_node(node)?);
            }
        }
    }
    if results.len() != 1 {
        return Err(F::Error::from(SemanticFoldError::MalformedWorkStack));
    }
    results
        .pop()
        .ok_or(SemanticFoldError::MalformedWorkStack)
        .map_err(F::Error::from)
}

enum FoldTask {
    Visit(SemanticNode),
    Rebuild(FoldFrame),
}

enum FoldFrame {
    Sequence(usize),
    If {
        condition: SemanticOperand<SemanticPredicate>,
        has_else: bool,
    },
    Loop {
        control: super::SemanticLoopControl,
        header: Option<crate::ir::BlockId>,
        kind: super::SemanticLoopKind,
        condition: SemanticOperand<SemanticPredicate>,
    },
    For {
        control: super::SemanticLoopControl,
        init: SemanticStatement,
        condition: SemanticOperand<SemanticPredicate>,
        update: SemanticStatement,
    },
    ForEach {
        control: super::SemanticLoopControl,
        variable: crate::ir::RegisterArg,
        iterable: SemanticOperand<SemanticExpression>,
    },
    Switch {
        region: Option<crate::ir::RegionId>,
        selector: SemanticOperand<SemanticExpression>,
        cases: Vec<super::SemanticSwitchCase>,
    },
    Try {
        region: crate::ir::RegionId,
        catches: Vec<super::SemanticCatch>,
        finally: Option<super::SemanticFinally>,
    },
    Synchronized {
        region: crate::ir::RegionId,
        lock: SemanticOperand<SemanticExpression>,
        method: bool,
    },
    Label(super::SemanticLabel),
}

impl FoldFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(len) => *len,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::Loop { .. } => 2,
            Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized { .. }
            | Self::Label(_) => 1,
            Self::Switch { cases, .. } => cases.len(),
            Self::Try {
                catches, finally, ..
            } => 1 + catches.len() + usize::from(finally.is_some()),
        }
    }

    fn rebuild(self, mut children: Vec<SemanticNode>) -> Result<SemanticNode, SemanticFoldError> {
        let expected = self.child_count();
        if children.len() != expected {
            return Err(SemanticFoldError::ChildArity {
                expected,
                actual: children.len(),
            });
        }
        let mut children = children.drain(..);
        let node = match self {
            Self::Sequence(_) => SemanticNode::Sequence(children.collect()),
            Self::If {
                condition,
                has_else,
            } => SemanticNode::If {
                condition,
                then_node: Box::new(Self::child(&mut children)?),
                else_node: if has_else {
                    Some(Box::new(Self::child(&mut children)?))
                } else {
                    None
                },
            },
            Self::Loop {
                control,
                header,
                kind,
                condition,
            } => SemanticNode::Loop {
                control,
                header,
                kind,
                test: super::SemanticLoopTest {
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
                mut cases,
            } => {
                for case in &mut cases {
                    case.body = Self::child(&mut children)?;
                }
                SemanticNode::Switch {
                    region,
                    selector,
                    cases,
                }
            }
            Self::Try {
                region,
                mut catches,
                mut finally,
            } => {
                let body = Box::new(Self::child(&mut children)?);
                for catch in &mut catches {
                    catch.body = Self::child(&mut children)?;
                }
                SemanticNode::Try {
                    region,
                    body,
                    catches,
                    finally: {
                        if let Some(finally) = &mut finally {
                            finally.body = Box::new(Self::child(&mut children)?);
                        }
                        finally
                    },
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
        Ok(node)
    }

    fn child(
        children: &mut impl Iterator<Item = SemanticNode>,
    ) -> Result<SemanticNode, SemanticFoldError> {
        children.next().ok_or(SemanticFoldError::MalformedWorkStack)
    }
}

pub fn walk_statement<V: SemanticVisitor + ?Sized>(visitor: &mut V, statement: &SemanticStatement) {
    match &statement.kind {
        SemanticStatementKind::Instruction(operation) => visitor.visit_operation(operation),
        SemanticStatementKind::Definition { value, .. } => visitor.visit_expression(value),
    }
}

pub fn walk_expression<V: SemanticVisitor + ?Sized>(
    visitor: &mut V,
    expression: &SemanticExpression,
) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            SemanticExpression::Register(register) => visitor.visit_register(register),
            SemanticExpression::Literal(_) => {}
            SemanticExpression::Operation(operation) => visitor.visit_operation(operation),
            SemanticExpression::Select {
                condition,
                when_true,
                when_false,
            } => {
                visitor.visit_predicate(condition);
                pending.push(when_false);
                pending.push(when_true);
            }
        }
    }
}

pub fn walk_predicate<V: SemanticVisitor + ?Sized>(visitor: &mut V, predicate: &SemanticPredicate) {
    let mut pending = vec![predicate];
    while let Some(predicate) = pending.pop() {
        match predicate {
            SemanticPredicate::Test(operation) => visitor.visit_operation(operation),
            SemanticPredicate::Not(inner) => pending.push(inner),
            SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                pending.extend(terms.iter().rev());
            }
            SemanticPredicate::True | SemanticPredicate::False => {}
        }
    }
}

pub fn walk_operation<V: SemanticVisitor + ?Sized>(visitor: &mut V, operation: &SemanticOperation) {
    let mut pending = vec![OperationVisitTask::Enter(operation)];
    while let Some(task) = pending.pop() {
        match task {
            OperationVisitTask::Enter(operation) => {
                visitor.enter_operation(operation);
                pending.push(OperationVisitTask::Exit(operation));
                pending.extend(
                    operation
                        .compound_target()
                        .map(OperationVisitTask::Expression),
                );
                pending.extend(
                    operation
                        .operands()
                        .iter()
                        .rev()
                        .map(OperationVisitTask::Expression),
                );
            }
            OperationVisitTask::Exit(operation) => visitor.exit_operation(operation),
            OperationVisitTask::Expression(expression) => visitor.visit_expression(expression),
        }
    }
}

enum OperationVisitTask<'a> {
    Enter(&'a SemanticOperation),
    Exit(&'a SemanticOperation),
    Expression(&'a SemanticExpression),
}
