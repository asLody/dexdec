use std::collections::BTreeSet;

use crate::language::java::{
    JavaAssignOp, JavaBinaryOp, JavaConstructorTarget, JavaExpr, JavaIdentifier,
    JavaMethodDeclarationKind, JavaModifier, JavaStmt, JavaTypeDeclaration,
};

pub(super) struct FieldInitializationFacts {
    legal_blank_finals: BTreeSet<JavaIdentifier>,
}

impl FieldInitializationFacts {
    pub(super) fn analyze(declaration: &JavaTypeDeclaration) -> Self {
        let candidates = declaration
            .fields
            .iter()
            .filter(|field| {
                field.initializer.is_none()
                    && field.modifiers.contains(&JavaModifier::Final)
                    && !field.modifiers.contains(&JavaModifier::Static)
            })
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        let constructors = declaration
            .methods
            .iter()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
            .collect::<Vec<_>>();
        let legal_blank_finals = candidates
            .into_iter()
            .filter(|field| {
                !constructors.is_empty()
                    && constructors.iter().all(|constructor| {
                        constructor.body.as_ref().is_some_and(|body| {
                            FieldInitializationAnalysis::new(field).accepts(&body.root)
                        })
                    })
            })
            .collect();
        Self { legal_blank_finals }
    }

    pub(super) fn apply(self, declaration: &mut JavaTypeDeclaration) {
        for field in &mut declaration.fields {
            if field.initializer.is_none()
                && field.modifiers.contains(&JavaModifier::Final)
                && !field.modifiers.contains(&JavaModifier::Static)
                && !self.legal_blank_finals.contains(&field.name)
            {
                field
                    .modifiers
                    .retain(|modifier| *modifier != JavaModifier::Final);
            }
        }
    }
}

#[derive(Clone, Copy)]
struct AssignmentCounts(u8);

impl AssignmentCounts {
    const NONE: Self = Self(0);
    const ZERO: Self = Self(1);
    const ONE: Self = Self(2);
    const MANY: Self = Self(4);

    fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    fn increment(self) -> Self {
        let mut result = Self::NONE;
        if self.0 & Self::ZERO.0 != 0 {
            result = result.union(Self::ONE);
        }
        if self.0 & (Self::ONE.0 | Self::MANY.0) != 0 {
            result = result.union(Self::MANY);
        }
        result
    }

    fn is_definitely_unassigned(self) -> bool {
        self == Self::ZERO
    }

    fn is_definitely_assigned_once(self) -> bool {
        self == Self::ONE
    }
}

impl PartialEq for AssignmentCounts {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(Clone, Copy)]
struct InitializationFlow {
    normal: AssignmentCounts,
    returns: AssignmentCounts,
}

impl InitializationFlow {
    fn normal(state: AssignmentCounts) -> Self {
        Self {
            normal: state,
            returns: AssignmentCounts::NONE,
        }
    }

    fn union(self, other: Self) -> Self {
        Self {
            normal: self.normal.union(other.normal),
            returns: self.returns.union(other.returns),
        }
    }
}

struct FieldInitializationAnalysis<'a> {
    field: &'a JavaIdentifier,
    legal: bool,
}

impl<'a> FieldInitializationAnalysis<'a> {
    fn new(field: &'a JavaIdentifier) -> Self {
        Self { field, legal: true }
    }

    fn accepts(mut self, body: &JavaStmt) -> bool {
        let flow = self.statement(body, AssignmentCounts::ZERO);
        let completions = flow.normal.union(flow.returns);
        self.legal
            && (completions == AssignmentCounts::NONE || completions.is_definitely_assigned_once())
    }

    fn statement(&mut self, statement: &JavaStmt, state: AssignmentCounts) -> InitializationFlow {
        match statement {
            JavaStmt::Empty => InitializationFlow::normal(state),
            JavaStmt::Block(statements) => self.statements(statements, state),
            JavaStmt::Labeled { body, .. } | JavaStmt::Synchronized { body, .. } => {
                self.statement(body, state)
            }
            JavaStmt::Variable { value, .. } => InitializationFlow::normal(
                value
                    .as_ref()
                    .map_or(state, |value| self.expression(value, state)),
            ),
            JavaStmt::Expression(expression) => {
                InitializationFlow::normal(self.expression(expression, state))
            }
            JavaStmt::ConstructorInvocation { target, args } => {
                let state = self.expressions(args, state);
                InitializationFlow::normal(match target {
                    JavaConstructorTarget::This => {
                        if !state.is_definitely_unassigned() {
                            self.legal = false;
                        }
                        AssignmentCounts::ONE
                    }
                    JavaConstructorTarget::Super => state,
                })
            }
            JavaStmt::Assign { target, op, value } => {
                let state = self.lvalue(target, state);
                let state = self.expression(value, state);
                InitializationFlow::normal(self.assignment(target, *op, state))
            }
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                let state = self.expression(condition, state);
                let then_flow = self.statement(then_stmt, state);
                let else_flow = else_stmt.as_deref().map_or_else(
                    || InitializationFlow::normal(state),
                    |statement| self.statement(statement, state),
                );
                then_flow.union(else_flow)
            }
            JavaStmt::While {
                condition, body, ..
            } => {
                let state = self.expression(condition, state);
                let body_flow = self.statement(body, state);
                if self.assigns_field(body) {
                    self.legal = false;
                }
                InitializationFlow {
                    normal: state.union(body_flow.normal),
                    returns: body_flow.returns,
                }
            }
            JavaStmt::DoWhile {
                body, condition, ..
            } => {
                let body_flow = self.statement(body, state);
                let normal = self.expression(condition, body_flow.normal);
                if self.assigns_field(body) {
                    self.legal = false;
                }
                InitializationFlow {
                    normal,
                    returns: body_flow.returns,
                }
            }
            JavaStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                let init_flow = self.statements(init, state);
                let entered = condition.as_ref().map_or(init_flow.normal, |value| {
                    self.expression(value, init_flow.normal)
                });
                let body_flow = self.statement(body, entered);
                let iterated = self.expressions(update, body_flow.normal);
                if self.assigns_field(body)
                    || init.iter().any(|statement| self.assigns_field(statement))
                    || update
                        .iter()
                        .any(|expression| self.expr_assigns_field(expression))
                {
                    self.legal = false;
                }
                InitializationFlow {
                    normal: entered.union(iterated),
                    returns: init_flow.returns.union(body_flow.returns),
                }
            }
            JavaStmt::ForEach { iterable, body, .. } => {
                let state = self.expression(iterable, state);
                let body_flow = self.statement(body, state);
                if self.assigns_field(body) {
                    self.legal = false;
                }
                InitializationFlow {
                    normal: state.union(body_flow.normal),
                    returns: body_flow.returns,
                }
            }
            JavaStmt::Switch {
                selector, cases, ..
            } => {
                let state = self.expression(selector, state);
                let mut flow = InitializationFlow {
                    normal: AssignmentCounts::NONE,
                    returns: AssignmentCounts::NONE,
                };
                let mut fallthrough = AssignmentCounts::NONE;
                for case in cases {
                    let entry = state.union(fallthrough);
                    let case_flow = self.statements(&case.body, entry);
                    fallthrough = case_flow.normal;
                    flow.returns = flow.returns.union(case_flow.returns);
                }
                if cases.iter().all(|case| !case.is_default) {
                    fallthrough = fallthrough.union(state);
                }
                flow.normal = fallthrough;
                flow
            }
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                let body_flow = self.statement(body, state);
                let catch_entry = state.union(body_flow.normal);
                let mut flow = body_flow;
                for catch in catches {
                    flow = flow.union(self.statement(&catch.body, catch_entry));
                }
                match finally {
                    Some(finally) => {
                        let finally_flow = self.statement(finally, flow.normal);
                        InitializationFlow {
                            normal: finally_flow.normal,
                            returns: flow.returns.union(finally_flow.returns),
                        }
                    }
                    None => flow,
                }
            }
            JavaStmt::Return(value) => {
                let state = value
                    .as_ref()
                    .map_or(state, |value| self.expression(value, state));
                InitializationFlow {
                    normal: AssignmentCounts::NONE,
                    returns: state,
                }
            }
            JavaStmt::Throw(value) => {
                self.expression(value, state);
                InitializationFlow::normal(AssignmentCounts::NONE)
            }
            JavaStmt::Break(_) | JavaStmt::Continue(_) => {
                InitializationFlow::normal(AssignmentCounts::NONE)
            }
        }
    }

    fn statements(
        &mut self,
        statements: &[JavaStmt],
        state: AssignmentCounts,
    ) -> InitializationFlow {
        let mut flow = InitializationFlow::normal(state);
        for statement in statements {
            let next = self.statement(statement, flow.normal);
            flow.normal = next.normal;
            flow.returns = flow.returns.union(next.returns);
        }
        flow
    }

    fn expressions(
        &mut self,
        expressions: &[JavaExpr],
        state: AssignmentCounts,
    ) -> AssignmentCounts {
        expressions.iter().fold(state, |state, expression| {
            self.expression(expression, state)
        })
    }

    fn expression(&mut self, expression: &JavaExpr, state: AssignmentCounts) -> AssignmentCounts {
        match expression {
            JavaExpr::Field { owner, .. } => self.expression(owner, state),
            JavaExpr::ArrayAccess { array, index } => {
                let state = self.expression(array, state);
                self.expression(index, state)
            }
            JavaExpr::Call { receiver, args, .. } => {
                let state = receiver
                    .as_deref()
                    .map_or(state, |receiver| self.expression(receiver, state));
                self.expressions(args, state)
            }
            JavaExpr::MethodReference { receiver, .. } => self.expression(receiver, state),
            JavaExpr::Lambda { body, .. } => self.expression(body, state),
            JavaExpr::BlockLambda { .. } => state,
            JavaExpr::New {
                enclosing, args, ..
            } => {
                let state = enclosing
                    .as_deref()
                    .map_or(state, |enclosing| self.expression(enclosing, state));
                self.expressions(args, state)
            }
            JavaExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => {
                let state = self.expressions(dimensions, state);
                self.expressions(initializer, state)
            }
            JavaExpr::Unary { operand, .. }
            | JavaExpr::Cast { value: operand, .. }
            | JavaExpr::InstanceOf { value: operand, .. } => self.expression(operand, state),
            JavaExpr::Update { target, .. } => {
                let state = self.lvalue(target, state);
                self.assignment(target, JavaAssignOp::Add, state)
            }
            JavaExpr::Binary { left, op, right } => {
                let state = self.expression(left, state);
                let right = self.expression(right, state);
                if matches!(op, JavaBinaryOp::LogicalAnd | JavaBinaryOp::LogicalOr) {
                    state.union(right)
                } else {
                    right
                }
            }
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => {
                let state = self.expression(condition, state);
                self.expression(when_true, state)
                    .union(self.expression(when_false, state))
            }
            JavaExpr::Assignment { target, op, value } => {
                let state = self.lvalue(target, state);
                let state = self.expression(value, state);
                self.assignment(target, *op, state)
            }
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::Name(_)
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_)
            | JavaExpr::StaticField { .. } => state,
        }
    }

    fn lvalue(&mut self, target: &JavaExpr, state: AssignmentCounts) -> AssignmentCounts {
        match target {
            JavaExpr::Field { owner, .. } => self.expression(owner, state),
            JavaExpr::ArrayAccess { array, index } => {
                let state = self.expression(array, state);
                self.expression(index, state)
            }
            _ => state,
        }
    }

    fn assignment(
        &mut self,
        target: &JavaExpr,
        operator: JavaAssignOp,
        state: AssignmentCounts,
    ) -> AssignmentCounts {
        if !self.is_field(target) {
            return state;
        }
        if operator != JavaAssignOp::Assign || !state.is_definitely_unassigned() {
            self.legal = false;
        }
        state.increment()
    }

    fn is_field(&self, expression: &JavaExpr) -> bool {
        matches!(
            expression,
            JavaExpr::Field { owner, name }
                if matches!(owner.as_ref(), JavaExpr::This) && name == self.field
        )
    }

    fn assigns_field(&self, statement: &JavaStmt) -> bool {
        match statement {
            JavaStmt::Assign { target, .. } => self.is_field(target),
            JavaStmt::Expression(expression) => self.expr_assigns_field(expression),
            JavaStmt::Block(statements) => statements
                .iter()
                .any(|statement| self.assigns_field(statement)),
            JavaStmt::Labeled { body, .. }
            | JavaStmt::While { body, .. }
            | JavaStmt::DoWhile { body, .. }
            | JavaStmt::ForEach { body, .. }
            | JavaStmt::Synchronized { body, .. } => self.assigns_field(body),
            JavaStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                self.assigns_field(then_stmt)
                    || else_stmt
                        .as_deref()
                        .is_some_and(|statement| self.assigns_field(statement))
            }
            JavaStmt::For { init, body, .. } => {
                init.iter().any(|statement| self.assigns_field(statement))
                    || self.assigns_field(body)
            }
            JavaStmt::Switch { cases, .. } => cases
                .iter()
                .flat_map(|case| &case.body)
                .any(|statement| self.assigns_field(statement)),
            JavaStmt::Try {
                body,
                catches,
                finally,
            } => {
                self.assigns_field(body)
                    || catches.iter().any(|catch| self.assigns_field(&catch.body))
                    || finally
                        .as_deref()
                        .is_some_and(|statement| self.assigns_field(statement))
            }
            _ => false,
        }
    }

    fn expr_assigns_field(&self, root: &JavaExpr) -> bool {
        let mut pending = vec![root];
        while let Some(expression) = pending.pop() {
            match expression {
                JavaExpr::Assignment { target, value, .. } => {
                    if self.is_field(target) {
                        return true;
                    }
                    pending.extend([target.as_ref(), value.as_ref()]);
                }
                JavaExpr::Update { target, .. } => {
                    if self.is_field(target) {
                        return true;
                    }
                    pending.push(target);
                }
                JavaExpr::Field { owner, .. } => pending.push(owner),
                JavaExpr::ArrayAccess { array, index } => {
                    pending.extend([array.as_ref(), index.as_ref()]);
                }
                JavaExpr::Call { receiver, args, .. } => {
                    pending.extend(args);
                    pending.extend(receiver.as_deref());
                }
                JavaExpr::MethodReference { receiver, .. } => pending.push(receiver),
                JavaExpr::Lambda { body, .. } => pending.push(body),
                JavaExpr::BlockLambda { .. } => {}
                JavaExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args);
                    pending.extend(enclosing.as_deref());
                }
                JavaExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(dimensions);
                    pending.extend(initializer);
                }
                JavaExpr::Unary { operand, .. }
                | JavaExpr::Cast { value: operand, .. }
                | JavaExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                JavaExpr::Binary { left, right, .. } => {
                    pending.extend([left.as_ref(), right.as_ref()]);
                }
                JavaExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => pending.extend([condition.as_ref(), when_true.as_ref(), when_false.as_ref()]),
                JavaExpr::This
                | JavaExpr::QualifiedThis(_)
                | JavaExpr::Super
                | JavaExpr::Name(_)
                | JavaExpr::Literal(_)
                | JavaExpr::ClassLiteral(_)
                | JavaExpr::StaticField { .. } => {}
            }
        }
        false
    }
}
