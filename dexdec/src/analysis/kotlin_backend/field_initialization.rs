use std::collections::BTreeSet;

use crate::language::kotlin::{
    KotlinAssignOp, KotlinAstRewriter, KotlinBinaryOp, KotlinConstructorTarget, KotlinExpr,
    KotlinIdentifier, KotlinMethodDeclarationKind, KotlinModifier, KotlinNullabilityFacts,
    KotlinStmt, KotlinType, KotlinTypeDeclaration,
};

pub(super) struct FieldInitializationFacts {
    legal_blank_finals: BTreeSet<KotlinIdentifier>,
    non_null_blank_finals: BTreeSet<KotlinIdentifier>,
    inferred_blank_finals: BTreeSet<KotlinIdentifier>,
}

impl FieldInitializationFacts {
    pub(super) fn refresh_tree(
        declaration: &mut KotlinTypeDeclaration,
        object_initializer: Option<&KotlinType>,
    ) {
        Self::analyze(declaration, object_initializer).apply(declaration);
        for nested in &mut declaration.nested {
            Self::refresh_tree(nested, None);
        }
    }

    pub(super) fn analyze(
        declaration: &KotlinTypeDeclaration,
        object_initializer: Option<&KotlinType>,
    ) -> Self {
        let declared_candidates = declaration
            .fields
            .iter()
            .filter(|field| {
                Self::has_default_initializer(field)
                    && field.modifiers.contains(&KotlinModifier::Final)
                    && !field.modifiers.contains(&KotlinModifier::Static)
            })
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        let constructors = declaration
            .methods
            .iter()
            .filter(|method| {
                method.kind == KotlinMethodDeclarationKind::Constructor
                    || (object_initializer.is_some()
                        && method.kind == KotlinMethodDeclarationKind::ClassInitializer)
            })
            .collect::<Vec<_>>();
        let mut external_writes = InstanceFieldWriteCollector::default();
        for method in declaration
            .methods
            .iter()
            .filter(|method| method.kind != KotlinMethodDeclarationKind::Constructor)
        {
            if let Some(body) = &method.body {
                external_writes.rewrite_statement(body.root.clone());
            }
        }
        let inferred_blank_finals = declaration
            .fields
            .iter()
            .filter(|field| {
                Self::has_default_initializer(field)
                    && !field.modifiers.contains(&KotlinModifier::Final)
                    && !field.modifiers.contains(&KotlinModifier::Static)
                    && field.modifiers.contains(&KotlinModifier::Private)
            })
            .filter(|field| !external_writes.names.contains(&field.name))
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        let candidates = declared_candidates
            .union(&inferred_blank_finals)
            .cloned()
            .collect::<BTreeSet<_>>();
        let legal_blank_finals = candidates
            .into_iter()
            .filter(|field| {
                !constructors.is_empty()
                    && constructors.iter().all(|constructor| {
                        constructor.body.as_ref().is_some_and(|body| {
                            FieldInitializationAnalysis::new(field, object_initializer)
                                .accepts(&body.root)
                        })
                    })
            })
            .collect::<BTreeSet<_>>();
        let non_null_blank_finals = legal_blank_finals
            .iter()
            .filter(|field| {
                let mut values = FieldAssignmentValues::new(field, object_initializer);
                for constructor in &constructors {
                    if let Some(body) = &constructor.body {
                        values.rewrite_statement(body.root.clone());
                    }
                }
                values.saw_assignment && values.all_non_null
            })
            .cloned()
            .collect();
        Self {
            legal_blank_finals,
            non_null_blank_finals,
            inferred_blank_finals,
        }
    }

    pub(super) fn apply(self, declaration: &mut KotlinTypeDeclaration) {
        for field in &mut declaration.fields {
            let default_initializer = Self::has_default_initializer(field);
            if self.inferred_blank_finals.contains(&field.name)
                && self.legal_blank_finals.contains(&field.name)
            {
                field.modifiers.push(KotlinModifier::Final);
            }
            if default_initializer && self.legal_blank_finals.contains(&field.name) {
                field.initializer = None;
            }
            if self.non_null_blank_finals.contains(&field.name) {
                field.nullable = false;
            }
            if default_initializer
                && field.modifiers.contains(&KotlinModifier::Final)
                && !field.modifiers.contains(&KotlinModifier::Static)
                && !self.legal_blank_finals.contains(&field.name)
            {
                field
                    .modifiers
                    .retain(|modifier| *modifier != KotlinModifier::Final);
            }
        }
    }

    fn has_default_initializer(field: &crate::language::kotlin::KotlinFieldDeclaration) -> bool {
        match (&field.ty, field.initializer.as_ref()) {
            (_, None) => true,
            (
                crate::language::kotlin::KotlinType::Class(_)
                | crate::language::kotlin::KotlinType::Array(_)
                | crate::language::kotlin::KotlinType::Variable(_),
                Some(KotlinExpr::Literal(crate::language::kotlin::KotlinLiteral::Null)),
            ) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Default)]
struct InstanceFieldWriteCollector {
    names: BTreeSet<KotlinIdentifier>,
}

impl InstanceFieldWriteCollector {
    fn record(&mut self, target: &KotlinExpr) {
        if let Some(name) = Self::target_name(target) {
            self.names.insert(name.clone());
        }
    }

    fn target_name(expression: &KotlinExpr) -> Option<&KotlinIdentifier> {
        match expression {
            KotlinExpr::Field { owner, name } if matches!(owner.as_ref(), KotlinExpr::This) => {
                Some(name)
            }
            KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
                Self::target_name(value)
            }
            _ => None,
        }
    }
}

impl KotlinAstRewriter for InstanceFieldWriteCollector {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(
        &mut self,
        _body: &mut crate::language::kotlin::KotlinAnonymousClassBody,
    ) {
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Assign { target, .. } = &statement {
            self.record(target);
        }
        statement
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match &expression {
            KotlinExpr::Assignment { target, .. } | KotlinExpr::Update { target, .. } => {
                self.record(target)
            }
            _ => {}
        }
        expression
    }
}

fn initializes_field(
    target: &KotlinExpr,
    field: &KotlinIdentifier,
    object_initializer: Option<&KotlinType>,
) -> bool {
    match target {
        KotlinExpr::Field { owner, name } => {
            name == field && matches!(owner.as_ref(), KotlinExpr::This)
        }
        KotlinExpr::StaticField { owner, name } => {
            name == field && object_initializer.is_some_and(|object| owner == object)
        }
        KotlinExpr::Name(name) => object_initializer.is_some() && name == field,
        KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
            initializes_field(value, field, object_initializer)
        }
        _ => false,
    }
}

struct FieldAssignmentValues<'a> {
    field: &'a KotlinIdentifier,
    object_initializer: Option<&'a KotlinType>,
    saw_assignment: bool,
    all_non_null: bool,
}

impl<'a> FieldAssignmentValues<'a> {
    fn new(field: &'a KotlinIdentifier, object_initializer: Option<&'a KotlinType>) -> Self {
        Self {
            field,
            object_initializer,
            saw_assignment: false,
            all_non_null: true,
        }
    }

    fn records(&mut self, target: &KotlinExpr, operator: KotlinAssignOp, value: &KotlinExpr) {
        if !initializes_field(target, self.field, self.object_initializer) {
            return;
        }
        self.saw_assignment = true;
        self.all_non_null &= operator == KotlinAssignOp::Assign
            && KotlinNullabilityFacts::expression_definitely_non_null(value);
    }
}

impl KotlinAstRewriter for FieldAssignmentValues<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(
        &mut self,
        _body: &mut crate::language::kotlin::KotlinAnonymousClassBody,
    ) {
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Assign { target, op, value } = &statement {
            self.records(target, *op, value);
        }
        statement
    }

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Assignment { target, op, value } = &expression {
            self.records(target, *op, value);
        }
        expression
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
    field: &'a KotlinIdentifier,
    object_initializer: Option<&'a KotlinType>,
    legal: bool,
}

impl<'a> FieldInitializationAnalysis<'a> {
    fn new(field: &'a KotlinIdentifier, object_initializer: Option<&'a KotlinType>) -> Self {
        Self {
            field,
            object_initializer,
            legal: true,
        }
    }

    fn accepts(mut self, body: &KotlinStmt) -> bool {
        let flow = self.statement(body, AssignmentCounts::ZERO);
        let completions = flow.normal.union(flow.returns);
        self.legal
            && (completions == AssignmentCounts::NONE || completions.is_definitely_assigned_once())
    }

    fn statement(&mut self, statement: &KotlinStmt, state: AssignmentCounts) -> InitializationFlow {
        match statement {
            KotlinStmt::Empty => InitializationFlow::normal(state),
            KotlinStmt::Block(statements) => self.statements(statements, state),
            KotlinStmt::Labeled { body, .. } | KotlinStmt::Synchronized { body, .. } => {
                self.statement(body, state)
            }
            KotlinStmt::Variable { value, .. } => InitializationFlow::normal(
                value
                    .as_ref()
                    .map_or(state, |value| self.expression(value, state)),
            ),
            KotlinStmt::Expression(expression) => {
                InitializationFlow::normal(self.expression(expression, state))
            }
            KotlinStmt::ConstructorInvocation { target, args } => {
                let state = self.expressions(args, state);
                InitializationFlow::normal(match target {
                    KotlinConstructorTarget::This => {
                        if !state.is_definitely_unassigned() {
                            self.legal = false;
                        }
                        AssignmentCounts::ONE
                    }
                    KotlinConstructorTarget::Super => state,
                })
            }
            KotlinStmt::Assign { target, op, value } => {
                let state = self.lvalue(target, state);
                let state = self.expression(value, state);
                InitializationFlow::normal(self.assignment(target, *op, state))
            }
            KotlinStmt::If {
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
            KotlinStmt::While {
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
            KotlinStmt::DoWhile {
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
            KotlinStmt::For {
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
            KotlinStmt::ForEach { iterable, body, .. } => {
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
            KotlinStmt::Switch {
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
            KotlinStmt::Try {
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
            KotlinStmt::Return(value) => {
                let state = value
                    .as_ref()
                    .map_or(state, |value| self.expression(value, state));
                InitializationFlow {
                    normal: AssignmentCounts::NONE,
                    returns: state,
                }
            }
            KotlinStmt::Throw(value) => {
                self.expression(value, state);
                InitializationFlow::normal(AssignmentCounts::NONE)
            }
            KotlinStmt::Break(_) | KotlinStmt::Continue(_) => {
                InitializationFlow::normal(AssignmentCounts::NONE)
            }
        }
    }

    fn statements(
        &mut self,
        statements: &[KotlinStmt],
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
        expressions: &[KotlinExpr],
        state: AssignmentCounts,
    ) -> AssignmentCounts {
        expressions.iter().fold(state, |state, expression| {
            self.expression(expression, state)
        })
    }

    fn expression(&mut self, expression: &KotlinExpr, state: AssignmentCounts) -> AssignmentCounts {
        match expression {
            KotlinExpr::SmartCast(value)
            | KotlinExpr::NonNullAssertion(value)
            | KotlinExpr::JvmIntrinsic {
                expression: value, ..
            } => self.expression(value, state),
            KotlinExpr::Field { owner, .. } => self.expression(owner, state),
            KotlinExpr::ArrayAccess { array, index } => {
                let state = self.expression(array, state);
                self.expression(index, state)
            }
            KotlinExpr::Call { receiver, args, .. } => {
                let state = receiver
                    .as_deref()
                    .map_or(state, |receiver| self.expression(receiver, state));
                self.expressions(args, state)
            }
            KotlinExpr::MethodReference { receiver, .. } => self.expression(receiver, state),
            KotlinExpr::Lambda { body, .. } => self.expression(body, state),
            KotlinExpr::BlockLambda { .. } => state,
            KotlinExpr::New {
                enclosing, args, ..
            } => {
                let state = enclosing
                    .as_deref()
                    .map_or(state, |enclosing| self.expression(enclosing, state));
                self.expressions(args, state)
            }
            KotlinExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => {
                let state = self.expressions(dimensions, state);
                self.expressions(initializer, state)
            }
            KotlinExpr::Unary { operand, .. }
            | KotlinExpr::Cast { value: operand, .. }
            | KotlinExpr::InstanceOf { value: operand, .. } => self.expression(operand, state),
            KotlinExpr::Update { target, .. } => {
                let state = self.lvalue(target, state);
                self.assignment(target, KotlinAssignOp::Add, state)
            }
            KotlinExpr::Binary { left, op, right } => {
                let state = self.expression(left, state);
                let right = self.expression(right, state);
                if matches!(op, KotlinBinaryOp::LogicalAnd | KotlinBinaryOp::LogicalOr) {
                    state.union(right)
                } else {
                    right
                }
            }
            KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => {
                let state = self.expression(condition, state);
                self.expression(when_true, state)
                    .union(self.expression(when_false, state))
            }
            KotlinExpr::Assignment { target, op, value } => {
                let state = self.lvalue(target, state);
                let state = self.expression(value, state);
                self.assignment(target, *op, state)
            }
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::Name(_)
            | KotlinExpr::Literal(_)
            | KotlinExpr::ClassLiteral(_)
            | KotlinExpr::ObjectReference(_)
            | KotlinExpr::StaticField { .. } => state,
        }
    }

    fn lvalue(&mut self, target: &KotlinExpr, state: AssignmentCounts) -> AssignmentCounts {
        match target {
            KotlinExpr::Field { owner, .. } => self.expression(owner, state),
            KotlinExpr::ArrayAccess { array, index } => {
                let state = self.expression(array, state);
                self.expression(index, state)
            }
            _ => state,
        }
    }

    fn assignment(
        &mut self,
        target: &KotlinExpr,
        operator: KotlinAssignOp,
        state: AssignmentCounts,
    ) -> AssignmentCounts {
        if !self.is_field(target) {
            return state;
        }
        if operator != KotlinAssignOp::Assign || !state.is_definitely_unassigned() {
            self.legal = false;
        }
        state.increment()
    }

    fn is_field(&self, expression: &KotlinExpr) -> bool {
        initializes_field(expression, self.field, self.object_initializer)
    }

    fn assigns_field(&self, statement: &KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Assign { target, .. } => self.is_field(target),
            KotlinStmt::Expression(expression) => self.expr_assigns_field(expression),
            KotlinStmt::Block(statements) => statements
                .iter()
                .any(|statement| self.assigns_field(statement)),
            KotlinStmt::Labeled { body, .. }
            | KotlinStmt::While { body, .. }
            | KotlinStmt::DoWhile { body, .. }
            | KotlinStmt::ForEach { body, .. }
            | KotlinStmt::Synchronized { body, .. } => self.assigns_field(body),
            KotlinStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                self.assigns_field(then_stmt)
                    || else_stmt
                        .as_deref()
                        .is_some_and(|statement| self.assigns_field(statement))
            }
            KotlinStmt::For { init, body, .. } => {
                init.iter().any(|statement| self.assigns_field(statement))
                    || self.assigns_field(body)
            }
            KotlinStmt::Switch { cases, .. } => cases
                .iter()
                .flat_map(|case| &case.body)
                .any(|statement| self.assigns_field(statement)),
            KotlinStmt::Try {
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

    fn expr_assigns_field(&self, root: &KotlinExpr) -> bool {
        let mut pending = vec![root];
        while let Some(expression) = pending.pop() {
            match expression {
                KotlinExpr::Assignment { target, value, .. } => {
                    if self.is_field(target) {
                        return true;
                    }
                    pending.extend([target.as_ref(), value.as_ref()]);
                }
                KotlinExpr::Update { target, .. } => {
                    if self.is_field(target) {
                        return true;
                    }
                    pending.push(target);
                }
                KotlinExpr::SmartCast(value)
                | KotlinExpr::NonNullAssertion(value)
                | KotlinExpr::JvmIntrinsic {
                    expression: value, ..
                } => pending.push(value),
                KotlinExpr::Field { owner, .. } => pending.push(owner),
                KotlinExpr::ArrayAccess { array, index } => {
                    pending.extend([array.as_ref(), index.as_ref()]);
                }
                KotlinExpr::Call { receiver, args, .. } => {
                    pending.extend(args);
                    pending.extend(receiver.as_deref());
                }
                KotlinExpr::MethodReference { receiver, .. } => pending.push(receiver),
                KotlinExpr::Lambda { body, .. } => pending.push(body),
                KotlinExpr::BlockLambda { .. } => {}
                KotlinExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args);
                    pending.extend(enclosing.as_deref());
                }
                KotlinExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(dimensions);
                    pending.extend(initializer);
                }
                KotlinExpr::Unary { operand, .. }
                | KotlinExpr::Cast { value: operand, .. }
                | KotlinExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                KotlinExpr::Binary { left, right, .. } => {
                    pending.extend([left.as_ref(), right.as_ref()]);
                }
                KotlinExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => pending.extend([condition.as_ref(), when_true.as_ref(), when_false.as_ref()]),
                KotlinExpr::This
                | KotlinExpr::QualifiedThis(_)
                | KotlinExpr::Super
                | KotlinExpr::Name(_)
                | KotlinExpr::Literal(_)
                | KotlinExpr::ClassLiteral(_)
                | KotlinExpr::ObjectReference(_)
                | KotlinExpr::StaticField { .. } => {}
            }
        }
        false
    }
}
