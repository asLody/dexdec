use std::collections::{BTreeMap, BTreeSet};

use crate::language::java::{
    JavaAssignOp, JavaAstRewriter, JavaBinaryOp, JavaConstructorTarget, JavaExpr, JavaIdentifier,
    JavaLiteral, JavaMethodDeclarationKind, JavaStmt, JavaType, JavaTypeDeclaration,
    JavaTypeDeclarationKind, JavaUnaryOp,
};

/// Removes constructor syntax that Java inserts implicitly.
pub(super) struct ConstructorSyntaxRecovery;

impl ConstructorSyntaxRecovery {
    pub(super) fn apply(declaration: &mut JavaTypeDeclaration) {
        let is_enum = declaration.kind == JavaTypeDeclarationKind::Enum;
        let final_fields = declaration
            .fields
            .iter()
            .filter(|field| {
                field
                    .modifiers
                    .contains(&crate::language::java::JavaModifier::Final)
            })
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        for constructor in declaration
            .methods
            .iter_mut()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
        {
            let Some(body) = constructor.body.as_mut() else {
                continue;
            };
            let JavaStmt::Block(statements) = &mut body.root else {
                continue;
            };
            let parameters = constructor
                .parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            let guards = ConstructorParameterGuards::take(statements, &parameters);
            ConstructorCapturePrelude::schedule(statements, &parameters, &final_fields);
            Self::schedule_arguments(statements);
            ConstructorParameterGuards::restore(statements, guards);
            if is_enum {
                // Java enum constructors invoke java.lang.Enum implicitly and
                // reject an explicit super(name, ordinal) invocation.
                statements.retain(|statement| {
                    !matches!(
                        statement,
                        JavaStmt::ConstructorInvocation {
                            target: JavaConstructorTarget::Super,
                            ..
                        }
                    )
                });
            }
            if matches!(
                statements.first(),
                Some(JavaStmt::ConstructorInvocation {
                    target: JavaConstructorTarget::Super,
                    args,
                }) if args.is_empty()
            ) {
                statements.remove(0);
            }
        }
    }

    fn schedule_arguments(statements: &mut Vec<JavaStmt>) {
        ConstructorEvaluationOrder::recover(statements);
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        if invocation == 0 {
            return;
        }

        let Some(bindings) = ConstructorBindings::analyze(&statements[..invocation]) else {
            return;
        };
        let JavaStmt::ConstructorInvocation { args, .. } = &statements[invocation] else {
            unreachable!("constructor invocation index was selected above")
        };
        if !bindings.can_schedule(args) {
            return;
        }

        let mut substitution = ConstructorSubstitution {
            values: &bindings.values,
        };
        let JavaStmt::ConstructorInvocation { args, .. } = &mut statements[invocation] else {
            unreachable!("constructor invocation index was selected above")
        };
        *args = std::mem::take(args)
            .into_iter()
            .map(|argument| substitution.rewrite_expression(argument))
            .collect();
        statements.drain(..invocation);
    }
}

struct ConstructorCapturePrelude;

struct ConstructorParameterGuards;

impl ConstructorParameterGuards {
    fn take(
        statements: &mut Vec<JavaStmt>,
        parameters: &BTreeSet<JavaIdentifier>,
    ) -> Vec<JavaStmt> {
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return Vec::new();
        };
        let leading = statements[..invocation]
            .iter()
            .take_while(|statement| Self::is_parameter_guard(statement, parameters))
            .count();
        statements.drain(..leading).collect()
    }

    fn restore(statements: &mut Vec<JavaStmt>, guards: Vec<JavaStmt>) {
        if guards.is_empty() {
            return;
        }
        let Some(0) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            statements.splice(0..0, guards);
            return;
        };
        statements.splice(1..1, guards);
    }

    fn is_parameter_guard(statement: &JavaStmt, parameters: &BTreeSet<JavaIdentifier>) -> bool {
        let JavaStmt::Expression(JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::Class(owner)),
            method,
            args,
            ..
        }) = statement
        else {
            return false;
        };
        let is_intrinsics = owner
            .name()
            .components()
            .last()
            .is_some_and(|component| component.as_str() == "Intrinsics");
        is_intrinsics
            && matches!(
                method.as_str(),
                "checkNotNullParameter" | "checkParameterIsNotNull"
            )
            && args
                .first()
                .is_some_and(|value| ConstructorCapturePrelude::is_capture_value(value, parameters))
    }
}

impl ConstructorCapturePrelude {
    fn schedule(
        statements: &mut Vec<JavaStmt>,
        parameters: &BTreeSet<JavaIdentifier>,
        final_fields: &BTreeSet<JavaIdentifier>,
    ) {
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        if invocation == 0
            || !statements[..invocation]
                .iter()
                .all(|statement| Self::is_capture_store(statement, parameters, final_fields))
        {
            return;
        }
        let invocation = statements.remove(invocation);
        statements.insert(0, invocation);
    }

    fn is_capture_store(
        statement: &JavaStmt,
        parameters: &BTreeSet<JavaIdentifier>,
        final_fields: &BTreeSet<JavaIdentifier>,
    ) -> bool {
        matches!(
            statement,
            JavaStmt::Assign {
                target: JavaExpr::Field { owner, name: field },
                value,
                ..
            } if matches!(owner.as_ref(), JavaExpr::This)
                && final_fields.contains(field)
                && Self::is_capture_value(value, parameters)
        )
    }

    fn is_capture_value(value: &JavaExpr, parameters: &BTreeSet<JavaIdentifier>) -> bool {
        match value {
            JavaExpr::Name(parameter) => parameters.contains(parameter),
            JavaExpr::QualifiedThis(_) => true,
            JavaExpr::Literal(_) => true,
            JavaExpr::Cast { value, .. } => Self::is_capture_value(value, parameters),
            _ => false,
        }
    }
}

struct ConstructorEvaluationOrder;

impl ConstructorEvaluationOrder {
    fn recover(statements: &mut Vec<JavaStmt>) {
        let Some(mut invocation) = statements
            .iter()
            .position(|statement| matches!(statement, JavaStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        let mut index = 0;
        while index < invocation {
            let Some(evaluation) = IdentityEvaluation::analyze(&statements[index]) else {
                index += 1;
                continue;
            };
            let mut binder = BoundReceiverBinder {
                input: &evaluation.input,
                evaluation: &evaluation.expression,
                replaced: false,
            };
            for candidate in &mut statements[index + 1..=invocation] {
                *candidate =
                    binder.rewrite_statement(std::mem::replace(candidate, JavaStmt::Empty));
                if binder.replaced {
                    break;
                }
            }
            if binder.replaced {
                statements.remove(index);
                invocation -= 1;
            } else {
                index += 1;
            }
        }
    }
}

struct IdentityEvaluation {
    input: JavaExpr,
    expression: JavaExpr,
}

impl IdentityEvaluation {
    fn analyze(statement: &JavaStmt) -> Option<Self> {
        let JavaStmt::Expression(
            expression @ JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::Class(owner)),
                method,
                args,
                ..
            },
        ) = statement
        else {
            return None;
        };
        let [input] = args.as_slice() else {
            return None;
        };
        let owner = owner.name();
        let components = owner.components();
        let is_objects = components
            .last()
            .is_some_and(|component| component == &JavaIdentifier::from_dex("Objects"));
        (is_objects && method == &JavaIdentifier::from_dex("requireNonNull")).then(|| Self {
            input: input.clone(),
            expression: expression.clone(),
        })
    }
}

struct BoundReceiverBinder<'a> {
    input: &'a JavaExpr,
    evaluation: &'a JavaExpr,
    replaced: bool,
}

impl BoundReceiverBinder<'_> {
    fn bind(&self, expression: JavaExpr) -> Option<JavaExpr> {
        if &expression == self.input {
            return Some(self.evaluation.clone());
        }
        let JavaExpr::Cast { ty, value } = expression else {
            return None;
        };
        Some(JavaExpr::Cast {
            ty,
            value: Box::new(self.bind(*value)?),
        })
    }
}

impl JavaAstRewriter for BoundReceiverBinder<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if self.replaced {
            return expression;
        }
        match expression {
            JavaExpr::MethodReference { receiver, method } => {
                let original = *receiver;
                let Some(receiver) = self.bind(original.clone()) else {
                    return JavaExpr::MethodReference {
                        receiver: Box::new(original),
                        method,
                    };
                };
                self.replaced = true;
                JavaExpr::MethodReference {
                    receiver: Box::new(receiver),
                    method,
                }
            }
            JavaExpr::New {
                enclosing,
                ty,
                target_type,
                mut args,
                anonymous_body,
            } => {
                if let Some((index, value)) =
                    args.iter().enumerate().find_map(|(index, argument)| {
                        self.bind(argument.clone()).map(|value| (index, value))
                    })
                {
                    args[index] = value;
                    self.replaced = true;
                }
                JavaExpr::New {
                    enclosing,
                    ty,
                    target_type,
                    args,
                    anonymous_body,
                }
            }
            expression => expression,
        }
    }
}

struct ConstructorBindings {
    order: Vec<JavaIdentifier>,
    values: BTreeMap<JavaIdentifier, JavaExpr>,
    dependencies: BTreeMap<JavaIdentifier, BTreeSet<JavaIdentifier>>,
}

impl ConstructorBindings {
    fn analyze(statements: &[JavaStmt]) -> Option<Self> {
        let mut dataflow = ConstructorDataflow::default();
        dataflow.evaluate(statements)?;
        dataflow.finalize_arrays()?;
        Some(Self {
            order: dataflow.order,
            values: dataflow.values,
            dependencies: dataflow.dependencies,
        })
    }

    fn can_schedule(&self, args: &[JavaExpr]) -> bool {
        let positions = args
            .iter()
            .enumerate()
            .flat_map(|(index, argument)| {
                ExpressionNames::collect(argument)
                    .into_iter()
                    .filter(|name| self.values.contains_key(name))
                    .map(move |name| (name, index))
            })
            .fold(
                BTreeMap::<JavaIdentifier, Vec<usize>>::new(),
                |mut positions, (name, index)| {
                    positions.entry(name).or_default().push(index);
                    positions
                },
            );

        let mut last_position = None;
        for name in &self.order {
            let mut visiting = BTreeSet::new();
            let Some(binding_positions) = self.binding_positions(name, &positions, &mut visiting)
            else {
                return false;
            };
            match binding_positions.as_slice() {
                [] if Self::stable(&self.values[name]) => continue,
                [position] if last_position.is_none_or(|previous| previous <= *position) => {
                    last_position = Some(*position);
                }
                _ => return false,
            }
        }

        let Some(last_position) = last_position else {
            return true;
        };
        args.iter().take(last_position).all(|argument| {
            let names = ExpressionNames::collect(argument);
            names.iter().any(|name| self.values.contains_key(name))
                || ReplayableExpression::check(argument)
        })
    }

    fn binding_positions(
        &self,
        name: &JavaIdentifier,
        direct: &BTreeMap<JavaIdentifier, Vec<usize>>,
        visiting: &mut BTreeSet<JavaIdentifier>,
    ) -> Option<Vec<usize>> {
        if !visiting.insert(name.clone()) {
            return None;
        }
        let mut positions = direct.get(name).cloned().unwrap_or_default();
        for (dependent, dependencies) in &self.dependencies {
            if dependencies.contains(name) {
                positions.extend(self.binding_positions(dependent, direct, visiting)?);
            }
        }
        visiting.remove(name);
        positions.sort_unstable();
        positions.dedup();
        Some(positions)
    }

    fn stable(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::Name(_)
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_)
            | JavaExpr::StaticField { .. } => true,
            JavaExpr::Cast { value, .. } => Self::stable(value),
            _ => false,
        }
    }
}

#[derive(Clone, Default)]
struct ConstructorDataflow {
    order: Vec<JavaIdentifier>,
    declared: BTreeSet<JavaIdentifier>,
    values: BTreeMap<JavaIdentifier, JavaExpr>,
    dependencies: BTreeMap<JavaIdentifier, BTreeSet<JavaIdentifier>>,
    array_writes: BTreeMap<JavaIdentifier, Vec<JavaExpr>>,
}

impl ConstructorDataflow {
    fn evaluate(&mut self, statements: &[JavaStmt]) -> Option<()> {
        for statement in statements {
            self.evaluate_statement(statement)?;
        }
        Some(())
    }

    fn evaluate_statement(&mut self, statement: &JavaStmt) -> Option<()> {
        match statement {
            JavaStmt::Variable {
                name,
                value: Some(value),
                ..
            } => self.declare(name, value),
            JavaStmt::Variable {
                name, value: None, ..
            } => self.declare_uninitialized(name),
            JavaStmt::Assign {
                target: JavaExpr::Name(name),
                op: JavaAssignOp::Assign,
                value,
            } => self.assign(name, value),
            JavaStmt::Assign {
                target: JavaExpr::ArrayAccess { array, index },
                op: JavaAssignOp::Assign,
                value,
            } => self.assign_array_element(array, index, value),
            JavaStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => self.branch(condition, then_stmt, else_stmt.as_deref()),
            JavaStmt::Block(statements) => self.evaluate(statements),
            _ => None,
        }
    }

    fn declare(&mut self, name: &JavaIdentifier, value: &JavaExpr) -> Option<()> {
        if !self.declared.insert(name.clone()) {
            return None;
        }
        let dependencies = self.binding_dependencies(value);
        let value = self.resolve(value.clone());
        self.record_evaluation(name, &value);
        self.values.insert(name.clone(), value);
        self.dependencies.insert(name.clone(), dependencies);
        Some(())
    }

    fn declare_uninitialized(&mut self, name: &JavaIdentifier) -> Option<()> {
        self.declared.insert(name.clone()).then_some(())
    }

    fn assign(&mut self, name: &JavaIdentifier, value: &JavaExpr) -> Option<()> {
        if !self.declared.contains(name)
            || self
                .values
                .get(name)
                .is_some_and(|prior| !ConstructorBindings::stable(prior))
        {
            return None;
        }
        let dependencies = self.binding_dependencies(value);
        let value = self.resolve(value.clone());
        self.record_evaluation(name, &value);
        self.values.insert(name.clone(), value);
        self.dependencies.insert(name.clone(), dependencies);
        Some(())
    }

    fn assign_array_element(
        &mut self,
        array: &JavaExpr,
        index: &JavaExpr,
        value: &JavaExpr,
    ) -> Option<()> {
        let JavaExpr::Name(name) = array else {
            return None;
        };
        let JavaExpr::Literal(JavaLiteral::Integer(index)) = index else {
            return None;
        };
        let index = usize::try_from(*index).ok()?;
        let JavaExpr::NewArray {
            dimensions,
            initializer,
            ..
        } = self.values.get(name)?
        else {
            return None;
        };
        if dimensions.len() != 1 || !initializer.is_empty() {
            return None;
        }
        let dependencies = self.binding_dependencies(value);
        let value = self.resolve(value.clone());
        let writes = self.array_writes.entry(name.clone()).or_default();
        if index != writes.len() {
            return None;
        }
        writes.push(value);
        self.dependencies
            .entry(name.clone())
            .or_default()
            .extend(dependencies);
        Some(())
    }

    fn finalize_arrays(&mut self) -> Option<()> {
        for (name, initializer) in std::mem::take(&mut self.array_writes) {
            let JavaExpr::NewArray {
                dimensions,
                initializer: current,
                ..
            } = self.values.get_mut(&name)?
            else {
                return None;
            };
            let [JavaExpr::Literal(JavaLiteral::Integer(length))] = dimensions.as_slice() else {
                return None;
            };
            if usize::try_from(*length).ok()? != initializer.len() || !current.is_empty() {
                return None;
            }
            dimensions.clear();
            *current = initializer;
        }
        Some(())
    }

    fn branch(
        &mut self,
        condition: &JavaExpr,
        then_stmt: &JavaStmt,
        else_stmt: Option<&JavaStmt>,
    ) -> Option<()> {
        let condition_dependencies = self.binding_dependencies(condition);
        let condition = self.resolve(condition.clone());

        let baseline = self.clone();
        let mut when_true = baseline.clone();
        when_true.evaluate_statement(then_stmt)?;
        let mut when_false = baseline.clone();
        if let Some(else_stmt) = else_stmt {
            when_false.evaluate_statement(else_stmt)?;
        }
        if when_true.values.keys().ne(when_false.values.keys())
            || when_true.array_writes != when_false.array_writes
        {
            return None;
        }

        let changed = when_true
            .values
            .iter()
            .filter(|(name, value)| when_false.values.get(*name) != Some(*value))
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        if changed.len() > 1 && !ReplayableExpression::check(&condition) {
            return None;
        }

        self.values = when_true
            .values
            .into_iter()
            .map(|(name, true_value)| {
                let false_value = when_false.values.get(&name)?.clone();
                let value = if true_value == false_value {
                    true_value
                } else {
                    JavaExpr::Conditional {
                        condition: Box::new(condition.clone()),
                        when_true: Box::new(true_value),
                        when_false: Box::new(false_value),
                    }
                };
                Some((name, value))
            })
            .collect::<Option<_>>()?;
        self.dependencies = when_true
            .dependencies
            .into_iter()
            .map(|(name, mut dependencies)| {
                dependencies.extend(
                    when_false
                        .dependencies
                        .get(&name)
                        .into_iter()
                        .flatten()
                        .cloned(),
                );
                if changed.contains(&name) {
                    dependencies.extend(condition_dependencies.iter().cloned());
                }
                (name, dependencies)
            })
            .collect();
        self.array_writes = when_true.array_writes;
        self.order = baseline.order;
        self.extend_order(&when_true.order);
        self.extend_order(&when_false.order);
        Some(())
    }

    fn binding_dependencies(&self, expression: &JavaExpr) -> BTreeSet<JavaIdentifier> {
        ExpressionNames::collect(expression)
            .into_iter()
            .filter(|name| self.values.contains_key(name))
            .collect()
    }

    fn resolve(&self, expression: JavaExpr) -> JavaExpr {
        ConstructorSubstitution {
            values: &self.values,
        }
        .rewrite_expression(expression)
    }

    fn record_evaluation(&mut self, name: &JavaIdentifier, value: &JavaExpr) {
        if !ConstructorBindings::stable(value) && !self.order.contains(name) {
            self.order.push(name.clone());
        }
    }

    fn extend_order(&mut self, order: &[JavaIdentifier]) {
        for name in order {
            if !self.order.contains(name) {
                self.order.push(name.clone());
            }
        }
    }
}

struct ReplayableExpression;

impl ReplayableExpression {
    fn check(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::This
            | JavaExpr::QualifiedThis(_)
            | JavaExpr::Super
            | JavaExpr::Name(_)
            | JavaExpr::Literal(_)
            | JavaExpr::ClassLiteral(_) => true,
            JavaExpr::Unary { operand, .. }
            | JavaExpr::Cast { value: operand, .. }
            | JavaExpr::InstanceOf { value: operand, .. } => Self::check(operand),
            JavaExpr::Binary { left, right, .. } => Self::check(left) && Self::check(right),
            _ => false,
        }
    }
}

struct ConstructorSubstitution<'a> {
    values: &'a BTreeMap<JavaIdentifier, JavaExpr>,
}

impl JavaAstRewriter for ConstructorSubstitution<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Name(name) => self
                .values
                .get(&name)
                .cloned()
                .unwrap_or(JavaExpr::Name(name)),
            JavaExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => ConstructorConditional::reduce(*condition, *when_true, *when_false),
            expression => expression,
        }
    }
}

struct ConstructorConditional;

impl ConstructorConditional {
    fn reduce(condition: JavaExpr, when_true: JavaExpr, when_false: JavaExpr) -> JavaExpr {
        let when_true = Self::under_assumption(&condition, true, when_true);
        let when_false = Self::under_assumption(&condition, false, when_false);
        if when_true == when_false {
            return when_true;
        }
        JavaExpr::Conditional {
            condition: Box::new(condition),
            when_true: Box::new(when_true),
            when_false: Box::new(when_false),
        }
    }

    fn under_assumption(condition: &JavaExpr, truth: bool, expression: JavaExpr) -> JavaExpr {
        let JavaExpr::Conditional {
            condition: nested_condition,
            when_true,
            when_false,
        } = expression
        else {
            return expression;
        };
        if !ReplayableExpression::check(condition)
            || !ReplayableExpression::check(&nested_condition)
        {
            return JavaExpr::Conditional {
                condition: nested_condition,
                when_true,
                when_false,
            };
        }
        match PredicateRelation::between(condition, &nested_condition) {
            PredicateRelation::Equivalent => {
                if truth {
                    *when_true
                } else {
                    *when_false
                }
            }
            PredicateRelation::Complement => {
                if truth {
                    *when_false
                } else {
                    *when_true
                }
            }
            PredicateRelation::Independent => JavaExpr::Conditional {
                condition: nested_condition,
                when_true,
                when_false,
            },
        }
    }
}

enum PredicateRelation {
    Equivalent,
    Complement,
    Independent,
}

impl PredicateRelation {
    fn between(left: &JavaExpr, right: &JavaExpr) -> Self {
        if left == right {
            return Self::Equivalent;
        }
        if matches!(
            (left, right),
            (
                JavaExpr::Unary {
                    op: JavaUnaryOp::LogicalNot,
                    operand
                },
                other
            ) | (
                other,
                JavaExpr::Unary {
                    op: JavaUnaryOp::LogicalNot,
                    operand
                }
            ) if operand.as_ref() == other
        ) {
            return Self::Complement;
        }
        let (
            JavaExpr::Binary {
                left: left_operand,
                op: left_operator,
                right: left_right_operand,
            },
            JavaExpr::Binary {
                left: right_operand,
                op: right_operator,
                right: right_right_operand,
            },
        ) = (left, right)
        else {
            return Self::Independent;
        };
        let complementary_operator = matches!(
            (left_operator, right_operator),
            (JavaBinaryOp::Equal, JavaBinaryOp::NotEqual)
                | (JavaBinaryOp::NotEqual, JavaBinaryOp::Equal)
        );
        if complementary_operator
            && left_operand == right_operand
            && left_right_operand == right_right_operand
        {
            Self::Complement
        } else {
            Self::Independent
        }
    }
}

struct ExpressionNames;

impl ExpressionNames {
    fn collect(expression: &JavaExpr) -> BTreeSet<JavaIdentifier> {
        let mut names = BTreeSet::new();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                JavaExpr::Name(name) => {
                    names.insert(name.clone());
                }
                JavaExpr::This
                | JavaExpr::QualifiedThis(_)
                | JavaExpr::Super
                | JavaExpr::Literal(_)
                | JavaExpr::ClassLiteral(_)
                | JavaExpr::StaticField { .. } => {}
                JavaExpr::Field { owner, .. } => pending.push(owner),
                JavaExpr::ArrayAccess { array, index } => {
                    pending.push(index);
                    pending.push(array);
                }
                JavaExpr::Call { receiver, args, .. } => {
                    pending.extend(args.iter().rev());
                    pending.extend(receiver.iter().map(|value| value.as_ref()));
                }
                JavaExpr::MethodReference { receiver, .. } => pending.push(receiver),
                JavaExpr::Lambda { body, .. } => pending.push(body),
                JavaExpr::BlockLambda { .. } => {}
                JavaExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args.iter().rev());
                    pending.extend(enclosing.iter().map(|value| value.as_ref()));
                }
                JavaExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(initializer.iter().rev());
                    pending.extend(dimensions.iter().rev());
                }
                JavaExpr::Unary { operand, .. }
                | JavaExpr::Cast { value: operand, .. }
                | JavaExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                JavaExpr::Update { target, .. } => pending.push(target),
                JavaExpr::Binary { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                JavaExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.push(when_false);
                    pending.push(when_true);
                    pending.push(condition);
                }
                JavaExpr::Assignment { target, value, .. } => {
                    pending.push(value);
                    pending.push(target);
                }
            }
        }
        names
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{ConstructorCapturePrelude, ConstructorParameterGuards, ConstructorSyntaxRecovery};
    use crate::language::java::{
        JavaAssignOp, JavaConstructorTarget, JavaExpr, JavaIdentifier, JavaStmt, JavaType,
    };

    #[test]
    fn casted_capture_stores_move_after_the_super_invocation() {
        let parameter = JavaIdentifier::from_dex("captured");
        let field = JavaIdentifier::from_dex("field");
        let constant_field = JavaIdentifier::from_dex("constantField");
        let mut statements = vec![
            JavaStmt::Assign {
                target: JavaExpr::Field {
                    owner: Box::new(JavaExpr::This),
                    name: field.clone(),
                },
                op: JavaAssignOp::Assign,
                value: JavaExpr::Cast {
                    ty: JavaType::source_class("java.util.List"),
                    value: Box::new(JavaExpr::Name(parameter.clone())),
                },
            },
            JavaStmt::Assign {
                target: JavaExpr::Field {
                    owner: Box::new(JavaExpr::This),
                    name: constant_field.clone(),
                },
                op: JavaAssignOp::Assign,
                value: JavaExpr::Literal(crate::language::java::JavaLiteral::Integer(0)),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Literal(
                    crate::language::java::JavaLiteral::Integer(2),
                )],
            },
        ];

        ConstructorCapturePrelude::schedule(
            &mut statements,
            &BTreeSet::from([parameter]),
            &BTreeSet::from([field, constant_field]),
        );

        assert!(matches!(
            statements.first(),
            Some(JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                ..
            })
        ));
    }

    #[test]
    fn kotlin_parameter_guards_move_after_the_super_invocation() {
        let parameter = JavaIdentifier::from_dex("context");
        let alias = JavaIdentifier::from_dex("checkedContext");
        let mut statements = vec![
            JavaStmt::Expression(JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::source_class("kotlin.jvm.internal.Intrinsics")),
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("checkNotNullParameter"),
                args: vec![
                    JavaExpr::Name(parameter.clone()),
                    JavaExpr::Literal(crate::language::java::JavaLiteral::String(
                        crate::ir::Utf16String::from("context"),
                    )),
                ],
            }),
            JavaStmt::Variable {
                ty: JavaType::source_class("android.content.Context"),
                name: alias.clone(),
                value: Some(JavaExpr::Name(parameter.clone())),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(alias)],
            },
        ];

        let parameters = BTreeSet::from([parameter]);
        let guards = ConstructorParameterGuards::take(&mut statements, &parameters);
        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);
        ConstructorParameterGuards::restore(&mut statements, guards);

        assert!(matches!(
            statements.first(),
            Some(JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                ..
            })
        ));
    }

    #[test]
    fn static_field_bindings_inline_into_constructor_arguments() {
        let binding = JavaIdentifier::from_dex("trueValue");
        let value = JavaExpr::StaticField {
            owner: JavaType::source_class("java.lang.Boolean"),
            name: JavaIdentifier::from_dex("TRUE"),
        };
        let mut statements = vec![
            JavaStmt::Variable {
                ty: JavaType::source_class("java.lang.Boolean"),
                name: binding.clone(),
                value: Some(value.clone()),
            },
            JavaStmt::ConstructorInvocation {
                target: JavaConstructorTarget::Super,
                args: vec![JavaExpr::Name(binding.clone()), JavaExpr::Name(binding)],
            },
        ];

        ConstructorSyntaxRecovery::schedule_arguments(&mut statements);

        assert!(matches!(
            statements.as_slice(),
            [JavaStmt::ConstructorInvocation { args, .. }]
                if args == &vec![value.clone(), value]
        ));
    }
}
