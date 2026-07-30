use std::collections::{BTreeMap, BTreeSet};

use crate::language::kotlin::{
    KotlinAssignOp, KotlinAstRewriter, KotlinBinaryOp, KotlinConstructorTarget, KotlinExpr,
    KotlinIdentifier, KotlinLiteral, KotlinMethodDeclarationKind, KotlinStmt, KotlinType,
    KotlinTypeDeclaration, KotlinUnaryOp,
};

/// Removes constructor syntax that Kotlin inserts implicitly.
pub(super) struct ConstructorSyntaxRecovery;

impl ConstructorSyntaxRecovery {
    pub(super) fn apply(declaration: &mut KotlinTypeDeclaration) {
        let final_fields = declaration
            .fields
            .iter()
            .filter(|field| {
                field
                    .modifiers
                    .contains(&crate::language::kotlin::KotlinModifier::Final)
            })
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        for constructor in declaration
            .methods
            .iter_mut()
            .filter(|method| method.kind == KotlinMethodDeclarationKind::Constructor)
        {
            let Some(body) = constructor.body.as_mut() else {
                continue;
            };
            let KotlinStmt::Block(statements) = &mut body.root else {
                continue;
            };
            ConstructorCapturePrelude::schedule(
                statements,
                &constructor
                    .parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect(),
                &final_fields,
            );
            Self::schedule_arguments(statements);
            if matches!(
                statements.first(),
                Some(KotlinStmt::ConstructorInvocation {
                    target: KotlinConstructorTarget::Super,
                    args,
                }) if args.is_empty()
            ) {
                statements.remove(0);
            }
        }
    }

    fn schedule_arguments(statements: &mut Vec<KotlinStmt>) {
        ConstructorEvaluationOrder::recover(statements);
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, KotlinStmt::ConstructorInvocation { .. }))
        else {
            return;
        };
        if invocation == 0 {
            return;
        }

        let Some(bindings) = ConstructorBindings::analyze(&statements[..invocation]) else {
            return;
        };
        let KotlinStmt::ConstructorInvocation { args, .. } = &statements[invocation] else {
            unreachable!("constructor invocation index was selected above")
        };
        if !bindings.can_schedule(args) {
            return;
        }

        let mut substitution = ConstructorSubstitution {
            values: &bindings.values,
        };
        let KotlinStmt::ConstructorInvocation { args, .. } = &mut statements[invocation] else {
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

impl ConstructorCapturePrelude {
    fn schedule(
        statements: &mut Vec<KotlinStmt>,
        parameters: &BTreeSet<KotlinIdentifier>,
        final_fields: &BTreeSet<KotlinIdentifier>,
    ) {
        let Some(invocation) = statements
            .iter()
            .position(|statement| matches!(statement, KotlinStmt::ConstructorInvocation { .. }))
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
        statement: &KotlinStmt,
        parameters: &BTreeSet<KotlinIdentifier>,
        final_fields: &BTreeSet<KotlinIdentifier>,
    ) -> bool {
        matches!(
            statement,
            KotlinStmt::Assign {
                target: KotlinExpr::Field { owner, name: field },
                value,
                ..
            } if matches!(owner.as_ref(), KotlinExpr::This)
                && final_fields.contains(field)
                && match value {
                    KotlinExpr::Name(parameter) => parameters.contains(parameter),
                    KotlinExpr::QualifiedThis(_) => true,
                    _ => false,
                }
        )
    }
}

struct ConstructorEvaluationOrder;

impl ConstructorEvaluationOrder {
    fn recover(statements: &mut Vec<KotlinStmt>) {
        let Some(mut invocation) = statements
            .iter()
            .position(|statement| matches!(statement, KotlinStmt::ConstructorInvocation { .. }))
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
                    binder.rewrite_statement(std::mem::replace(candidate, KotlinStmt::Empty));
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
    input: KotlinExpr,
    expression: KotlinExpr,
}

impl IdentityEvaluation {
    fn analyze(statement: &KotlinStmt) -> Option<Self> {
        if let KotlinStmt::Expression(check) = statement {
            let check = Self::transparent(check);
            let KotlinExpr::JvmIntrinsic {
                kind: crate::language::kotlin::KotlinJvmIntrinsic::ReceiverNullCheck,
                expression,
            } = check
            else {
                return Self::objects_require_non_null(statement);
            };
            let KotlinExpr::Call {
                receiver: Some(receiver),
                args,
                ..
            } = expression.as_ref()
            else {
                return None;
            };
            if !args.is_empty() {
                return None;
            }
            let input = receiver.as_ref().clone();
            return Some(Self {
                expression: KotlinExpr::NonNullAssertion(Box::new(input.clone())),
                input,
            });
        }
        Self::objects_require_non_null(statement)
    }

    fn transparent(expression: &KotlinExpr) -> &KotlinExpr {
        match expression {
            KotlinExpr::SmartCast(value) => Self::transparent(value),
            expression => expression,
        }
    }

    fn objects_require_non_null(statement: &KotlinStmt) -> Option<Self> {
        let KotlinStmt::Expression(
            expression @ KotlinExpr::Call {
                receiver: None,
                owner: Some(KotlinType::Class(owner)),
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
            .is_some_and(|component| component == &KotlinIdentifier::from_dex("Objects"));
        (is_objects && method == &KotlinIdentifier::from_dex("requireNonNull")).then(|| Self {
            input: input.clone(),
            expression: expression.clone(),
        })
    }
}

struct BoundReceiverBinder<'a> {
    input: &'a KotlinExpr,
    evaluation: &'a KotlinExpr,
    replaced: bool,
}

impl BoundReceiverBinder<'_> {
    fn bind(&self, expression: KotlinExpr) -> Option<KotlinExpr> {
        if &expression == self.input {
            return Some(self.evaluation.clone());
        }
        let KotlinExpr::Cast { ty, value } = expression else {
            return None;
        };
        Some(KotlinExpr::Cast {
            ty,
            value: Box::new(self.bind(*value)?),
        })
    }
}

impl KotlinAstRewriter for BoundReceiverBinder<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if self.replaced {
            return expression;
        }
        if let Some(bound) = self.bind(expression.clone()) {
            self.replaced = true;
            return bound;
        }
        match expression {
            KotlinExpr::MethodReference { receiver, method } => {
                let original = *receiver;
                let Some(receiver) = self.bind(original.clone()) else {
                    return KotlinExpr::MethodReference {
                        receiver: Box::new(original),
                        method,
                    };
                };
                self.replaced = true;
                KotlinExpr::MethodReference {
                    receiver: Box::new(receiver),
                    method,
                }
            }
            KotlinExpr::New {
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
                KotlinExpr::New {
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
    order: Vec<KotlinIdentifier>,
    values: BTreeMap<KotlinIdentifier, KotlinExpr>,
    dependencies: BTreeMap<KotlinIdentifier, BTreeSet<KotlinIdentifier>>,
}

impl ConstructorBindings {
    fn analyze(statements: &[KotlinStmt]) -> Option<Self> {
        let mut dataflow = ConstructorDataflow::default();
        dataflow.evaluate(statements)?;
        dataflow.finalize_arrays()?;
        Some(Self {
            order: dataflow.order,
            values: dataflow.values,
            dependencies: dataflow.dependencies,
        })
    }

    fn can_schedule(&self, args: &[KotlinExpr]) -> bool {
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
                BTreeMap::<KotlinIdentifier, Vec<usize>>::new(),
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
        name: &KotlinIdentifier,
        direct: &BTreeMap<KotlinIdentifier, Vec<usize>>,
        visiting: &mut BTreeSet<KotlinIdentifier>,
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

    fn stable(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::Name(_)
            | KotlinExpr::Literal(_)
            | KotlinExpr::ClassLiteral(_) => true,
            KotlinExpr::Cast { value, .. } => Self::stable(value),
            _ => false,
        }
    }
}

#[derive(Clone, Default)]
struct ConstructorDataflow {
    order: Vec<KotlinIdentifier>,
    declared: BTreeSet<KotlinIdentifier>,
    values: BTreeMap<KotlinIdentifier, KotlinExpr>,
    dependencies: BTreeMap<KotlinIdentifier, BTreeSet<KotlinIdentifier>>,
    array_writes: BTreeMap<KotlinIdentifier, Vec<KotlinExpr>>,
}

impl ConstructorDataflow {
    fn evaluate(&mut self, statements: &[KotlinStmt]) -> Option<()> {
        for statement in statements {
            self.evaluate_statement(statement)?;
        }
        Some(())
    }

    fn evaluate_statement(&mut self, statement: &KotlinStmt) -> Option<()> {
        match statement {
            KotlinStmt::Variable {
                name,
                value: Some(value),
                ..
            } => self.declare(name, value),
            KotlinStmt::Variable {
                name, value: None, ..
            } => self.declare_uninitialized(name),
            KotlinStmt::Assign {
                target: KotlinExpr::Name(name),
                op: KotlinAssignOp::Assign,
                value,
            } => self.assign(name, value),
            KotlinStmt::Assign {
                target: KotlinExpr::ArrayAccess { array, index },
                op: KotlinAssignOp::Assign,
                value,
            } => self.assign_array_element(array, index, value),
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => self.branch(condition, then_stmt, else_stmt.as_deref()),
            KotlinStmt::Block(statements) => self.evaluate(statements),
            _ => None,
        }
    }

    fn declare(&mut self, name: &KotlinIdentifier, value: &KotlinExpr) -> Option<()> {
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

    fn declare_uninitialized(&mut self, name: &KotlinIdentifier) -> Option<()> {
        self.declared.insert(name.clone()).then_some(())
    }

    fn assign(&mut self, name: &KotlinIdentifier, value: &KotlinExpr) -> Option<()> {
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
        array: &KotlinExpr,
        index: &KotlinExpr,
        value: &KotlinExpr,
    ) -> Option<()> {
        let KotlinExpr::Name(name) = array else {
            return None;
        };
        let KotlinExpr::Literal(KotlinLiteral::Integer(index)) = index else {
            return None;
        };
        let index = usize::try_from(*index).ok()?;
        let KotlinExpr::NewArray {
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
            let KotlinExpr::NewArray {
                dimensions,
                initializer: current,
                ..
            } = self.values.get_mut(&name)?
            else {
                return None;
            };
            let [KotlinExpr::Literal(KotlinLiteral::Integer(length))] = dimensions.as_slice()
            else {
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
        condition: &KotlinExpr,
        then_stmt: &KotlinStmt,
        else_stmt: Option<&KotlinStmt>,
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
                    KotlinExpr::Conditional {
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

    fn binding_dependencies(&self, expression: &KotlinExpr) -> BTreeSet<KotlinIdentifier> {
        ExpressionNames::collect(expression)
            .into_iter()
            .filter(|name| self.values.contains_key(name))
            .collect()
    }

    fn resolve(&self, expression: KotlinExpr) -> KotlinExpr {
        ConstructorSubstitution {
            values: &self.values,
        }
        .rewrite_expression(expression)
    }

    fn record_evaluation(&mut self, name: &KotlinIdentifier, value: &KotlinExpr) {
        if !ConstructorBindings::stable(value) && !self.order.contains(name) {
            self.order.push(name.clone());
        }
    }

    fn extend_order(&mut self, order: &[KotlinIdentifier]) {
        for name in order {
            if !self.order.contains(name) {
                self.order.push(name.clone());
            }
        }
    }
}

struct ReplayableExpression;

impl ReplayableExpression {
    fn check(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::Name(_)
            | KotlinExpr::Literal(_)
            | KotlinExpr::ClassLiteral(_) => true,
            KotlinExpr::Unary { operand, .. }
            | KotlinExpr::Cast { value: operand, .. }
            | KotlinExpr::InstanceOf { value: operand, .. } => Self::check(operand),
            KotlinExpr::Binary { left, right, .. } => Self::check(left) && Self::check(right),
            _ => false,
        }
    }
}

struct ConstructorSubstitution<'a> {
    values: &'a BTreeMap<KotlinIdentifier, KotlinExpr>,
}

impl KotlinAstRewriter for ConstructorSubstitution<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Name(name) => self
                .values
                .get(&name)
                .cloned()
                .unwrap_or(KotlinExpr::Name(name)),
            KotlinExpr::Conditional {
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
    fn reduce(condition: KotlinExpr, when_true: KotlinExpr, when_false: KotlinExpr) -> KotlinExpr {
        let when_true = Self::under_assumption(&condition, true, when_true);
        let when_false = Self::under_assumption(&condition, false, when_false);
        if when_true == when_false {
            return when_true;
        }
        KotlinExpr::Conditional {
            condition: Box::new(condition),
            when_true: Box::new(when_true),
            when_false: Box::new(when_false),
        }
    }

    fn under_assumption(condition: &KotlinExpr, truth: bool, expression: KotlinExpr) -> KotlinExpr {
        let KotlinExpr::Conditional {
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
            return KotlinExpr::Conditional {
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
            PredicateRelation::Independent => KotlinExpr::Conditional {
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
    fn between(left: &KotlinExpr, right: &KotlinExpr) -> Self {
        if left == right {
            return Self::Equivalent;
        }
        if matches!(
            (left, right),
            (
                KotlinExpr::Unary {
                    op: KotlinUnaryOp::LogicalNot,
                    operand
                },
                other
            ) | (
                other,
                KotlinExpr::Unary {
                    op: KotlinUnaryOp::LogicalNot,
                    operand
                }
            ) if operand.as_ref() == other
        ) {
            return Self::Complement;
        }
        let (
            KotlinExpr::Binary {
                left: left_operand,
                op: left_operator,
                right: left_right_operand,
            },
            KotlinExpr::Binary {
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
            (KotlinBinaryOp::Equal, KotlinBinaryOp::NotEqual)
                | (KotlinBinaryOp::NotEqual, KotlinBinaryOp::Equal)
                | (
                    KotlinBinaryOp::ReferentialEqual,
                    KotlinBinaryOp::ReferentialNotEqual
                )
                | (
                    KotlinBinaryOp::ReferentialNotEqual,
                    KotlinBinaryOp::ReferentialEqual
                )
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
    fn collect(expression: &KotlinExpr) -> BTreeSet<KotlinIdentifier> {
        let mut names = BTreeSet::new();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                KotlinExpr::Name(name) => {
                    names.insert(name.clone());
                }
                KotlinExpr::This
                | KotlinExpr::QualifiedThis(_)
                | KotlinExpr::Super
                | KotlinExpr::Literal(_)
                | KotlinExpr::ClassLiteral(_)
                | KotlinExpr::ObjectReference(_)
                | KotlinExpr::StaticField { .. } => {}
                KotlinExpr::SmartCast(value)
                | KotlinExpr::NonNullAssertion(value)
                | KotlinExpr::JvmIntrinsic {
                    expression: value, ..
                } => pending.push(value),
                KotlinExpr::Field { owner, .. } => pending.push(owner),
                KotlinExpr::ArrayAccess { array, index } => {
                    pending.push(index);
                    pending.push(array);
                }
                KotlinExpr::Call { receiver, args, .. } => {
                    pending.extend(args.iter().rev());
                    pending.extend(receiver.iter().map(|value| value.as_ref()));
                }
                KotlinExpr::MethodReference { receiver, .. } => pending.push(receiver),
                KotlinExpr::Lambda { body, .. } => pending.push(body),
                KotlinExpr::BlockLambda { .. } => {}
                KotlinExpr::New {
                    enclosing, args, ..
                } => {
                    pending.extend(args.iter().rev());
                    pending.extend(enclosing.iter().map(|value| value.as_ref()));
                }
                KotlinExpr::NewArray {
                    dimensions,
                    initializer,
                    ..
                } => {
                    pending.extend(initializer.iter().rev());
                    pending.extend(dimensions.iter().rev());
                }
                KotlinExpr::Unary { operand, .. }
                | KotlinExpr::Cast { value: operand, .. }
                | KotlinExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                KotlinExpr::Update { target, .. } => pending.push(target),
                KotlinExpr::Binary { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                KotlinExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.push(when_false);
                    pending.push(when_true);
                    pending.push(condition);
                }
                KotlinExpr::Assignment { target, value, .. } => {
                    pending.push(value);
                    pending.push(target);
                }
            }
        }
        names
    }
}
