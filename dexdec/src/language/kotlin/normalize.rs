use std::collections::{BTreeMap, BTreeSet};

use super::{
    KotlinAstRewriter, KotlinBinaryOp, KotlinCatch, KotlinExpr, KotlinIdentifier, KotlinMethodBody,
    KotlinStmt, KotlinSwitchCase, KotlinType,
};

pub trait KotlinAstTransform {
    type Error;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error>;
}

#[derive(Debug, Default)]
pub struct KotlinAstNormalizer;

/// Re-expresses DEX `return-void` exits from a class initializer as structured
/// Kotlin control flow. Kotlin forbids explicit returns in initializer blocks.
#[derive(Debug, Default)]
pub struct KotlinInitializerExitLowering;

/// Introduces Kotlin-local mutable storage for source parameters written by
/// the recovered method body. Kotlin parameters are immutable by definition.
#[derive(Debug)]
pub struct KotlinMutableParameterLowering {
    parameters: Vec<(KotlinIdentifier, KotlinType)>,
}

/// Rebinds the JVM parameter that carries an extension receiver to Kotlin's
/// implicit `this`. If the parameter was assigned, mutable-parameter lowering
/// has already introduced a local copy; only that copy's initializer is
/// rebound and subsequent uses keep referring to the local.
#[derive(Debug)]
pub struct KotlinExtensionReceiverLowering {
    parameter: KotlinIdentifier,
    nullable: bool,
}

pub struct KotlinNameUseAnalysis;

/// Applies Kotlin smart casts from path-sensitive nullness facts.
///
/// Only immutable parameters are candidates. Facts flow over short-circuit
/// boolean edges and structured branch edges, matching Kotlin's stability
/// rules without changing JVM null-dereference semantics.
#[derive(Debug)]
pub struct KotlinSmartCastLowering {
    parameters: BTreeSet<KotlinIdentifier>,
}

#[derive(Debug, Default)]
pub struct KotlinLocalBindingAnalysis;

#[derive(Debug, Default)]
pub struct KotlinNullabilityFacts {
    non_null_locals: BTreeSet<KotlinIdentifier>,
}

impl KotlinSmartCastLowering {
    pub fn new(parameters: impl IntoIterator<Item = KotlinIdentifier>) -> Self {
        Self {
            parameters: parameters.into_iter().collect(),
        }
    }
}

impl KotlinMutableParameterLowering {
    pub fn new(parameters: impl IntoIterator<Item = (KotlinIdentifier, KotlinType)>) -> Self {
        Self {
            parameters: parameters.into_iter().collect(),
        }
    }
}

impl KotlinExtensionReceiverLowering {
    pub fn new(parameter: KotlinIdentifier, nullable: bool) -> Self {
        Self {
            parameter,
            nullable,
        }
    }
}

impl KotlinNameUseAnalysis {
    pub fn contains(body: &KotlinMethodBody, name: &KotlinIdentifier) -> bool {
        let mut query = KotlinNameUseQuery {
            name,
            referenced: false,
        };
        query.rewrite_statement(body.root.clone());
        query.referenced
    }
}

struct KotlinNameUseQuery<'a> {
    name: &'a KotlinIdentifier,
    referenced: bool,
}

impl KotlinAstRewriter for KotlinNameUseQuery<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if matches!(&expression, KotlinExpr::Name(name) if name == self.name) {
            self.referenced = true;
        }
        expression
    }
}

impl KotlinAstTransform for KotlinExtensionReceiverLowering {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        if let KotlinStmt::Block(statements) = &mut body.root {
            if let Some(KotlinStmt::Variable { name, value, .. }) = statements.first_mut() {
                if name == &self.parameter {
                    match value {
                        Some(KotlinExpr::Name(source)) if source == &self.parameter => {
                            *value = Some(KotlinExpr::This);
                            return Ok(true);
                        }
                        Some(KotlinExpr::NonNullAssertion(source)) if matches!(source.as_ref(), KotlinExpr::Name(name) if name == &self.parameter) =>
                        {
                            **source = KotlinExpr::This;
                            if !self.nullable {
                                *value = Some(KotlinExpr::This);
                            }
                            return Ok(true);
                        }
                        _ => {}
                    }
                }
            }
        }
        let before = body.root.clone();
        let mut rewriter = ExtensionReceiverReferences {
            parameter: &self.parameter,
            nullable: self.nullable,
        };
        rewriter.rewrite_body(body);
        Ok(body.root != before)
    }
}

struct ExtensionReceiverReferences<'a> {
    parameter: &'a KotlinIdentifier,
    nullable: bool,
}

impl KotlinAstRewriter for ExtensionReceiverReferences<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Name(name) if &name == self.parameter => KotlinExpr::This,
            KotlinExpr::NonNullAssertion(value)
                if !self.nullable && matches!(value.as_ref(), KotlinExpr::This) =>
            {
                KotlinExpr::This
            }
            expression => expression,
        }
    }
}

impl KotlinAstTransform for KotlinMutableParameterLowering {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        if self.parameters.is_empty() {
            return Ok(false);
        }
        let mut writes = AssignmentTargetCollector::default();
        body.root = writes.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
        let shadows = self
            .parameters
            .iter()
            .filter(|(name, _)| writes.names.contains(name))
            .map(|(name, ty)| KotlinStmt::Variable {
                binding: Default::default(),
                ty: ty.clone(),
                name: name.clone(),
                value: Some(KotlinExpr::Name(name.clone())),
            })
            .collect::<Vec<_>>();
        if shadows.is_empty() {
            return Ok(false);
        }
        let KotlinStmt::Block(statements) = &mut body.root else {
            return Err(super::KotlinStructuralError::MalformedWorkStack);
        };
        let insertion = usize::from(matches!(
            statements.first(),
            Some(KotlinStmt::ConstructorInvocation { .. })
        ));
        statements.splice(insertion..insertion, shadows);
        Ok(true)
    }
}

impl KotlinAstTransform for KotlinSmartCastLowering {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        let mut locals = LocalNameCollector::default();
        locals.rewrite_statement(body.root.clone());
        let mut writes = AssignmentTargetCollector::default();
        writes.rewrite_statement(body.root.clone());
        let mut stable = self.parameters.clone();
        stable.extend(locals.names);
        stable.retain(|name| !writes.names.contains(name));
        let mut lowering = SmartCastFlow::new(&stable);
        body.root = lowering.statement(
            std::mem::replace(&mut body.root, KotlinStmt::Empty),
            &SmartCastFacts::default(),
        );
        Ok(lowering.changed)
    }
}

struct SmartCastFlow<'a> {
    candidates: &'a BTreeSet<KotlinIdentifier>,
    changed: bool,
}

#[derive(Clone, Debug, Default)]
struct SmartCastFacts {
    non_null: BTreeSet<KotlinIdentifier>,
    refined_types: BTreeMap<KotlinIdentifier, Vec<KotlinType>>,
}

impl<'a> SmartCastFlow<'a> {
    fn new(candidates: &'a BTreeSet<KotlinIdentifier>) -> Self {
        Self {
            candidates,
            changed: false,
        }
    }

    fn statement(&mut self, statement: KotlinStmt, facts: &SmartCastFacts) -> KotlinStmt {
        match statement {
            KotlinStmt::Block(statements) => {
                let mut current = facts.clone();
                let mut lowered = Vec::with_capacity(statements.len());
                for statement in statements {
                    let continuation = Self::continuation_facts(&statement, &current);
                    lowered.push(self.statement(statement, &current));
                    current = continuation;
                }
                KotlinStmt::Block(lowered)
            }
            KotlinStmt::Labeled { label, body } => KotlinStmt::Labeled {
                label,
                body: Box::new(self.statement(*body, facts)),
            },
            KotlinStmt::Variable {
                binding,
                ty,
                name,
                value,
            } => KotlinStmt::Variable {
                binding,
                ty,
                name,
                value: value.map(|value| self.expression(value, facts)),
            },
            KotlinStmt::Expression(expression) => {
                KotlinStmt::Expression(self.expression(expression, facts))
            }
            KotlinStmt::ConstructorInvocation { target, args } => {
                KotlinStmt::ConstructorInvocation {
                    target,
                    args: args
                        .into_iter()
                        .map(|argument| self.expression(argument, facts))
                        .collect(),
                }
            }
            KotlinStmt::Assign { target, op, value } => KotlinStmt::Assign {
                target: self.lvalue(target, facts),
                op,
                value: self.expression(value, facts),
            },
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => {
                let required = Self::required_by_expression(&condition);
                let mut then_facts = Self::branch_facts(&condition, true, facts);
                then_facts.non_null.extend(required.iter().cloned());
                let mut else_facts = Self::branch_facts(&condition, false, facts);
                else_facts.non_null.extend(required);
                KotlinStmt::If {
                    condition: self.expression(condition, facts),
                    then_stmt: Box::new(self.statement(*then_stmt, &then_facts)),
                    else_stmt: else_stmt
                        .map(|statement| Box::new(self.statement(*statement, &else_facts))),
                }
            }
            KotlinStmt::While {
                label,
                condition,
                body,
            } => {
                let mut body_facts = Self::branch_facts(&condition, true, facts);
                body_facts
                    .non_null
                    .extend(Self::required_by_expression(&condition));
                KotlinStmt::While {
                    label,
                    condition: self.expression(condition, facts),
                    body: Box::new(self.statement(*body, &body_facts)),
                }
            }
            KotlinStmt::DoWhile {
                label,
                body,
                condition,
            } => KotlinStmt::DoWhile {
                label,
                body: Box::new(self.statement(*body, facts)),
                condition: self.expression(condition, facts),
            },
            KotlinStmt::For {
                label,
                init,
                condition,
                update,
                body,
            } => {
                let body_facts = condition
                    .as_ref()
                    .map(|condition| {
                        let mut body_facts = Self::branch_facts(condition, true, facts);
                        body_facts
                            .non_null
                            .extend(Self::required_by_expression(condition));
                        body_facts
                    })
                    .unwrap_or_else(|| facts.clone());
                KotlinStmt::For {
                    label,
                    init: init
                        .into_iter()
                        .map(|statement| self.statement(statement, facts))
                        .collect(),
                    condition: condition.map(|condition| self.expression(condition, facts)),
                    update: update
                        .into_iter()
                        .map(|expression| self.expression(expression, &body_facts))
                        .collect(),
                    body: Box::new(self.statement(*body, &body_facts)),
                }
            }
            KotlinStmt::ForEach {
                label,
                ty,
                variable,
                iterable,
                body,
            } => KotlinStmt::ForEach {
                label,
                ty,
                variable,
                iterable: self.expression(iterable, facts),
                body: Box::new(self.statement(*body, facts)),
            },
            KotlinStmt::Switch {
                label,
                selector,
                cases,
            } => KotlinStmt::Switch {
                label,
                selector: self.expression(selector, facts),
                cases: cases
                    .into_iter()
                    .map(|case| KotlinSwitchCase {
                        labels: case
                            .labels
                            .into_iter()
                            .map(|label| self.expression(label, facts))
                            .collect(),
                        body: case
                            .body
                            .into_iter()
                            .map(|statement| self.statement(statement, facts))
                            .collect(),
                        ..case
                    })
                    .collect(),
            },
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => KotlinStmt::Try {
                body: Box::new(self.statement(*body, facts)),
                catches: catches
                    .into_iter()
                    .map(|catch| {
                        let mut catch_facts = facts.clone();
                        catch_facts.non_null.insert(catch.variable.clone());
                        KotlinCatch {
                            body: self.statement(catch.body, &catch_facts),
                            ..catch
                        }
                    })
                    .collect(),
                finally: finally.map(|body| Box::new(self.statement(*body, facts))),
            },
            KotlinStmt::Synchronized { lock, body } => KotlinStmt::Synchronized {
                lock: self.expression(lock, facts),
                body: Box::new(self.statement(*body, facts)),
            },
            KotlinStmt::Return(value) => {
                KotlinStmt::Return(value.map(|value| self.expression(value, facts)))
            }
            KotlinStmt::Throw(value) => KotlinStmt::Throw(self.expression(value, facts)),
            leaf @ (KotlinStmt::Empty | KotlinStmt::Break(_) | KotlinStmt::Continue(_)) => leaf,
        }
    }

    fn expression(&mut self, expression: KotlinExpr, facts: &SmartCastFacts) -> KotlinExpr {
        match expression {
            KotlinExpr::Field { owner, name } => KotlinExpr::Field {
                owner: Box::new(self.receiver(*owner, facts)),
                name,
            },
            KotlinExpr::ArrayAccess { array, index } => {
                let index_facts =
                    Self::with_requirements(facts, Self::receiver_requirements(&array));
                KotlinExpr::ArrayAccess {
                    array: Box::new(self.receiver(*array, facts)),
                    index: Box::new(self.expression(*index, &index_facts)),
                }
            }
            KotlinExpr::Call {
                receiver,
                owner,
                type_arguments,
                method,
                args,
            } => {
                let mut argument_facts = facts.clone();
                let receiver = receiver.map(|receiver| {
                    argument_facts
                        .non_null
                        .extend(Self::receiver_requirements(&receiver));
                    Box::new(self.receiver(*receiver, facts))
                });
                KotlinExpr::Call {
                    receiver,
                    owner,
                    type_arguments,
                    method,
                    args: args.map_values(|expression| {
                        let required = Self::required_by_expression(&expression);
                        let expression = self.expression(expression, &argument_facts);
                        argument_facts.non_null.extend(required);
                        expression
                    }),
                }
            }
            KotlinExpr::MethodReference { receiver, method } => KotlinExpr::MethodReference {
                receiver: Box::new(self.receiver(*receiver, facts)),
                method,
            },
            KotlinExpr::Lambda { parameters, body } => {
                let nested = Self::without_bound_names(facts, &parameters);
                KotlinExpr::Lambda {
                    parameters,
                    body: Box::new(self.expression(*body, &nested)),
                }
            }
            KotlinExpr::BlockLambda { parameters, body } => {
                let nested = Self::without_bound_names(facts, &parameters);
                KotlinExpr::BlockLambda {
                    parameters,
                    body: Box::new(self.statement(*body, &nested)),
                }
            }
            KotlinExpr::New {
                enclosing,
                ty,
                target_type,
                args,
                anonymous_body,
            } => {
                let mut argument_facts = facts.clone();
                let enclosing = enclosing.map(|owner| {
                    argument_facts
                        .non_null
                        .extend(Self::receiver_requirements(&owner));
                    Box::new(self.receiver(*owner, facts))
                });
                KotlinExpr::New {
                    enclosing,
                    ty,
                    target_type,
                    args: self.expressions_in_order(args, argument_facts),
                    anonymous_body,
                }
            }
            KotlinExpr::NewArray {
                element_type,
                dimensions,
                initializer,
            } => {
                let mut current = facts.clone();
                let dimensions = self.expressions_in_order_from(dimensions, &mut current);
                let initializer = self.expressions_in_order_from(initializer, &mut current);
                KotlinExpr::NewArray {
                    element_type,
                    dimensions,
                    initializer,
                }
            }
            KotlinExpr::Unary { op, operand } => KotlinExpr::Unary {
                op,
                operand: Box::new(self.expression(*operand, facts)),
            },
            KotlinExpr::Update { op, target, prefix } => KotlinExpr::Update {
                op,
                target: Box::new(self.lvalue(*target, facts)),
                prefix,
            },
            KotlinExpr::Binary { left, op, right } => {
                let mut right_facts = match op {
                    KotlinBinaryOp::LogicalAnd => Self::branch_facts(&left, true, facts),
                    KotlinBinaryOp::LogicalOr => Self::branch_facts(&left, false, facts),
                    _ => Self::with_requirements(facts, Self::required_by_expression(&left)),
                };
                right_facts
                    .non_null
                    .extend(Self::required_by_expression(&left));
                let left = self.expression(*left, facts);
                let right = self.expression(*right, &right_facts);
                if let Some(value) = Self::known_null_comparison(&left, op, &right, facts) {
                    KotlinExpr::Literal(super::KotlinLiteral::Boolean(value))
                } else if let Some(value) = fold_boolean_binary(&left, op, &right) {
                    value
                } else {
                    KotlinExpr::Binary {
                        left: Box::new(left),
                        op,
                        right: Box::new(right),
                    }
                }
            }
            KotlinExpr::Cast { ty, value } => {
                if Self::direct_name(&value).is_some_and(|name| {
                    facts
                        .refined_types
                        .get(name)
                        .is_some_and(|types| types.contains(&ty))
                }) {
                    self.changed = true;
                    self.expression(*value, facts)
                } else {
                    let value = self.receiver(*value, facts);
                    let value = match value {
                        KotlinExpr::Cast {
                            ty: inner_type,
                            value,
                        } if Self::same_runtime_type(&inner_type, &ty) => {
                            self.changed = true;
                            *value
                        }
                        value => value,
                    };
                    KotlinExpr::Cast {
                        ty,
                        value: Box::new(value),
                    }
                }
            }
            KotlinExpr::InstanceOf { value, ty } => KotlinExpr::InstanceOf {
                value: Box::new(self.expression(*value, facts)),
                ty,
            },
            KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => {
                let required = Self::required_by_expression(&condition);
                let mut true_facts = Self::branch_facts(&condition, true, facts);
                true_facts.non_null.extend(required.iter().cloned());
                let mut false_facts = Self::branch_facts(&condition, false, facts);
                false_facts.non_null.extend(required);
                KotlinExpr::Conditional {
                    condition: Box::new(self.expression(*condition, facts)),
                    when_true: Box::new(self.expression(*when_true, &true_facts)),
                    when_false: Box::new(self.expression(*when_false, &false_facts)),
                }
            }
            KotlinExpr::Assignment { target, op, value } => {
                let value_facts =
                    Self::with_requirements(facts, Self::required_by_expression(&target));
                KotlinExpr::Assignment {
                    target: Box::new(self.lvalue(*target, facts)),
                    op,
                    value: Box::new(self.expression(*value, &value_facts)),
                }
            }
            KotlinExpr::SmartCast(value) => {
                KotlinExpr::SmartCast(Box::new(self.expression(*value, facts)))
            }
            KotlinExpr::NonNullAssertion(value) => {
                let value = self.expression(*value, facts);
                if definitely_non_null_with(&value, &facts.non_null) {
                    value
                } else {
                    KotlinExpr::NonNullAssertion(Box::new(value))
                }
            }
            KotlinExpr::Name(name)
                if self.candidates.contains(&name) && facts.non_null.contains(&name) =>
            {
                self.changed = true;
                KotlinExpr::SmartCast(Box::new(KotlinExpr::Name(name)))
            }
            leaf => leaf,
        }
    }

    fn lvalue(&mut self, expression: KotlinExpr, facts: &SmartCastFacts) -> KotlinExpr {
        match expression {
            KotlinExpr::Field { owner, name } => KotlinExpr::Field {
                owner: Box::new(self.receiver(*owner, facts)),
                name,
            },
            KotlinExpr::ArrayAccess { array, index } => KotlinExpr::ArrayAccess {
                array: Box::new(self.receiver(*array, facts)),
                index: Box::new(self.expression(*index, facts)),
            },
            KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
                self.lvalue(*value, facts)
            }
            expression => expression,
        }
    }

    fn with_requirements(
        facts: &SmartCastFacts,
        requirements: BTreeSet<KotlinIdentifier>,
    ) -> SmartCastFacts {
        let mut result = facts.clone();
        result.non_null.extend(requirements);
        result
    }

    fn expressions_in_order(
        &mut self,
        expressions: Vec<KotlinExpr>,
        mut facts: SmartCastFacts,
    ) -> Vec<KotlinExpr> {
        self.expressions_in_order_from(expressions, &mut facts)
    }

    fn expressions_in_order_from(
        &mut self,
        expressions: Vec<KotlinExpr>,
        facts: &mut SmartCastFacts,
    ) -> Vec<KotlinExpr> {
        expressions
            .into_iter()
            .map(|expression| {
                let required = Self::required_by_expression(&expression);
                let expression = self.expression(expression, facts);
                facts.non_null.extend(required);
                expression
            })
            .collect()
    }

    fn receiver(&mut self, expression: KotlinExpr, facts: &SmartCastFacts) -> KotlinExpr {
        let expression = self.expression(expression, facts);
        if let KotlinExpr::Name(name) = &expression {
            if self.candidates.contains(name) && facts.non_null.contains(name) {
                self.changed = true;
                return KotlinExpr::SmartCast(Box::new(expression));
            }
        }
        expression
    }

    fn branch_facts(
        condition: &KotlinExpr,
        truth: bool,
        incoming: &SmartCastFacts,
    ) -> SmartCastFacts {
        let mut facts = incoming.clone();
        facts
            .non_null
            .extend(Self::implied_non_null(condition, truth));
        Self::merge_refinements(
            &mut facts.refined_types,
            Self::implied_refined_types(condition, truth),
        );
        facts
    }

    fn continuation_facts(statement: &KotlinStmt, incoming: &SmartCastFacts) -> SmartCastFacts {
        let mut facts = incoming.clone();
        if let KotlinStmt::If {
            condition,
            then_stmt,
            else_stmt,
        } = statement
        {
            let then_completes = Self::completes_normally(then_stmt);
            let else_completes = else_stmt
                .as_deref()
                .map(Self::completes_normally)
                .unwrap_or(true);
            facts = match (then_completes, else_completes) {
                (false, true) => Self::branch_facts(condition, false, incoming),
                (true, false) => Self::branch_facts(condition, true, incoming),
                _ => incoming.clone(),
            };
        }
        facts
            .non_null
            .extend(Self::required_by_statement(statement));
        match statement {
            KotlinStmt::Variable { name, value, .. } => {
                facts.non_null.remove(name);
                facts.refined_types.remove(name);
                if value
                    .as_ref()
                    .is_some_and(KotlinNullabilityFacts::expression_definitely_non_null)
                {
                    facts.non_null.insert(name.clone());
                }
            }
            KotlinStmt::Assign {
                target: KotlinExpr::Name(name),
                op: super::KotlinAssignOp::Assign,
                value,
            } => {
                facts.non_null.remove(name);
                facts.refined_types.remove(name);
                if definitely_non_null_with(value, &facts.non_null) {
                    facts.non_null.insert(name.clone());
                }
            }
            _ => {}
        }
        facts
    }

    fn required_by_statement(statement: &KotlinStmt) -> BTreeSet<KotlinIdentifier> {
        match statement {
            KotlinStmt::Variable {
                value: Some(value), ..
            }
            | KotlinStmt::Expression(value)
            | KotlinStmt::Return(Some(value))
            | KotlinStmt::Throw(value) => Self::required_by_expression(value),
            KotlinStmt::ConstructorInvocation { args, .. } => {
                Self::required_by_expressions(args.iter())
            }
            KotlinStmt::Assign { target, value, .. } => Self::union(
                Self::required_by_expression(target),
                Self::required_by_expression(value),
            ),
            KotlinStmt::If { condition, .. }
            | KotlinStmt::While { condition, .. }
            | KotlinStmt::DoWhile { condition, .. } => Self::required_by_expression(condition),
            KotlinStmt::For {
                init, condition, ..
            } => {
                let mut required = init.iter().fold(BTreeSet::new(), |required, statement| {
                    Self::union(required, Self::required_by_statement(statement))
                });
                if let Some(condition) = condition {
                    required.extend(Self::required_by_expression(condition));
                }
                required
            }
            KotlinStmt::ForEach { iterable, .. }
            | KotlinStmt::Switch {
                selector: iterable, ..
            }
            | KotlinStmt::Synchronized { lock: iterable, .. } => {
                Self::required_by_expression(iterable)
            }
            KotlinStmt::Empty
            | KotlinStmt::Block(_)
            | KotlinStmt::Labeled { .. }
            | KotlinStmt::Variable { value: None, .. }
            | KotlinStmt::Try { .. }
            | KotlinStmt::Return(None)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => BTreeSet::new(),
        }
    }

    fn required_by_expressions<'b>(
        expressions: impl IntoIterator<Item = &'b KotlinExpr>,
    ) -> BTreeSet<KotlinIdentifier> {
        expressions
            .into_iter()
            .fold(BTreeSet::new(), |required, expression| {
                Self::union(required, Self::required_by_expression(expression))
            })
    }

    fn required_by_expression(expression: &KotlinExpr) -> BTreeSet<KotlinIdentifier> {
        match expression {
            KotlinExpr::Field { owner, .. }
            | KotlinExpr::MethodReference {
                receiver: owner, ..
            } => Self::receiver_requirements(owner),
            KotlinExpr::ArrayAccess { array, index } => Self::union(
                Self::receiver_requirements(array),
                Self::required_by_expression(index),
            ),
            KotlinExpr::Call { receiver, args, .. } => {
                let mut required = receiver
                    .as_deref()
                    .map(Self::receiver_requirements)
                    .unwrap_or_default();
                required.extend(Self::required_by_expressions(args));
                required
            }
            KotlinExpr::New {
                enclosing, args, ..
            } => {
                let mut required = enclosing
                    .as_deref()
                    .map(Self::receiver_requirements)
                    .unwrap_or_default();
                required.extend(Self::required_by_expressions(args));
                required
            }
            KotlinExpr::NewArray {
                dimensions,
                initializer,
                ..
            } => Self::union(
                Self::required_by_expressions(dimensions),
                Self::required_by_expressions(initializer),
            ),
            KotlinExpr::Unary { operand, .. }
            | KotlinExpr::Update {
                target: operand, ..
            }
            | KotlinExpr::Cast { value: operand, .. }
            | KotlinExpr::InstanceOf { value: operand, .. }
            | KotlinExpr::SmartCast(operand)
            | KotlinExpr::JvmIntrinsic {
                expression: operand,
                ..
            } => Self::required_by_expression(operand),
            KotlinExpr::NonNullAssertion(operand) => Self::union(
                Self::receiver_requirements(operand),
                Self::required_by_expression(operand),
            ),
            KotlinExpr::Binary { left, op, right } => {
                let left_required = Self::required_by_expression(left);
                if matches!(op, KotlinBinaryOp::LogicalAnd | KotlinBinaryOp::LogicalOr) {
                    left_required
                } else {
                    Self::union(left_required, Self::required_by_expression(right))
                }
            }
            KotlinExpr::Conditional { condition, .. } => Self::required_by_expression(condition),
            KotlinExpr::Assignment { target, value, .. } => Self::union(
                Self::required_by_expression(target),
                Self::required_by_expression(value),
            ),
            KotlinExpr::Lambda { .. }
            | KotlinExpr::BlockLambda { .. }
            | KotlinExpr::This
            | KotlinExpr::QualifiedThis(_)
            | KotlinExpr::Super
            | KotlinExpr::Name(_)
            | KotlinExpr::Literal(_)
            | KotlinExpr::ClassLiteral(_)
            | KotlinExpr::ObjectReference(_)
            | KotlinExpr::StaticField { .. } => BTreeSet::new(),
        }
    }

    fn receiver_requirements(receiver: &KotlinExpr) -> BTreeSet<KotlinIdentifier> {
        let mut required = Self::required_by_expression(receiver);
        if let Some(name) = Self::direct_name(receiver) {
            required.insert(name.clone());
        }
        required
    }

    fn direct_name(expression: &KotlinExpr) -> Option<&KotlinIdentifier> {
        match expression {
            KotlinExpr::Name(name) => Some(name),
            KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) => {
                Self::direct_name(value)
            }
            _ => None,
        }
    }

    fn same_runtime_type(left: &KotlinType, right: &KotlinType) -> bool {
        match (left, right) {
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) => left == right,
            (KotlinType::Class(left), KotlinType::Class(right)) => left.name() == right.name(),
            (KotlinType::Variable(left), KotlinType::Variable(right)) => left == right,
            (KotlinType::Array(left), KotlinType::Array(right)) => {
                Self::same_runtime_type(left, right)
            }
            _ => false,
        }
    }

    fn completes_normally(statement: &KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => false,
            KotlinStmt::Block(statements) => statements.iter().all(Self::completes_normally),
            KotlinStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                Self::completes_normally(then_stmt)
                    || else_stmt
                        .as_deref()
                        .map(Self::completes_normally)
                        .unwrap_or(true)
            }
            KotlinStmt::Try { finally, .. } => finally
                .as_deref()
                .map(Self::completes_normally)
                .unwrap_or(true),
            KotlinStmt::Synchronized { body, .. } => Self::completes_normally(body),
            KotlinStmt::Empty
            | KotlinStmt::Labeled { .. }
            | KotlinStmt::Variable { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::Assign { .. }
            | KotlinStmt::While { .. }
            | KotlinStmt::DoWhile { .. }
            | KotlinStmt::For { .. }
            | KotlinStmt::ForEach { .. }
            | KotlinStmt::Switch { .. } => true,
        }
    }

    fn implied_non_null(expression: &KotlinExpr, truth: bool) -> BTreeSet<KotlinIdentifier> {
        match expression {
            KotlinExpr::Unary {
                op: super::KotlinUnaryOp::LogicalNot,
                operand,
            } => Self::implied_non_null(operand, !truth),
            KotlinExpr::Binary { left, op, right } => match op {
                KotlinBinaryOp::LogicalAnd if truth => Self::union(
                    Self::implied_non_null(left, true),
                    Self::implied_non_null(right, true),
                ),
                KotlinBinaryOp::LogicalOr if !truth => Self::union(
                    Self::implied_non_null(left, false),
                    Self::implied_non_null(right, false),
                ),
                KotlinBinaryOp::LogicalAnd => Self::intersection(
                    Self::implied_non_null(left, false),
                    Self::implied_non_null(right, false),
                ),
                KotlinBinaryOp::LogicalOr => Self::intersection(
                    Self::implied_non_null(left, true),
                    Self::implied_non_null(right, true),
                ),
                KotlinBinaryOp::NotEqual | KotlinBinaryOp::ReferentialNotEqual if truth => {
                    Self::name_compared_with_null(left, right)
                }
                KotlinBinaryOp::Equal | KotlinBinaryOp::ReferentialEqual if !truth => {
                    Self::name_compared_with_null(left, right)
                }
                _ => BTreeSet::new(),
            },
            KotlinExpr::InstanceOf { value, .. } if truth => {
                Self::direct_name(value).cloned().into_iter().collect()
            }
            _ => BTreeSet::new(),
        }
    }

    fn implied_refined_types(
        expression: &KotlinExpr,
        truth: bool,
    ) -> BTreeMap<KotlinIdentifier, Vec<KotlinType>> {
        match expression {
            KotlinExpr::Unary {
                op: super::KotlinUnaryOp::LogicalNot,
                operand,
            } => Self::implied_refined_types(operand, !truth),
            KotlinExpr::Binary { left, op, right } => match op {
                KotlinBinaryOp::LogicalAnd if truth => Self::union_refinements(
                    Self::implied_refined_types(left, true),
                    Self::implied_refined_types(right, true),
                ),
                KotlinBinaryOp::LogicalOr if !truth => Self::union_refinements(
                    Self::implied_refined_types(left, false),
                    Self::implied_refined_types(right, false),
                ),
                KotlinBinaryOp::LogicalAnd => Self::intersection_refinements(
                    Self::implied_refined_types(left, false),
                    Self::implied_refined_types(right, false),
                ),
                KotlinBinaryOp::LogicalOr => Self::intersection_refinements(
                    Self::implied_refined_types(left, true),
                    Self::implied_refined_types(right, true),
                ),
                _ => BTreeMap::new(),
            },
            KotlinExpr::InstanceOf { value, ty } if truth => Self::direct_name(value)
                .map(|name| BTreeMap::from([(name.clone(), vec![ty.clone()])]))
                .unwrap_or_default(),
            _ => BTreeMap::new(),
        }
    }

    fn name_compared_with_null(
        left: &KotlinExpr,
        right: &KotlinExpr,
    ) -> BTreeSet<KotlinIdentifier> {
        let name = match (left, right) {
            (value, KotlinExpr::Literal(super::KotlinLiteral::Null))
            | (KotlinExpr::Literal(super::KotlinLiteral::Null), value) => {
                let Some(name) = Self::direct_name(value) else {
                    return BTreeSet::new();
                };
                name
            }
            _ => return BTreeSet::new(),
        };
        BTreeSet::from([name.clone()])
    }

    fn known_null_comparison(
        left: &KotlinExpr,
        op: KotlinBinaryOp,
        right: &KotlinExpr,
        facts: &SmartCastFacts,
    ) -> Option<bool> {
        let names = Self::name_compared_with_null(left, right);
        if names.len() != 1 || !names.iter().all(|name| facts.non_null.contains(name)) {
            return None;
        }
        match op {
            KotlinBinaryOp::Equal | KotlinBinaryOp::ReferentialEqual => Some(false),
            KotlinBinaryOp::NotEqual | KotlinBinaryOp::ReferentialNotEqual => Some(true),
            _ => None,
        }
    }

    fn union(
        mut left: BTreeSet<KotlinIdentifier>,
        right: BTreeSet<KotlinIdentifier>,
    ) -> BTreeSet<KotlinIdentifier> {
        left.extend(right);
        left
    }

    fn intersection(
        mut left: BTreeSet<KotlinIdentifier>,
        right: BTreeSet<KotlinIdentifier>,
    ) -> BTreeSet<KotlinIdentifier> {
        left.retain(|name| right.contains(name));
        left
    }

    fn merge_refinements(
        target: &mut BTreeMap<KotlinIdentifier, Vec<KotlinType>>,
        source: BTreeMap<KotlinIdentifier, Vec<KotlinType>>,
    ) {
        for (name, types) in source {
            let known = target.entry(name).or_default();
            for ty in types {
                if !known.contains(&ty) {
                    known.push(ty);
                }
            }
        }
    }

    fn union_refinements(
        mut left: BTreeMap<KotlinIdentifier, Vec<KotlinType>>,
        right: BTreeMap<KotlinIdentifier, Vec<KotlinType>>,
    ) -> BTreeMap<KotlinIdentifier, Vec<KotlinType>> {
        Self::merge_refinements(&mut left, right);
        left
    }

    fn intersection_refinements(
        mut left: BTreeMap<KotlinIdentifier, Vec<KotlinType>>,
        right: BTreeMap<KotlinIdentifier, Vec<KotlinType>>,
    ) -> BTreeMap<KotlinIdentifier, Vec<KotlinType>> {
        left.retain(|name, types| {
            let Some(other) = right.get(name) else {
                return false;
            };
            types.retain(|ty| other.contains(ty));
            !types.is_empty()
        });
        left
    }

    fn without_bound_names(facts: &SmartCastFacts, bound: &[KotlinIdentifier]) -> SmartCastFacts {
        let mut nested = facts.clone();
        for name in bound {
            nested.non_null.remove(name);
            nested.refined_types.remove(name);
        }
        nested
    }
}

#[derive(Debug, Default)]
struct LocalNameCollector {
    names: BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for LocalNameCollector {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(&mut self, _body: &mut super::KotlinAnonymousClassBody) {}

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match &statement {
            KotlinStmt::Variable { name, .. } => {
                self.names.insert(name.clone());
            }
            KotlinStmt::Try { catches, .. } => {
                self.names
                    .extend(catches.iter().map(|catch| catch.variable.clone()));
            }
            _ => {}
        }
        statement
    }
}

#[derive(Default)]
struct AssignmentTargetCollector {
    names: BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for AssignmentTargetCollector {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match &expression {
            KotlinExpr::Update { target, .. } | KotlinExpr::Assignment { target, .. } => {
                if let KotlinExpr::Name(name) = target.as_ref() {
                    self.names.insert(name.clone());
                }
            }
            _ => {}
        }
        expression
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Assign {
            target: KotlinExpr::Name(name),
            ..
        } = &statement
        {
            self.names.insert(name.clone());
        }
        statement
    }
}

impl KotlinAstTransform for KotlinLocalBindingAnalysis {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        let mut writes = AssignmentTargetCollector::default();
        writes.rewrite_statement(body.root.clone());
        let mut definitions = LocalDefinitionCollector::default();
        definitions.rewrite_statement(body.root.clone());
        let non_null = definitions.solve_non_null();
        let mut analysis = LocalBindingRewriter {
            writes: &writes.names,
            non_null: &non_null,
            changed: false,
        };
        body.root =
            analysis.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
        let mut collector = NonNullLocalCollector::default();
        collector.rewrite_statement(body.root.clone());
        let mut marker = NonNullNameMarker {
            names: &collector.names,
            changed: false,
        };
        body.root = marker.rewrite_statement(std::mem::replace(&mut body.root, KotlinStmt::Empty));
        Ok(analysis.changed || marker.changed)
    }
}

struct LocalBindingRewriter<'a> {
    writes: &'a BTreeSet<KotlinIdentifier>,
    non_null: &'a BTreeSet<KotlinIdentifier>,
    changed: bool,
}

impl KotlinAstRewriter for LocalBindingRewriter<'_> {
    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        let KotlinStmt::Variable {
            mut binding,
            mut ty,
            name,
            value,
        } = statement
        else {
            return statement;
        };
        let mutable = self.writes.contains(&name);
        if !mutable
            && value.as_ref().is_some_and(|value| {
                matches!(value, KotlinExpr::NewArray { initializer, .. }
                    if !initializer.is_empty()
                        && initializer.iter().all(KotlinNullabilityFacts::expression_definitely_non_null))
            })
        {
            self.changed |= ty.prove_array_elements_non_null();
        }
        let nullable = match &ty {
            KotlinType::Primitive(_) => false,
            KotlinType::Class(_) | KotlinType::Array(_) | KotlinType::Variable(_) => {
                !self.non_null.contains(&name)
            }
        };
        self.changed |= binding.mutable != mutable || binding.nullable != nullable;
        binding.mutable = mutable;
        binding.nullable = nullable;
        KotlinStmt::Variable {
            binding,
            ty,
            name,
            value,
        }
    }
}

#[derive(Debug, Default)]
struct LocalDefinitionCollector {
    definitions: BTreeMap<KotlinIdentifier, Vec<KotlinExpr>>,
}

impl LocalDefinitionCollector {
    fn record(&mut self, name: &KotlinIdentifier, value: &KotlinExpr) {
        self.definitions
            .entry(name.clone())
            .or_default()
            .push(value.clone());
    }

    fn solve_non_null(&self) -> BTreeSet<KotlinIdentifier> {
        let mut non_null = BTreeSet::new();
        loop {
            let before = non_null.len();
            for (name, definitions) in &self.definitions {
                if !definitions.is_empty()
                    && definitions
                        .iter()
                        .all(|value| definitely_non_null_with(value, &non_null))
                {
                    non_null.insert(name.clone());
                }
            }
            if non_null.len() == before {
                return non_null;
            }
        }
    }
}

impl KotlinAstRewriter for LocalDefinitionCollector {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(&mut self, _body: &mut super::KotlinAnonymousClassBody) {}

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Assignment {
            target,
            op: super::KotlinAssignOp::Assign,
            value,
        } = &expression
        {
            if let KotlinExpr::Name(name) = target.as_ref() {
                self.record(name, value);
            }
        }
        expression
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        match &statement {
            KotlinStmt::Variable {
                name,
                value: Some(value),
                ..
            } => self.record(name, value),
            KotlinStmt::Assign {
                target: KotlinExpr::Name(name),
                op: super::KotlinAssignOp::Assign,
                value,
            } => self.record(name, value),
            _ => {}
        }
        statement
    }
}

impl KotlinNullabilityFacts {
    pub fn expression_definitely_non_null(expression: &KotlinExpr) -> bool {
        definitely_non_null_with(expression, &BTreeSet::new())
    }

    pub fn of(body: &KotlinMethodBody) -> Self {
        let mut collector = NonNullLocalCollector::default();
        collector.rewrite_statement(body.root.clone());
        Self {
            non_null_locals: collector.names,
        }
    }

    pub fn all_value_returns_non_null(&self, body: &KotlinMethodBody) -> bool {
        let mut collector = ReturnNullabilityCollector {
            non_null_locals: &self.non_null_locals,
            saw_value_return: false,
            all_non_null: true,
        };
        collector.rewrite_statement(body.root.clone());
        collector.saw_value_return && collector.all_non_null
    }
}

#[derive(Debug, Default)]
struct NonNullLocalCollector {
    names: BTreeSet<KotlinIdentifier>,
}

struct NonNullNameMarker<'a> {
    names: &'a BTreeSet<KotlinIdentifier>,
    changed: bool,
}

impl KotlinAstRewriter for NonNullNameMarker<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(&mut self, _body: &mut super::KotlinAnonymousClassBody) {}

    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Name(name) if self.names.contains(&name) => {
                self.changed = true;
                KotlinExpr::SmartCast(Box::new(KotlinExpr::Name(name)))
            }
            KotlinExpr::SmartCast(value) => match *value {
                KotlinExpr::SmartCast(value) => KotlinExpr::SmartCast(value),
                value => KotlinExpr::SmartCast(Box::new(value)),
            },
            KotlinExpr::NonNullAssertion(value) => match *value {
                value @ KotlinExpr::SmartCast(_) => {
                    self.changed = true;
                    value
                }
                value => KotlinExpr::NonNullAssertion(Box::new(value)),
            },
            expression => expression,
        }
    }
}

impl KotlinAstRewriter for NonNullLocalCollector {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(&mut self, _body: &mut super::KotlinAnonymousClassBody) {}

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Variable { binding, name, .. } = &statement {
            if !binding.nullable {
                self.names.insert(name.clone());
            }
        }
        statement
    }
}

struct ReturnNullabilityCollector<'a> {
    non_null_locals: &'a BTreeSet<KotlinIdentifier>,
    saw_value_return: bool,
    all_non_null: bool,
}

impl KotlinAstRewriter for ReturnNullabilityCollector<'_> {
    fn rewrite_nested_functions(&self) -> bool {
        false
    }

    fn finish_anonymous_body(&mut self, _body: &mut super::KotlinAnonymousClassBody) {}

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Return(value) = &statement {
            self.saw_value_return |= value.is_some();
            self.all_non_null &= value
                .as_ref()
                .is_some_and(|value| definitely_non_null_with(value, self.non_null_locals));
        }
        statement
    }
}

fn definitely_non_null_with(
    expression: &KotlinExpr,
    non_null_names: &BTreeSet<KotlinIdentifier>,
) -> bool {
    match expression {
        KotlinExpr::This
        | KotlinExpr::QualifiedThis(_)
        | KotlinExpr::Super
        | KotlinExpr::ClassLiteral(_)
        | KotlinExpr::ObjectReference(_)
        | KotlinExpr::SmartCast(_)
        | KotlinExpr::NonNullAssertion(_)
        | KotlinExpr::Lambda { .. }
        | KotlinExpr::BlockLambda { .. }
        | KotlinExpr::New { .. }
        | KotlinExpr::NewArray { .. } => true,
        KotlinExpr::Literal(super::KotlinLiteral::Null) => false,
        KotlinExpr::Literal(_) => true,
        KotlinExpr::Conditional {
            when_true,
            when_false,
            ..
        } => {
            definitely_non_null_with(when_true, non_null_names)
                && definitely_non_null_with(when_false, non_null_names)
        }
        KotlinExpr::Name(name) => non_null_names.contains(name),
        KotlinExpr::Cast { value, .. }
        | KotlinExpr::JvmIntrinsic {
            expression: value, ..
        } => definitely_non_null_with(value, non_null_names),
        KotlinExpr::Field { .. }
        | KotlinExpr::StaticField { .. }
        | KotlinExpr::ArrayAccess { .. }
        | KotlinExpr::Call { .. }
        | KotlinExpr::MethodReference { .. }
        | KotlinExpr::Unary { .. }
        | KotlinExpr::Update { .. }
        | KotlinExpr::Binary { .. }
        | KotlinExpr::InstanceOf { .. }
        | KotlinExpr::Assignment { .. } => false,
    }
}

impl KotlinAstTransform for KotlinInitializerExitLowering {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        let KotlinStmt::Block(statements) = &mut body.root else {
            return Ok(false);
        };
        let mut changed = TerminalBranchLinearizer::apply_required_void_exit(statements);
        if changed {
            if let Some(last) = statements.last_mut() {
                changed |= KotlinAstNormalizer::strip_terminal_void_return(last);
            }
            if matches!(statements.last(), Some(KotlinStmt::Empty)) {
                statements.pop();
            }
        }
        Ok(changed)
    }
}

impl KotlinAstNormalizer {
    /// Canonicalizes a standalone expression produced after method-body
    /// lowering, such as a recovered default argument or field initializer.
    pub(crate) fn canonicalize_expression(expression: KotlinExpr) -> KotlinExpr {
        let mut normalizer = KotlinExpressionNormalizer { changed: false };
        normalizer.rewrite_expression(expression)
    }

    fn normalize(root: KotlinStmt) -> Result<(KotlinStmt, bool), super::KotlinStructuralError> {
        let mut pending = vec![SyntaxTask::Visit(root)];
        let mut results = Vec::new();
        let mut changed = false;
        while let Some(task) = pending.pop() {
            match task {
                SyntaxTask::Visit(statement) => match statement {
                    KotlinStmt::Block(children) => {
                        let count = children.len();
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Block(count)));
                        pending.extend(children.into_iter().rev().map(SyntaxTask::Visit));
                    }
                    KotlinStmt::Labeled { label, body } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Labeled(label)));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    KotlinStmt::If {
                        condition,
                        then_stmt,
                        else_stmt,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::If {
                            condition,
                            has_else: else_stmt.is_some(),
                        }));
                        if let Some(else_stmt) = else_stmt {
                            pending.push(SyntaxTask::Visit(*else_stmt));
                        }
                        pending.push(SyntaxTask::Visit(*then_stmt));
                    }
                    KotlinStmt::While {
                        label,
                        condition,
                        body,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::While { label, condition }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    KotlinStmt::DoWhile {
                        label,
                        body,
                        condition,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::DoWhile {
                            label,
                            condition,
                        }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    KotlinStmt::For {
                        label,
                        init,
                        condition,
                        update,
                        body,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::For {
                            label,
                            init,
                            condition,
                            update,
                        }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    KotlinStmt::ForEach {
                        label,
                        ty,
                        variable,
                        iterable,
                        body,
                    } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::ForEach {
                            label,
                            ty,
                            variable,
                            iterable,
                        }));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    KotlinStmt::Switch {
                        label,
                        selector,
                        mut cases,
                    } => {
                        let bodies = cases
                            .iter_mut()
                            .map(|case| KotlinStmt::Block(std::mem::take(&mut case.body)))
                            .collect::<Vec<_>>();
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Switch {
                            label,
                            selector,
                            cases,
                        }));
                        pending.extend(bodies.into_iter().rev().map(SyntaxTask::Visit));
                    }
                    KotlinStmt::Try {
                        body,
                        mut catches,
                        finally,
                    } => {
                        let has_finally = finally.is_some();
                        let mut bodies =
                            Vec::with_capacity(1 + catches.len() + usize::from(has_finally));
                        bodies.push(*body);
                        bodies.extend(
                            catches
                                .iter_mut()
                                .map(|catch| std::mem::replace(&mut catch.body, KotlinStmt::Empty)),
                        );
                        if let Some(finally) = finally {
                            bodies.push(*finally);
                        }
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Try {
                            catches,
                            has_finally,
                        }));
                        pending.extend(bodies.into_iter().rev().map(SyntaxTask::Visit));
                    }
                    KotlinStmt::Synchronized { lock, body } => {
                        pending.push(SyntaxTask::Rebuild(SyntaxFrame::Synchronized(lock)));
                        pending.push(SyntaxTask::Visit(*body));
                    }
                    leaf => results.push(leaf),
                },
                SyntaxTask::Rebuild(frame) => {
                    let count = frame.child_count();
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(super::KotlinStructuralError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect();
                    let (statement, local_change) = frame.rebuild(children)?;
                    changed |= local_change;
                    results.push(statement);
                }
            }
        }
        let [root] = results.as_slice() else {
            return Err(super::KotlinStructuralError::MalformedWorkStack);
        };
        Ok((root.clone(), changed))
    }

    fn flatten(children: Vec<KotlinStmt>) -> (Vec<KotlinStmt>, bool) {
        let mut flattened = Vec::with_capacity(children.len());
        let mut pending = children.into_iter().rev().collect::<Vec<_>>();
        let mut changed = false;
        while let Some(child) = pending.pop() {
            match child {
                KotlinStmt::Block(children) => {
                    pending.extend(children.into_iter().rev());
                    changed = true;
                }
                KotlinStmt::Empty => changed = true,
                child => flattened.push(child),
            }
        }
        changed |= TerminalBranchLinearizer::apply(&mut flattened);
        (flattened, changed)
    }

    fn protection(
        body: KotlinStmt,
        catches: Vec<KotlinCatch>,
        finally: Option<Box<KotlinStmt>>,
    ) -> (KotlinStmt, bool) {
        let empty_finally = finally.as_deref().is_some_and(|finally| match finally {
            KotlinStmt::Empty => true,
            KotlinStmt::Block(statements) => statements.is_empty(),
            _ => false,
        });
        if catches.is_empty() && empty_finally {
            return (body, true);
        }
        let empty_body = match &body {
            KotlinStmt::Empty => true,
            KotlinStmt::Block(statements) => statements.is_empty(),
            _ => false,
        };
        if empty_body && finally.is_none() {
            return (KotlinStmt::Empty, true);
        }
        match (catches.is_empty() && finally.is_some(), body) {
            (
                true,
                KotlinStmt::Try {
                    body,
                    catches,
                    finally: None,
                },
            ) => (
                KotlinStmt::Try {
                    body,
                    catches,
                    finally,
                },
                true,
            ),
            (_, body) => (
                KotlinStmt::Try {
                    body: Box::new(body),
                    catches,
                    finally,
                },
                false,
            ),
        }
    }

    fn synchronized(lock: KotlinExpr, body: KotlinStmt) -> (KotlinStmt, bool) {
        let KotlinStmt::Block(mut statements) = body else {
            return (
                KotlinStmt::Synchronized {
                    lock,
                    body: Box::new(body),
                },
                false,
            );
        };
        let Some(KotlinStmt::Synchronized {
            lock: inner_lock,
            body: inner_body,
        }) = statements.first()
        else {
            return (
                KotlinStmt::Synchronized {
                    lock,
                    body: Box::new(KotlinStmt::Block(statements)),
                },
                false,
            );
        };
        if inner_lock != &lock || !matches!(lock, KotlinExpr::Name(_)) {
            return (
                KotlinStmt::Synchronized {
                    lock,
                    body: Box::new(KotlinStmt::Block(statements)),
                },
                false,
            );
        }
        let inner = match inner_body.as_ref() {
            KotlinStmt::Block(inner) => inner.clone(),
            KotlinStmt::Empty => Vec::new(),
            statement => vec![statement.clone()],
        };
        statements.splice(0..1, inner);
        (
            KotlinStmt::Synchronized {
                lock,
                body: Box::new(KotlinStmt::Block(statements)),
            },
            true,
        )
    }

    fn foreach(
        label: Option<KotlinIdentifier>,
        ty: KotlinType,
        variable: KotlinIdentifier,
        iterable: KotlinExpr,
        body: KotlinStmt,
    ) -> (KotlinStmt, bool) {
        let KotlinStmt::Block(mut statements) = body else {
            return (
                KotlinStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(body),
                },
                false,
            );
        };
        let Some(KotlinStmt::Variable {
            ty: target_type,
            name: target,
            value:
                Some(KotlinExpr::Cast {
                    ty: cast_type,
                    value,
                }),
            ..
        }) = statements.first()
        else {
            return (
                KotlinStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(KotlinStmt::Block(statements)),
                },
                false,
            );
        };
        if target_type != cast_type
            || !matches!(value.as_ref(), KotlinExpr::Name(source) if source == &variable)
        {
            return (
                KotlinStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(KotlinStmt::Block(statements)),
                },
                false,
            );
        }
        let mut uses = NameUseCounter {
            target: &variable,
            count: 0,
        };
        for statement in statements.iter().skip(1).cloned() {
            uses.rewrite_statement(statement);
        }
        if uses.count != 0 {
            return (
                KotlinStmt::ForEach {
                    label,
                    ty,
                    variable,
                    iterable,
                    body: Box::new(KotlinStmt::Block(statements)),
                },
                false,
            );
        }
        let target_type = target_type.clone();
        let target = target.clone();
        statements.remove(0);
        (
            KotlinStmt::ForEach {
                label,
                ty: target_type,
                variable: target,
                iterable,
                body: Box::new(KotlinStmt::Block(statements)),
            },
            true,
        )
    }

    fn conditional(
        condition: KotlinExpr,
        then_stmt: KotlinStmt,
        else_stmt: Option<KotlinStmt>,
    ) -> (KotlinStmt, bool) {
        if let Some(else_stmt) = else_stmt {
            let then_empty = Self::is_empty(&then_stmt);
            let else_empty = Self::is_empty(&else_stmt);
            if then_empty && !else_empty {
                return (
                    KotlinStmt::If {
                        condition: condition.negated(),
                        then_stmt: Box::new(else_stmt),
                        else_stmt: None,
                    },
                    true,
                );
            }
            if !then_empty && else_empty {
                return (
                    KotlinStmt::If {
                        condition,
                        then_stmt: Box::new(then_stmt),
                        else_stmt: None,
                    },
                    true,
                );
            }
            if let Some((nested_condition, nested_then, Some(nested_else))) =
                Self::conditional_view(&then_stmt)
            {
                if Self::same_branch(nested_else, &else_stmt) {
                    return (
                        KotlinStmt::If {
                            condition: KotlinExpr::Binary {
                                left: Box::new(condition),
                                op: KotlinBinaryOp::LogicalAnd,
                                right: Box::new(nested_condition.clone()),
                            },
                            then_stmt: Box::new(nested_then.clone()),
                            else_stmt: Some(Box::new(else_stmt)),
                        },
                        true,
                    );
                }
            }
            if let Some((nested_condition, nested_then, nested_else)) =
                Self::conditional_view(&else_stmt)
            {
                if Self::same_branch(nested_then, &then_stmt) {
                    return (
                        KotlinStmt::If {
                            condition: KotlinExpr::Binary {
                                left: Box::new(condition),
                                op: KotlinBinaryOp::LogicalOr,
                                right: Box::new(nested_condition.clone()),
                            },
                            then_stmt: Box::new(then_stmt),
                            else_stmt: nested_else.cloned().map(Box::new),
                        },
                        true,
                    );
                }
            }
            return (
                KotlinStmt::If {
                    condition,
                    then_stmt: Box::new(then_stmt),
                    else_stmt: Some(Box::new(else_stmt)),
                },
                false,
            );
        }
        let nested = match &then_stmt {
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt: None,
            } => Some((condition.clone(), then_stmt.as_ref().clone())),
            KotlinStmt::Block(statements) => match statements.as_slice() {
                [KotlinStmt::If {
                    condition,
                    then_stmt,
                    else_stmt: None,
                }] => Some((condition.clone(), then_stmt.as_ref().clone())),
                _ => None,
            },
            _ => None,
        };
        if let Some((nested_condition, nested_body)) = nested {
            return (
                KotlinStmt::If {
                    condition: KotlinExpr::Binary {
                        left: Box::new(condition),
                        op: KotlinBinaryOp::LogicalAnd,
                        right: Box::new(nested_condition),
                    },
                    then_stmt: Box::new(nested_body),
                    else_stmt: None,
                },
                true,
            );
        }
        (
            KotlinStmt::If {
                condition,
                then_stmt: Box::new(then_stmt),
                else_stmt: None,
            },
            false,
        )
    }

    fn conditional_view(
        statement: &KotlinStmt,
    ) -> Option<(&KotlinExpr, &KotlinStmt, Option<&KotlinStmt>)> {
        let KotlinStmt::If {
            condition,
            then_stmt,
            else_stmt,
        } = Self::branch_view(statement)
        else {
            return None;
        };
        Some((
            condition,
            Self::branch_view(then_stmt),
            else_stmt.as_deref().map(Self::branch_view),
        ))
    }

    fn branch_view(mut statement: &KotlinStmt) -> &KotlinStmt {
        while let KotlinStmt::Block(statements) = statement {
            let [single] = statements.as_slice() else {
                break;
            };
            statement = single;
        }
        statement
    }

    fn same_branch(left: &KotlinStmt, right: &KotlinStmt) -> bool {
        Self::branch_view(left) == Self::branch_view(right)
    }

    fn is_empty(statement: &KotlinStmt) -> bool {
        matches!(statement, KotlinStmt::Empty)
            || matches!(statement, KotlinStmt::Block(statements) if statements.is_empty())
    }

    fn strip_terminal_void_return(statement: &mut KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Return(None) => {
                *statement = KotlinStmt::Empty;
                true
            }
            KotlinStmt::Block(statements) => {
                let changed = statements
                    .last_mut()
                    .is_some_and(Self::strip_terminal_void_return);
                if matches!(statements.last(), Some(KotlinStmt::Empty)) {
                    statements.pop();
                }
                changed
            }
            KotlinStmt::Synchronized { body, .. } => Self::strip_terminal_void_return(body),
            _ => false,
        }
    }
}

struct TerminalBranchLinearizer;

impl TerminalBranchLinearizer {
    const NESTING_PENALTY: usize = 12;

    fn apply(statements: &mut Vec<KotlinStmt>) -> bool {
        let mut changed = false;
        let mut index = 0usize;
        while index + 1 < statements.len() {
            let Some(candidate) = Self::candidate(statements, index) else {
                index += 1;
                continue;
            };
            Self::linearize(statements, index, candidate);
            changed = true;
            index += 1;
        }
        changed
    }

    fn apply_required_void_exit(statements: &mut Vec<KotlinStmt>) -> bool {
        let mut changed = false;
        let mut index = 0usize;
        while index + 1 < statements.len() {
            let Some(candidate) = Self::required_void_exit_candidate(statements, index) else {
                index += 1;
                continue;
            };
            Self::linearize(statements, index, candidate);
            changed = true;
            index += 1;
        }
        changed
    }

    fn linearize(
        statements: &mut Vec<KotlinStmt>,
        index: usize,
        candidate: TerminalBranchCandidate,
    ) {
        let tail = statements.split_off(index + 1);
        let Some(KotlinStmt::If {
            condition,
            then_stmt,
            else_stmt: None,
        }) = statements.pop()
        else {
            unreachable!("terminal branch candidate changed during linearization");
        };
        statements.push(KotlinStmt::If {
            condition: condition.negated(),
            then_stmt: Box::new(KotlinStmt::Block(tail.clone())),
            else_stmt: None,
        });
        match *then_stmt {
            KotlinStmt::Block(body) => statements.extend(body),
            KotlinStmt::Empty => {}
            statement => statements.push(statement),
        }
        if candidate.duplicates_tail {
            statements.extend(tail);
        }
    }

    fn candidate(statements: &[KotlinStmt], index: usize) -> Option<TerminalBranchCandidate> {
        let KotlinStmt::If {
            condition,
            then_stmt,
            else_stmt: None,
        } = statements.get(index)?
        else {
            return None;
        };
        let tail = &statements[index + 1..];
        if Self::sequence_can_complete_normally(tail) {
            return None;
        }
        let then_depth = Self::nesting_depth(then_stmt);
        let tail_depth = tail
            .iter()
            .map(Self::nesting_depth)
            .max()
            .unwrap_or_default();
        let original_depth = (then_depth + 1).max(tail_depth);
        let linearized_depth = then_depth.max(tail_depth + 1);
        let lowers_nesting = linearized_depth < original_depth;
        let lowers_condition_cost = linearized_depth == original_depth
            && condition.clone().negated().cost() < condition.cost();
        if !lowers_nesting && !lowers_condition_cost {
            return None;
        }
        let duplicates_tail = Self::can_complete_normally(then_stmt);
        if duplicates_tail {
            let depth_reduction = original_depth.saturating_sub(linearized_depth);
            let duplication_budget = depth_reduction.saturating_mul(Self::NESTING_PENALTY);
            if Self::sequence_cost(tail) > duplication_budget {
                return None;
            }
        }
        Some(TerminalBranchCandidate { duplicates_tail })
    }

    fn required_void_exit_candidate(
        statements: &[KotlinStmt],
        index: usize,
    ) -> Option<TerminalBranchCandidate> {
        let KotlinStmt::If {
            then_stmt,
            else_stmt: None,
            ..
        } = statements.get(index)?
        else {
            return None;
        };
        let tail = &statements[index + 1..];
        (!tail.is_empty()
            && !Self::sequence_can_complete_normally(tail)
            && Self::terminates_with_void_return(then_stmt))
        .then(|| TerminalBranchCandidate {
            duplicates_tail: Self::can_complete_normally(then_stmt),
        })
    }

    fn terminates_with_void_return(statement: &KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Return(None) => true,
            KotlinStmt::Block(statements) => statements
                .last()
                .is_some_and(Self::terminates_with_void_return),
            KotlinStmt::Synchronized { body, .. } => Self::terminates_with_void_return(body),
            KotlinStmt::If {
                then_stmt,
                else_stmt: Some(else_stmt),
                ..
            } => {
                Self::terminates_with_void_return(then_stmt)
                    && Self::terminates_with_void_return(else_stmt)
            }
            _ => false,
        }
    }

    fn sequence_can_complete_normally(statements: &[KotlinStmt]) -> bool {
        statements.iter().all(Self::can_complete_normally)
    }

    fn can_complete_normally(statement: &KotlinStmt) -> bool {
        match statement {
            KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => false,
            KotlinStmt::Block(statements) => Self::sequence_can_complete_normally(statements),
            KotlinStmt::If {
                then_stmt,
                else_stmt: Some(else_stmt),
                ..
            } => Self::can_complete_normally(then_stmt) || Self::can_complete_normally(else_stmt),
            KotlinStmt::Synchronized { body, .. } => Self::can_complete_normally(body),
            KotlinStmt::While {
                label,
                condition,
                body,
            } => {
                !Self::is_true(condition)
                    || Self::contains_exiting_break(body, label.as_ref(), true)
            }
            KotlinStmt::DoWhile {
                label,
                body,
                condition,
            } => {
                Self::contains_exiting_break(body, label.as_ref(), true)
                    || (Self::can_complete_normally(body) && !Self::is_true(condition))
            }
            KotlinStmt::For {
                label,
                condition,
                body,
                ..
            } => {
                condition
                    .as_ref()
                    .is_some_and(|condition| !Self::is_true(condition))
                    || Self::contains_exiting_break(body, label.as_ref(), true)
            }
            KotlinStmt::Switch { label, cases, .. } => {
                Self::switch_can_complete_normally(label.as_ref(), cases)
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                let protected_completes = Self::can_complete_normally(body)
                    || catches
                        .iter()
                        .any(|catch| Self::can_complete_normally(&catch.body));
                let finally_completes = finally.as_deref().is_none_or(Self::can_complete_normally);
                protected_completes && finally_completes
            }
            KotlinStmt::Empty
            | KotlinStmt::Variable { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::Assign { .. }
            | KotlinStmt::If {
                else_stmt: None, ..
            }
            | KotlinStmt::Labeled { .. }
            | KotlinStmt::ForEach { .. } => true,
        }
    }

    fn is_true(expression: &KotlinExpr) -> bool {
        matches!(
            expression,
            KotlinExpr::Literal(super::KotlinLiteral::Boolean(true))
        )
    }

    fn switch_can_complete_normally(
        label: Option<&KotlinIdentifier>,
        cases: &[KotlinSwitchCase],
    ) -> bool {
        if cases.is_empty() || !cases.iter().any(|case| case.is_default) {
            return true;
        }
        if cases
            .last()
            .is_some_and(|case| Self::sequence_can_complete_normally(&case.body))
        {
            return true;
        }
        cases.iter().any(|case| {
            case.body
                .iter()
                .any(|statement| Self::contains_exiting_break(statement, label, true))
        })
    }

    fn contains_exiting_break(
        root: &KotlinStmt,
        target_label: Option<&KotlinIdentifier>,
        direct: bool,
    ) -> bool {
        let mut pending = vec![(root, direct)];
        while let Some((statement, direct)) = pending.pop() {
            match statement {
                KotlinStmt::Break(None) if direct => return true,
                KotlinStmt::Break(Some(label)) if target_label == Some(label) => return true,
                KotlinStmt::Block(statements) => {
                    pending.extend(statements.iter().map(|statement| (statement, direct)));
                }
                KotlinStmt::If {
                    then_stmt,
                    else_stmt,
                    ..
                } => {
                    pending.push((then_stmt, direct));
                    pending.extend(else_stmt.as_deref().map(|statement| (statement, direct)));
                }
                KotlinStmt::Labeled { body, .. } | KotlinStmt::Synchronized { body, .. } => {
                    pending.push((body, direct));
                }
                KotlinStmt::Try {
                    body,
                    catches,
                    finally,
                } => {
                    pending.push((body, direct));
                    pending.extend(catches.iter().map(|catch| (&catch.body, direct)));
                    pending.extend(finally.as_deref().map(|statement| (statement, direct)));
                }
                KotlinStmt::While { body, .. }
                | KotlinStmt::DoWhile { body, .. }
                | KotlinStmt::For { body, .. }
                | KotlinStmt::ForEach { body, .. } => {
                    if target_label.is_some() {
                        pending.push((body, false));
                    }
                }
                KotlinStmt::Switch { cases, .. } => {
                    if target_label.is_some() {
                        pending.extend(
                            cases
                                .iter()
                                .flat_map(|case| &case.body)
                                .map(|statement| (statement, false)),
                        );
                    }
                }
                KotlinStmt::Empty
                | KotlinStmt::Variable { .. }
                | KotlinStmt::Expression(_)
                | KotlinStmt::ConstructorInvocation { .. }
                | KotlinStmt::Assign { .. }
                | KotlinStmt::Return(_)
                | KotlinStmt::Throw(_)
                | KotlinStmt::Break(None)
                | KotlinStmt::Break(Some(_))
                | KotlinStmt::Continue(_) => {}
            }
        }
        false
    }

    fn nesting_depth(statement: &KotlinStmt) -> usize {
        match statement {
            KotlinStmt::Block(statements) => statements
                .iter()
                .map(Self::nesting_depth)
                .max()
                .unwrap_or_default(),
            KotlinStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                1 + Self::nesting_depth(then_stmt).max(
                    else_stmt
                        .as_deref()
                        .map(Self::nesting_depth)
                        .unwrap_or_default(),
                )
            }
            KotlinStmt::Labeled { body, .. }
            | KotlinStmt::While { body, .. }
            | KotlinStmt::DoWhile { body, .. }
            | KotlinStmt::For { body, .. }
            | KotlinStmt::ForEach { body, .. }
            | KotlinStmt::Synchronized { body, .. } => 1 + Self::nesting_depth(body),
            KotlinStmt::Switch { cases, .. } => {
                1 + cases
                    .iter()
                    .flat_map(|case| &case.body)
                    .map(Self::nesting_depth)
                    .max()
                    .unwrap_or_default()
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                let branches = std::iter::once(body.as_ref())
                    .chain(catches.iter().map(|catch| &catch.body))
                    .chain(finally.as_deref());
                1 + branches.map(Self::nesting_depth).max().unwrap_or_default()
            }
            KotlinStmt::Empty
            | KotlinStmt::Variable { .. }
            | KotlinStmt::Expression(_)
            | KotlinStmt::ConstructorInvocation { .. }
            | KotlinStmt::Assign { .. }
            | KotlinStmt::Return(_)
            | KotlinStmt::Throw(_)
            | KotlinStmt::Break(_)
            | KotlinStmt::Continue(_) => 0,
        }
    }

    fn sequence_cost(statements: &[KotlinStmt]) -> usize {
        statements.iter().map(Self::statement_cost).sum()
    }

    fn statement_cost(statement: &KotlinStmt) -> usize {
        match statement {
            KotlinStmt::Empty => 0,
            KotlinStmt::Variable { value, .. } => {
                1 + value.as_ref().map(KotlinExpr::cost).unwrap_or_default()
            }
            KotlinStmt::Expression(expression) | KotlinStmt::Throw(expression) => {
                1 + expression.cost()
            }
            KotlinStmt::ConstructorInvocation { args, .. } => {
                1 + args.iter().map(KotlinExpr::cost).sum::<usize>()
            }
            KotlinStmt::Assign { target, value, .. } => 1 + target.cost() + value.cost(),
            KotlinStmt::Return(value) => {
                1 + value.as_ref().map(KotlinExpr::cost).unwrap_or_default()
            }
            KotlinStmt::Break(_) | KotlinStmt::Continue(_) => 1,
            KotlinStmt::Block(statements) => Self::sequence_cost(statements),
            KotlinStmt::Labeled { body, .. }
            | KotlinStmt::While { body, .. }
            | KotlinStmt::DoWhile { body, .. }
            | KotlinStmt::ForEach { body, .. }
            | KotlinStmt::Synchronized { body, .. } => 1 + Self::statement_cost(body),
            KotlinStmt::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                1 + Self::sequence_cost(init)
                    + condition.as_ref().map(KotlinExpr::cost).unwrap_or_default()
                    + update.iter().map(KotlinExpr::cost).sum::<usize>()
                    + Self::statement_cost(body)
            }
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
            KotlinStmt::Switch {
                selector, cases, ..
            } => {
                1 + selector.cost()
                    + cases
                        .iter()
                        .map(|case| Self::sequence_cost(&case.body))
                        .sum::<usize>()
            }
            KotlinStmt::Try {
                body,
                catches,
                finally,
            } => {
                1 + Self::statement_cost(body)
                    + catches
                        .iter()
                        .map(|catch| Self::statement_cost(&catch.body))
                        .sum::<usize>()
                    + finally
                        .as_deref()
                        .map(Self::statement_cost)
                        .unwrap_or_default()
            }
        }
    }
}

struct TerminalBranchCandidate {
    duplicates_tail: bool,
}

impl KotlinAstTransform for KotlinAstNormalizer {
    type Error = super::KotlinStructuralError;

    fn apply(&mut self, body: &mut KotlinMethodBody) -> Result<bool, Self::Error> {
        let (mut root, mut changed) =
            Self::normalize(std::mem::replace(&mut body.root, KotlinStmt::Empty))?;
        if let KotlinStmt::Block(statements) = &mut root {
            if let Some(last) = statements.last_mut() {
                changed |= Self::strip_terminal_void_return(last);
            }
            if matches!(statements.last(), Some(KotlinStmt::Empty)) {
                statements.pop();
            }
        }
        let mut expressions = KotlinExpressionNormalizer { changed: false };
        body.root = expressions.rewrite_statement(root);
        changed |= expressions.changed;
        Ok(changed)
    }
}

struct KotlinExpressionNormalizer {
    changed: bool,
}

impl KotlinAstRewriter for KotlinExpressionNormalizer {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        let original = expression.clone();
        let replacement = match expression {
            KotlinExpr::Call {
                receiver,
                owner,
                type_arguments,
                method,
                mut args,
            } => {
                let empty_spreads = args
                    .as_slice()
                    .iter()
                    .enumerate()
                    .filter(|(index, value)| args.is_spread(*index) && is_empty_array(value))
                    .map(|(index, _)| index)
                    .collect::<Vec<_>>();
                for index in empty_spreads.into_iter().rev() {
                    args.remove(index);
                }
                KotlinExpr::Call {
                    receiver,
                    owner,
                    type_arguments,
                    method,
                    args,
                }
            }
            KotlinExpr::Binary { left, op, right } => fold_boolean_binary(&left, op, &right)
                .unwrap_or(KotlinExpr::Binary { left, op, right }),
            KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => match condition.as_ref() {
                KotlinExpr::Literal(super::KotlinLiteral::Boolean(true)) => *when_true,
                KotlinExpr::Literal(super::KotlinLiteral::Boolean(false)) => *when_false,
                _ => KotlinExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                },
            },
            KotlinExpr::Unary {
                op: super::KotlinUnaryOp::LogicalNot,
                operand,
            } => match operand.as_ref() {
                KotlinExpr::Literal(super::KotlinLiteral::Boolean(value)) => {
                    KotlinExpr::Literal(super::KotlinLiteral::Boolean(!value))
                }
                _ => KotlinExpr::Unary {
                    op: super::KotlinUnaryOp::LogicalNot,
                    operand,
                },
            },
            KotlinExpr::Cast { ty, value } if literal_has_type(&value, &ty) => *value,
            KotlinExpr::NonNullAssertion(value)
                if KotlinNullabilityFacts::expression_definitely_non_null(&value) =>
            {
                *value
            }
            expression => expression,
        };
        self.changed |= replacement != original;
        replacement
    }

    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Block(mut statements) = statement {
            if let Some(terminal) = statements
                .iter()
                .position(|statement| !SmartCastFlow::completes_normally(statement))
            {
                self.changed |= terminal + 1 != statements.len();
                statements.truncate(terminal + 1);
            }
            return KotlinStmt::Block(statements);
        }
        let KotlinStmt::If {
            condition,
            then_stmt,
            else_stmt,
        } = statement
        else {
            return statement;
        };
        match condition {
            KotlinExpr::Literal(super::KotlinLiteral::Boolean(true)) => {
                self.changed = true;
                *then_stmt
            }
            KotlinExpr::Literal(super::KotlinLiteral::Boolean(false)) => {
                self.changed = true;
                else_stmt.map_or(KotlinStmt::Empty, |statement| *statement)
            }
            condition => KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            },
        }
    }
}

fn is_empty_array(expression: &KotlinExpr) -> bool {
    matches!(
        expression,
        KotlinExpr::NewArray {
            dimensions,
            initializer,
            ..
        } if initializer.is_empty()
            && matches!(dimensions.as_slice(), [KotlinExpr::Literal(super::KotlinLiteral::Integer(0))])
    )
}

fn literal_has_type(expression: &KotlinExpr, ty: &KotlinType) -> bool {
    matches!(
        (expression, ty),
        (
            KotlinExpr::Literal(super::KotlinLiteral::Integer(_)),
            KotlinType::Primitive(super::KotlinPrimitiveType::Int)
        ) | (
            KotlinExpr::Literal(super::KotlinLiteral::Long(_)),
            KotlinType::Primitive(super::KotlinPrimitiveType::Long)
        ) | (
            KotlinExpr::Literal(super::KotlinLiteral::Float(_)),
            KotlinType::Primitive(super::KotlinPrimitiveType::Float)
        ) | (
            KotlinExpr::Literal(super::KotlinLiteral::Double(_)),
            KotlinType::Primitive(super::KotlinPrimitiveType::Double)
        ) | (
            KotlinExpr::Literal(super::KotlinLiteral::Character(_)),
            KotlinType::Primitive(super::KotlinPrimitiveType::Char)
        )
    )
}

fn fold_boolean_binary(
    left: &KotlinExpr,
    op: KotlinBinaryOp,
    right: &KotlinExpr,
) -> Option<KotlinExpr> {
    let KotlinExpr::Literal(super::KotlinLiteral::Boolean(left)) = left else {
        return None;
    };
    match (op, *left) {
        (KotlinBinaryOp::LogicalAnd, true) | (KotlinBinaryOp::LogicalOr, false) => {
            Some(right.clone())
        }
        (KotlinBinaryOp::LogicalAnd, false) => {
            Some(KotlinExpr::Literal(super::KotlinLiteral::Boolean(false)))
        }
        (KotlinBinaryOp::LogicalOr, true) => {
            Some(KotlinExpr::Literal(super::KotlinLiteral::Boolean(true)))
        }
        _ => None,
    }
}

enum SyntaxTask {
    Visit(KotlinStmt),
    Rebuild(SyntaxFrame),
}

enum SyntaxFrame {
    Block(usize),
    Labeled(KotlinIdentifier),
    If {
        condition: KotlinExpr,
        has_else: bool,
    },
    While {
        label: Option<KotlinIdentifier>,
        condition: KotlinExpr,
    },
    DoWhile {
        label: Option<KotlinIdentifier>,
        condition: KotlinExpr,
    },
    For {
        label: Option<KotlinIdentifier>,
        init: Vec<KotlinStmt>,
        condition: Option<KotlinExpr>,
        update: Vec<KotlinExpr>,
    },
    ForEach {
        label: Option<KotlinIdentifier>,
        ty: KotlinType,
        variable: KotlinIdentifier,
        iterable: KotlinExpr,
    },
    Switch {
        label: Option<KotlinIdentifier>,
        selector: KotlinExpr,
        cases: Vec<KotlinSwitchCase>,
    },
    Try {
        catches: Vec<KotlinCatch>,
        has_finally: bool,
    },
    Synchronized(KotlinExpr),
}

impl SyntaxFrame {
    fn child_count(&self) -> usize {
        match self {
            Self::Block(count) => *count,
            Self::Labeled(_) => 1,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::While { .. }
            | Self::DoWhile { .. }
            | Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized(_) => 1,
            Self::Switch { cases, .. } => cases.len(),
            Self::Try {
                catches,
                has_finally,
            } => 1 + catches.len() + usize::from(*has_finally),
        }
    }

    fn rebuild(
        self,
        children: Vec<KotlinStmt>,
    ) -> Result<(KotlinStmt, bool), super::KotlinStructuralError> {
        let expected = self.child_count();
        if children.len() != expected {
            return Err(super::KotlinStructuralError::ChildArity {
                expected,
                actual: children.len(),
            });
        }
        let mut children = children.into_iter();
        let statement = match self {
            Self::Block(_) => {
                let (children, changed) = KotlinAstNormalizer::flatten(children.collect());
                return Ok((KotlinStmt::Block(children), changed));
            }
            Self::Labeled(label) => KotlinStmt::Labeled {
                label,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::If {
                condition,
                has_else,
            } => {
                let then_stmt = Self::child(&mut children)?;
                let else_stmt = if has_else {
                    Some(Self::child(&mut children)?)
                } else {
                    None
                };
                return Ok(KotlinAstNormalizer::conditional(
                    condition, then_stmt, else_stmt,
                ));
            }
            Self::While { label, condition } => KotlinStmt::While {
                label,
                condition,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::DoWhile { label, condition } => KotlinStmt::DoWhile {
                label,
                body: Box::new(Self::child(&mut children)?),
                condition,
            },
            Self::For {
                label,
                init,
                condition,
                update,
            } => KotlinStmt::For {
                label,
                init,
                condition,
                update,
                body: Box::new(Self::child(&mut children)?),
            },
            Self::ForEach {
                label,
                ty,
                variable,
                iterable,
            } => {
                return Ok(KotlinAstNormalizer::foreach(
                    label,
                    ty,
                    variable,
                    iterable,
                    Self::child(&mut children)?,
                ));
            }
            Self::Switch {
                label,
                selector,
                mut cases,
            } => {
                let mut changed = false;
                for case in &mut cases {
                    case.body = match Self::child(&mut children)? {
                        KotlinStmt::Block(body) => body,
                        KotlinStmt::Empty => Vec::new(),
                        statement => vec![statement],
                    };
                    let exits_switch = matches!(case.body.last(), Some(KotlinStmt::Break(None)))
                        || matches!(
                            (case.body.last(), label.as_ref()),
                            (Some(KotlinStmt::Break(Some(target))), Some(label)) if target == label
                        );
                    if exits_switch {
                        case.body.pop();
                        changed = true;
                    }
                }
                return Ok((
                    KotlinStmt::Switch {
                        label: None,
                        selector,
                        cases,
                    },
                    changed || label.is_some(),
                ));
            }
            Self::Try {
                mut catches,
                has_finally,
            } => {
                let body = Self::child(&mut children)?;
                for catch in &mut catches {
                    catch.body = Self::child(&mut children)?;
                }
                let finally = if has_finally {
                    Some(Box::new(Self::child(&mut children)?))
                } else {
                    None
                };
                return Ok(KotlinAstNormalizer::protection(body, catches, finally));
            }
            Self::Synchronized(lock) => {
                return Ok(KotlinAstNormalizer::synchronized(
                    lock,
                    Self::child(&mut children)?,
                ));
            }
        };
        Ok((statement, false))
    }

    fn child(
        children: &mut impl Iterator<Item = KotlinStmt>,
    ) -> Result<KotlinStmt, super::KotlinStructuralError> {
        children
            .next()
            .ok_or(super::KotlinStructuralError::MalformedWorkStack)
    }
}

struct NameUseCounter<'a> {
    target: &'a KotlinIdentifier,
    count: usize,
}

impl KotlinAstRewriter for NameUseCounter<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if matches!(&expression, KotlinExpr::Name(name) if name == self.target) {
            self.count += 1;
        }
        expression
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::kotlin::{
        KotlinAssignOp, KotlinClassType, KotlinClassTypeSegment, KotlinLiteral, KotlinTypeArgument,
    };

    fn name(value: &str) -> KotlinExpr {
        KotlinExpr::Name(KotlinIdentifier::from_dex(value))
    }

    #[test]
    fn removes_try_with_only_an_empty_finally() {
        let statement = KotlinStmt::Expression(name("work"));
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Try {
                body: Box::new(statement.clone()),
                catches: Vec::new(),
                finally: Some(Box::new(KotlinStmt::Block(Vec::new()))),
            },
        };

        assert!(KotlinAstNormalizer.apply(&mut body).unwrap());
        assert_eq!(body.root, statement);
    }

    #[test]
    fn canonicalizes_assertion_over_proven_non_null_expression() {
        let expression = KotlinExpr::NonNullAssertion(Box::new(KotlinExpr::Literal(
            KotlinLiteral::String("default".into()),
        )));

        assert_eq!(
            KotlinAstNormalizer::canonicalize_expression(expression),
            KotlinExpr::Literal(KotlinLiteral::String("default".into()))
        );
    }

    #[test]
    fn preserves_assertion_without_a_non_null_proof() {
        let expression = KotlinExpr::NonNullAssertion(Box::new(name("value")));

        assert!(matches!(
            KotlinAstNormalizer::canonicalize_expression(expression),
            KotlinExpr::NonNullAssertion(value)
                if matches!(value.as_ref(), KotlinExpr::Name(_))
        ));
    }

    #[test]
    fn removes_redundant_assertion_from_non_null_extension_receiver() {
        let receiver = KotlinIdentifier::from_dex("receiver");
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Return(Some(KotlinExpr::NonNullAssertion(Box::new(
                KotlinExpr::Name(receiver.clone()),
            )))),
        };

        KotlinExtensionReceiverLowering::new(receiver, false)
            .apply(&mut body)
            .expect("extension receiver lowering");

        assert!(matches!(
            body.root,
            KotlinStmt::Return(Some(KotlinExpr::This))
        ));
    }

    #[test]
    fn preserves_assertion_from_nullable_extension_receiver() {
        let receiver = KotlinIdentifier::from_dex("receiver");
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Return(Some(KotlinExpr::NonNullAssertion(Box::new(
                KotlinExpr::Name(receiver.clone()),
            )))),
        };

        KotlinExtensionReceiverLowering::new(receiver, true)
            .apply(&mut body)
            .expect("extension receiver lowering");

        assert!(matches!(
            body.root,
            KotlinStmt::Return(Some(KotlinExpr::NonNullAssertion(value)))
                if matches!(value.as_ref(), KotlinExpr::This)
        ));
    }

    #[test]
    fn smart_casts_receiver_on_short_circuit_non_null_edge() {
        let parameter = KotlinIdentifier::from_dex("value");
        let call = KotlinExpr::Call {
            receiver: Some(Box::new(name("value"))),
            owner: None,
            type_arguments: Vec::new(),
            method: KotlinIdentifier::from_dex("hashCode"),
            args: Vec::new().into(),
        };
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Expression(KotlinExpr::Binary {
                left: Box::new(KotlinExpr::Binary {
                    left: Box::new(name("value")),
                    op: KotlinBinaryOp::ReferentialNotEqual,
                    right: Box::new(KotlinExpr::Literal(KotlinLiteral::Null)),
                }),
                op: KotlinBinaryOp::LogicalAnd,
                right: Box::new(call),
            }),
        };

        let changed = KotlinSmartCastLowering::new([parameter])
            .apply(&mut body)
            .expect("smart cast lowering");

        assert!(changed);
        let KotlinStmt::Expression(KotlinExpr::Binary { right, .. }) = body.root else {
            panic!("binary expression")
        };
        let KotlinExpr::Call {
            receiver: Some(receiver),
            ..
        } = *right
        else {
            panic!("receiver call")
        };
        assert!(matches!(*receiver, KotlinExpr::SmartCast(_)));
    }

    #[test]
    fn does_not_smart_cast_written_parameters() {
        let parameter = KotlinIdentifier::from_dex("value");
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Block(vec![
                KotlinStmt::Assign {
                    target: name("value"),
                    op: KotlinAssignOp::Assign,
                    value: KotlinExpr::Literal(KotlinLiteral::Null),
                },
                KotlinStmt::If {
                    condition: KotlinExpr::Binary {
                        left: Box::new(name("value")),
                        op: KotlinBinaryOp::ReferentialNotEqual,
                        right: Box::new(KotlinExpr::Literal(KotlinLiteral::Null)),
                    },
                    then_stmt: Box::new(KotlinStmt::Expression(KotlinExpr::Call {
                        receiver: Some(Box::new(name("value"))),
                        owner: None,
                        type_arguments: Vec::new(),
                        method: KotlinIdentifier::from_dex("hashCode"),
                        args: Vec::new().into(),
                    })),
                    else_stmt: None,
                },
            ]),
        };

        let changed = KotlinSmartCastLowering::new([parameter])
            .apply(&mut body)
            .expect("smart cast lowering");

        assert!(!changed);
    }

    #[test]
    fn smart_casts_after_a_terminal_null_guard() {
        let parameter = KotlinIdentifier::from_dex("value");
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Block(vec![
                KotlinStmt::If {
                    condition: KotlinExpr::Binary {
                        left: Box::new(name("value")),
                        op: KotlinBinaryOp::ReferentialEqual,
                        right: Box::new(KotlinExpr::Literal(KotlinLiteral::Null)),
                    },
                    then_stmt: Box::new(KotlinStmt::Return(None)),
                    else_stmt: None,
                },
                KotlinStmt::Expression(KotlinExpr::Call {
                    receiver: Some(Box::new(name("value"))),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: KotlinIdentifier::from_dex("hashCode"),
                    args: Vec::new().into(),
                }),
            ]),
        };

        let changed = KotlinSmartCastLowering::new([parameter])
            .apply(&mut body)
            .expect("smart cast lowering");

        assert!(changed);
        let KotlinStmt::Block(statements) = body.root else {
            panic!("method block")
        };
        let KotlinStmt::Expression(KotlinExpr::Call {
            receiver: Some(receiver),
            ..
        }) = &statements[1]
        else {
            panic!("receiver call")
        };
        assert!(matches!(receiver.as_ref(), KotlinExpr::SmartCast(_)));
    }

    #[test]
    fn mutable_local_remains_non_null_when_every_definition_is_non_null() {
        let local = KotlinIdentifier::from_dex("value");
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Block(vec![
                KotlinStmt::Variable {
                    binding: Default::default(),
                    ty: KotlinType::source_class("java.lang.String"),
                    name: local.clone(),
                    value: Some(KotlinExpr::Literal(KotlinLiteral::String("first".into()))),
                },
                KotlinStmt::Assign {
                    target: KotlinExpr::Name(local.clone()),
                    op: KotlinAssignOp::Assign,
                    value: KotlinExpr::Literal(KotlinLiteral::String("second".into())),
                },
                KotlinStmt::Return(Some(KotlinExpr::NonNullAssertion(Box::new(
                    KotlinExpr::Name(local),
                )))),
            ]),
        };

        KotlinLocalBindingAnalysis
            .apply(&mut body)
            .expect("local binding analysis");

        let KotlinStmt::Block(statements) = body.root else {
            panic!("method block")
        };
        let KotlinStmt::Variable { binding, .. } = &statements[0] else {
            panic!("local declaration")
        };
        assert!(binding.mutable);
        assert!(!binding.nullable);
        assert!(matches!(
            &statements[2],
            KotlinStmt::Return(Some(KotlinExpr::SmartCast(_)))
        ));
    }

    #[test]
    fn collapses_casts_with_the_same_jvm_erasure() {
        let raw = KotlinType::Class(KotlinClassType {
            segments: vec![KotlinClassTypeSegment {
                name: KotlinIdentifier::from_dex("Iterable"),
                arguments: vec![KotlinTypeArgument::Any],
            }],
        });
        let parameterized = KotlinType::Class(KotlinClassType {
            segments: vec![KotlinClassTypeSegment {
                name: KotlinIdentifier::from_dex("Iterable"),
                arguments: vec![KotlinTypeArgument::Exact(KotlinType::source_class(
                    "java.lang.String",
                ))],
            }],
        });
        let mut body = KotlinMethodBody {
            root: KotlinStmt::Expression(KotlinExpr::Cast {
                ty: parameterized.clone(),
                value: Box::new(KotlinExpr::Cast {
                    ty: raw,
                    value: Box::new(name("values")),
                }),
            }),
        };

        let changed = KotlinSmartCastLowering::new([])
            .apply(&mut body)
            .expect("cast normalization");

        assert!(changed);
        let KotlinStmt::Expression(KotlinExpr::Cast { ty, value }) = body.root else {
            panic!("outer cast")
        };
        assert_eq!(ty, parameterized);
        assert!(matches!(*value, KotlinExpr::Name(_)));
    }
}
