use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{ArgType, MethodDescriptor, MethodReference};
use crate::language::kotlin::{
    KotlinAssignOp, KotlinAstNormalizer, KotlinAstRewriter, KotlinBinaryOp, KotlinExpr,
    KotlinIdentifier, KotlinJvmIntrinsic, KotlinLiteral, KotlinMethodDeclaration,
    KotlinMethodDeclarationKind, KotlinModifier, KotlinStmt,
};

use super::kotlin_model::{KotlinDefaultArgumentLayout, KotlinSourceAbi};

type LoweredMethod = (
    Option<MethodReference>,
    BTreeSet<MethodReference>,
    KotlinMethodDeclaration,
);

struct Recovery {
    primary: usize,
    remove: Vec<usize>,
    values: Vec<(usize, KotlinExpr)>,
}

struct Invocation {
    arguments: Vec<KotlinExpr>,
    dispatch_offset: usize,
}

/// Rejoins a metadata-declared function with its Kotlin/JVM default dispatcher.
///
/// The dispatcher is removed only after its complete ABI and dataflow have
/// been proven: exact descriptor, direct call target, mask tests, forwarded
/// parameters, and one recovered expression for every metadata default.
pub(super) struct KotlinDefaultArguments<'a> {
    source_abi: &'a KotlinSourceAbi,
}

impl<'a> KotlinDefaultArguments<'a> {
    pub(super) fn new(source_abi: &'a KotlinSourceAbi) -> Self {
        Self { source_abi }
    }

    pub(super) fn recover(&self, methods: &mut Vec<LoweredMethod>) {
        let mut recovered = Vec::new();
        for primary in 0..methods.len() {
            let Some(reference) = methods[primary].0.as_ref() else {
                continue;
            };
            let Some(layout) = self.source_abi.declared_default_arguments(reference) else {
                continue;
            };
            let Some(dispatcher) = self.dispatcher(methods, primary, reference, layout) else {
                continue;
            };
            let Some(values) = self.values(&methods[primary], &methods[dispatcher], layout) else {
                continue;
            };
            let Some(mut remove) =
                self.redundant_overloads(methods, primary, dispatcher, reference, &values)
            else {
                continue;
            };
            remove.push(dispatcher);
            recovered.push(Recovery {
                primary,
                remove,
                values,
            });
        }

        let mut removed = BTreeSet::new();
        for recovery in recovered {
            if recovery.remove.iter().any(|index| removed.contains(index)) {
                continue;
            }
            removed.extend(recovery.remove);
            for (parameter, value) in recovery.values {
                methods[recovery.primary].2.parameters[parameter].default_value = Some(value);
            }
        }
        if removed.is_empty() {
            return;
        }
        let mut index = 0usize;
        methods.retain(|_| {
            let keep = !removed.contains(&index);
            index += 1;
            keep
        });
    }

    fn dispatcher(
        &self,
        methods: &[LoweredMethod],
        primary: usize,
        reference: &MethodReference,
        layout: &KotlinDefaultArgumentLayout,
    ) -> Option<usize> {
        let declaration = &methods[primary].2;
        let (name, parameters, return_type, static_dispatcher, kind) = match declaration.kind {
            KotlinMethodDeclarationKind::Method => {
                let is_static = declaration.modifiers.contains(&KotlinModifier::Static);
                let mut parameters = Vec::new();
                if !is_static {
                    parameters.push(reference.owner.clone());
                }
                parameters.extend(reference.descriptor.parameters.iter().cloned());
                parameters.extend(std::iter::repeat_n(ArgType::INT, layout.mask_count));
                parameters.push(ArgType::object("java/lang/Object"));
                (
                    format!("{}$default", reference.name),
                    parameters,
                    reference.descriptor.return_type.clone(),
                    true,
                    KotlinMethodDeclarationKind::Method,
                )
            }
            KotlinMethodDeclarationKind::Constructor => {
                let mut parameters = reference.descriptor.parameters.clone();
                parameters.extend(std::iter::repeat_n(ArgType::INT, layout.mask_count));
                parameters.push(ArgType::object(
                    "kotlin/jvm/internal/DefaultConstructorMarker",
                ));
                (
                    "<init>".to_string(),
                    parameters,
                    ArgType::VOID,
                    false,
                    KotlinMethodDeclarationKind::Constructor,
                )
            }
            KotlinMethodDeclarationKind::ClassInitializer => return None,
        };
        let descriptor = MethodDescriptor {
            parameters,
            return_type,
        };
        let candidates = methods
            .iter()
            .enumerate()
            .filter(|(_, (candidate, invokes, declaration))| {
                let indexed_dispatcher = candidate
                    .as_ref()
                    .is_some_and(|candidate| self.source_abi.is_default_dispatcher(candidate));
                candidate.as_ref().is_some_and(|candidate| {
                    candidate.owner == reference.owner
                        && candidate.name == name
                        && candidate.descriptor == descriptor
                }) && (invokes.contains(reference) || indexed_dispatcher)
                    && (declaration.compiler_generated || indexed_dispatcher)
                    && declaration.modifiers.contains(&KotlinModifier::Static) == static_dispatcher
                    && declaration.kind == kind
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        match candidates.as_slice() {
            [candidate] => Some(*candidate),
            _ => None,
        }
    }

    fn values(
        &self,
        primary: &LoweredMethod,
        dispatcher: &LoweredMethod,
        layout: &KotlinDefaultArgumentLayout,
    ) -> Option<Vec<(usize, KotlinExpr)>> {
        let primary_reference = primary.0.as_ref()?;
        let primary_declaration = &primary.2;
        let dispatcher_declaration = &dispatcher.2;
        let invocation = match primary_declaration.kind {
            KotlinMethodDeclarationKind::Method => self.method_invocation(
                primary_reference,
                primary_declaration,
                dispatcher_declaration,
            )?,
            KotlinMethodDeclarationKind::Constructor => {
                let arguments = DefaultValueFlow::arguments(dispatcher_declaration.body.as_ref()?)?;
                if arguments.len() != primary_reference.descriptor.parameters.len() {
                    return None;
                }
                Invocation {
                    arguments,
                    dispatch_offset: 0,
                }
            }
            KotlinMethodDeclarationKind::ClassInitializer => return None,
        };

        let default_by_parameter = layout
            .parameters
            .iter()
            .map(|parameter| (parameter.parameter, parameter))
            .collect::<BTreeMap<_, _>>();
        let mut substitutions = BTreeMap::new();
        let extension = self
            .source_abi
            .declared_extension_receiver(primary_reference);
        for parameter in 0..primary_reference.descriptor.parameters.len() {
            let source = dispatcher_declaration
                .parameters
                .get(invocation.dispatch_offset + parameter)?
                .name
                .clone();
            if Some(parameter) == extension {
                substitutions.insert(source, KotlinExpr::This);
            } else {
                let target = self.visible_parameter(primary_reference, parameter)?;
                substitutions.insert(
                    source,
                    KotlinExpr::Name(primary_declaration.parameters.get(target)?.name.clone()),
                );
            }
        }

        let mask_start = invocation.dispatch_offset + primary_reference.descriptor.parameters.len();
        let dispatcher_names = dispatcher_declaration
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let source_names = substitutions.keys().cloned().collect::<BTreeSet<_>>();
        let internal_names = dispatcher_names
            .difference(&source_names)
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut values = Vec::new();
        for (parameter, argument) in invocation.arguments.iter().enumerate() {
            let forwarded = &dispatcher_declaration
                .parameters
                .get(invocation.dispatch_offset + parameter)?
                .name;
            let Some(default) = default_by_parameter.get(&parameter) else {
                if !Self::is_name(argument, forwarded) {
                    return None;
                }
                continue;
            };
            let mask = &dispatcher_declaration
                .parameters
                .get(mask_start + default.mask)?
                .name;
            let Some(value) = Self::default_value(argument, forwarded, mask, default.bit) else {
                if !layout.exact && Self::is_name(argument, forwarded) {
                    continue;
                }
                return None;
            };
            let mut substitution = ParameterSubstitution {
                values: &substitutions,
            };
            let value = substitution.rewrite_expression(value);
            if DispatchNames::contains(&value, &internal_names) {
                return None;
            }
            values.push((self.visible_parameter(primary_reference, parameter)?, value));
        }
        (layout.exact && values.len() == layout.parameters.len()
            || !layout.exact && !values.is_empty())
        .then_some(values)
    }

    fn method_invocation(
        &self,
        primary_reference: &MethodReference,
        primary_declaration: &KotlinMethodDeclaration,
        dispatcher: &KotlinMethodDeclaration,
    ) -> Option<Invocation> {
        let call = Self::dispatcher_call(dispatcher)?;
        let KotlinExpr::Call {
            receiver,
            method,
            args,
            ..
        } = Self::proof_value(call)
        else {
            return None;
        };
        if Some(method) != primary_declaration.name.as_ref() {
            return None;
        }

        let is_static = primary_declaration
            .modifiers
            .contains(&KotlinModifier::Static);
        let dispatch_offset = usize::from(!is_static);
        let extension = self
            .source_abi
            .declared_extension_receiver(primary_reference);
        let source_lowered_extension = is_static && extension.is_some();
        let expected_arguments = primary_reference
            .descriptor
            .parameters
            .len()
            .saturating_sub(usize::from(source_lowered_extension));
        if args.len() != expected_arguments {
            return None;
        }
        if source_lowered_extension {
            let receiver_parameter = extension?;
            let expected = dispatcher
                .parameters
                .get(dispatch_offset + receiver_parameter)?
                .name
                .clone();
            if !receiver
                .as_deref()
                .is_some_and(|value| Self::is_name(value, &expected))
            {
                return None;
            }
        } else if is_static {
            if receiver.is_some() {
                return None;
            }
        } else {
            let expected = dispatcher.parameters.first()?.name.clone();
            if !receiver
                .as_deref()
                .is_some_and(|value| Self::is_name(value, &expected))
            {
                return None;
            }
        }

        let mut arguments = Vec::with_capacity(primary_reference.descriptor.parameters.len());
        for parameter in 0..primary_reference.descriptor.parameters.len() {
            let argument = if source_lowered_extension && Some(parameter) == extension {
                receiver.as_deref()?
            } else {
                let argument = if source_lowered_extension {
                    parameter.saturating_sub(usize::from(
                        extension.is_some_and(|extension| parameter > extension),
                    ))
                } else {
                    parameter
                };
                args.get(argument)?
            };
            arguments.push(argument.clone());
        }
        Some(Invocation {
            arguments,
            dispatch_offset,
        })
    }

    fn redundant_overloads(
        &self,
        methods: &[LoweredMethod],
        primary: usize,
        dispatcher: usize,
        reference: &MethodReference,
        values: &[(usize, KotlinExpr)],
    ) -> Option<Vec<usize>> {
        if methods[primary].2.kind != KotlinMethodDeclarationKind::Constructor {
            return self
                .redundant_method_overloads(methods, primary, dispatcher, reference, values);
        }
        let parameter_count = reference.descriptor.parameters.len();
        if values.len() != parameter_count
            || values
                .iter()
                .enumerate()
                .any(|(parameter, (default, _))| *default != parameter)
        {
            return Some(Vec::new());
        }
        let dispatcher_reference = methods[dispatcher].0.as_ref()?;
        let candidates = methods
            .iter()
            .enumerate()
            .filter(|(index, (candidate, invokes, declaration))| {
                *index != primary
                    && *index != dispatcher
                    && candidate.as_ref().is_some_and(|candidate| {
                        candidate.owner == reference.owner
                            && candidate.name == "<init>"
                            && candidate.descriptor.parameters.is_empty()
                            && candidate.descriptor.return_type == ArgType::VOID
                    })
                    && invokes.contains(dispatcher_reference)
                    && declaration.kind == KotlinMethodDeclarationKind::Constructor
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let candidate = match candidates.as_slice() {
            [] => return Some(Vec::new()),
            [candidate] => *candidate,
            _ => return None,
        };
        Some(vec![candidate])
    }

    fn redundant_method_overloads(
        &self,
        methods: &[LoweredMethod],
        primary: usize,
        dispatcher: usize,
        reference: &MethodReference,
        values: &[(usize, KotlinExpr)],
    ) -> Option<Vec<usize>> {
        if self
            .source_abi
            .declared_extension_receiver(reference)
            .is_some()
        {
            return Some(Vec::new());
        }
        let defaults = values
            .iter()
            .map(|(parameter, _)| *parameter)
            .collect::<BTreeSet<_>>();
        let dispatcher_reference = methods[dispatcher].0.as_ref()?;
        let primary_declaration = &methods[primary].2;
        let target_static = primary_declaration
            .modifiers
            .contains(&KotlinModifier::Static);
        let mut remove = Vec::new();
        for (index, (candidate, invokes, declaration)) in methods.iter().enumerate() {
            if index == primary || index == dispatcher || !invokes.contains(dispatcher_reference) {
                continue;
            }
            let Some(candidate) = candidate else {
                continue;
            };
            let parameter_count = candidate.descriptor.parameters.len();
            if candidate.owner != reference.owner
                || candidate.name != reference.name
                || candidate.descriptor.return_type != reference.descriptor.return_type
                || declaration.kind != KotlinMethodDeclarationKind::Method
                || parameter_count >= reference.descriptor.parameters.len()
                || candidate.descriptor.parameters
                    != reference.descriptor.parameters[..parameter_count]
                || !(parameter_count..reference.descriptor.parameters.len())
                    .all(|parameter| defaults.contains(&parameter))
                || !Self::forwards_parameters(declaration, primary_declaration, target_static)
            {
                continue;
            }
            remove.push(index);
        }
        Some(remove)
    }

    fn forwards_parameters(
        overload: &KotlinMethodDeclaration,
        primary: &KotlinMethodDeclaration,
        target_static: bool,
    ) -> bool {
        let Some(call) = overload.body.as_ref().and_then(Self::sole_call) else {
            return false;
        };
        let KotlinExpr::Call {
            receiver,
            method,
            args,
            ..
        } = Self::proof_value(call)
        else {
            return false;
        };
        if Some(method) != primary.name.as_ref()
            || if target_static {
                receiver.is_some()
            } else {
                !receiver
                    .as_deref()
                    .is_some_and(|receiver| matches!(Self::proof_value(receiver), KotlinExpr::This))
            }
        {
            return false;
        }
        let parameters = overload.parameters.iter().collect::<Vec<_>>();
        args.len() == parameters.len()
            && args
                .iter()
                .zip(parameters)
                .all(|(argument, parameter)| Self::is_name(argument, &parameter.name))
    }

    fn sole_call(body: &crate::language::kotlin::KotlinMethodBody) -> Option<&KotlinExpr> {
        Self::returned_call(body).or_else(|| match &body.root {
            KotlinStmt::Expression(expression) => Some(expression),
            KotlinStmt::Block(statements) => match statements.as_slice() {
                [KotlinStmt::Expression(expression)] => Some(expression),
                _ => None,
            },
            _ => None,
        })
    }

    fn visible_parameter(&self, method: &MethodReference, dex_parameter: usize) -> Option<usize> {
        let extension = self.source_abi.declared_extension_receiver(method);
        let mut visible = 0usize;
        for parameter in 0..method.descriptor.parameters.len() {
            if Some(parameter) == extension {
                continue;
            }
            if parameter == dex_parameter {
                return Some(visible);
            }
            visible += 1;
        }
        None
    }

    fn returned_call(body: &crate::language::kotlin::KotlinMethodBody) -> Option<&KotlinExpr> {
        match &body.root {
            KotlinStmt::Return(Some(expression)) => Some(expression),
            KotlinStmt::Block(statements) => {
                let (last, prefix) = statements.split_last()?;
                if !prefix.iter().all(|statement| {
                    matches!(
                        statement,
                        KotlinStmt::Expression(KotlinExpr::JvmIntrinsic {
                            kind: KotlinJvmIntrinsic::ParameterCheck,
                            ..
                        })
                    )
                }) {
                    return None;
                }
                match last {
                    KotlinStmt::Return(Some(expression)) => Some(expression),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn dispatcher_call(dispatcher: &KotlinMethodDeclaration) -> Option<&KotlinExpr> {
        let body = dispatcher.body.as_ref()?;
        let KotlinStmt::Block(statements) = &body.root else {
            return Self::returned_call(body);
        };
        let (last, prefix) = statements.split_last()?;
        let marker = &dispatcher.parameters.last()?.name;
        if !prefix.iter().all(|statement| {
            matches!(
                statement,
                KotlinStmt::Expression(KotlinExpr::JvmIntrinsic {
                    kind: KotlinJvmIntrinsic::ParameterCheck,
                    ..
                })
            ) || Self::marker_guard(statement, marker)
        }) {
            return None;
        }
        match last {
            KotlinStmt::Return(Some(expression)) => Some(expression),
            _ => None,
        }
    }

    fn marker_guard(statement: &KotlinStmt, marker: &KotlinIdentifier) -> bool {
        let KotlinStmt::If {
            condition,
            else_stmt: None,
            ..
        } = statement
        else {
            return false;
        };
        let KotlinExpr::Binary { left, op, right } = Self::proof_value(condition) else {
            return false;
        };
        if !matches!(
            op,
            KotlinBinaryOp::NotEqual | KotlinBinaryOp::ReferentialNotEqual
        ) {
            return false;
        }
        (Self::is_name(left, marker) && Self::is_null(right))
            || (Self::is_null(left) && Self::is_name(right, marker))
    }

    fn default_value(
        argument: &KotlinExpr,
        forwarded: &KotlinIdentifier,
        mask: &KotlinIdentifier,
        bit: u32,
    ) -> Option<KotlinExpr> {
        let mut clear = MaskBitFact {
            mask,
            bit,
            set: false,
        };
        let forwarded_value = clear.rewrite_expression(argument.clone());
        if !Self::is_name(&forwarded_value, forwarded) {
            return None;
        }
        let mut set = MaskBitFact {
            mask,
            bit,
            set: true,
        };
        let value =
            KotlinAstNormalizer::canonicalize_expression(set.rewrite_expression(argument.clone()));
        let forwarded = BTreeSet::from([forwarded.clone()]);
        (!DispatchNames::contains(&value, &forwarded)).then_some(value)
    }

    /// Returns whether the default branch is taken when this predicate is true.
    fn mask_test(condition: &KotlinExpr, mask: &KotlinIdentifier, bit: u32) -> Option<bool> {
        let KotlinExpr::Binary { left, op, right } = Self::proof_value(condition) else {
            return None;
        };
        if !matches!(op, KotlinBinaryOp::Equal | KotlinBinaryOp::NotEqual) {
            return None;
        }
        let masked = if Self::integer(right) == Some(0) {
            left.as_ref()
        } else if Self::integer(left) == Some(0) {
            right.as_ref()
        } else {
            return None;
        };
        let KotlinExpr::Binary {
            left,
            op: KotlinBinaryOp::BitAnd,
            right,
        } = Self::proof_value(masked)
        else {
            return None;
        };
        let matches = (Self::is_name(left, mask) && Self::integer(right) == Some(bit))
            || (Self::is_name(right, mask) && Self::integer(left) == Some(bit));
        matches.then_some(*op == KotlinBinaryOp::NotEqual)
    }

    fn integer(expression: &KotlinExpr) -> Option<u32> {
        match Self::proof_value(expression) {
            KotlinExpr::Literal(KotlinLiteral::Integer(value)) => Some(*value as u32),
            _ => None,
        }
    }

    fn is_name(expression: &KotlinExpr, expected: &KotlinIdentifier) -> bool {
        matches!(Self::proof_value(expression), KotlinExpr::Name(name) if name == expected)
    }

    fn is_null(expression: &KotlinExpr) -> bool {
        matches!(
            Self::proof_value(expression),
            KotlinExpr::Literal(KotlinLiteral::Null)
        )
    }

    fn proof_value(mut expression: &KotlinExpr) -> &KotlinExpr {
        while let KotlinExpr::SmartCast(value) | KotlinExpr::NonNullAssertion(value) = expression {
            expression = value;
        }
        expression
    }
}

/// Symbolically evaluates the straight-line prefix of a default constructor.
///
/// Kotlin dispatchers commonly materialize a default through a local assigned
/// in one or both mask branches before delegating to `this(...)`. This sparse
/// environment keeps only proven local values and joins branch states with a
/// conditional expression. Any statement outside that model rejects recovery.
#[derive(Clone, Default)]
struct DefaultValueFlow {
    values: BTreeMap<KotlinIdentifier, KotlinExpr>,
}

impl DefaultValueFlow {
    fn arguments(body: &crate::language::kotlin::KotlinMethodBody) -> Option<Vec<KotlinExpr>> {
        let KotlinStmt::Block(statements) = &body.root else {
            return None;
        };
        let (terminal, prefix) = statements.split_last()?;
        let KotlinStmt::ConstructorInvocation {
            target: crate::language::kotlin::KotlinConstructorTarget::This,
            args,
        } = terminal
        else {
            return None;
        };
        let mut flow = Self::default();
        for statement in prefix {
            flow.apply(statement)?;
        }
        Some(
            args.iter()
                .cloned()
                .map(|value| flow.resolve(value))
                .collect(),
        )
    }

    fn apply(&mut self, statement: &KotlinStmt) -> Option<()> {
        match statement {
            KotlinStmt::Empty => Some(()),
            KotlinStmt::Block(statements) => {
                for statement in statements {
                    self.apply(statement)?;
                }
                Some(())
            }
            KotlinStmt::Variable {
                name,
                value: Some(value),
                ..
            } => {
                let value = self.resolve(value.clone());
                self.values.insert(name.clone(), value);
                Some(())
            }
            KotlinStmt::Assign {
                target: KotlinExpr::Name(name),
                op: KotlinAssignOp::Assign,
                value,
            } if self.values.contains_key(name) => {
                let value = self.resolve(value.clone());
                self.values.insert(name.clone(), value);
                Some(())
            }
            KotlinStmt::If {
                condition,
                then_stmt,
                else_stmt,
            } => self.apply_branch(condition, then_stmt, else_stmt.as_deref()),
            KotlinStmt::Expression(KotlinExpr::JvmIntrinsic {
                kind: KotlinJvmIntrinsic::ParameterCheck,
                ..
            }) => Some(()),
            _ => None,
        }
    }

    fn apply_branch(
        &mut self,
        condition: &KotlinExpr,
        when_true: &KotlinStmt,
        when_false: Option<&KotlinStmt>,
    ) -> Option<()> {
        let condition = self.resolve(condition.clone());
        let visible = self.values.keys().cloned().collect::<Vec<_>>();
        let mut true_flow = self.clone();
        true_flow.apply(when_true)?;
        let mut false_flow = self.clone();
        if let Some(when_false) = when_false {
            false_flow.apply(when_false)?;
        }
        for name in visible {
            let when_true = true_flow.values.get(&name)?.clone();
            let when_false = false_flow.values.get(&name)?.clone();
            let value = if when_true == when_false {
                when_true
            } else {
                KotlinExpr::Conditional {
                    condition: Box::new(condition.clone()),
                    when_true: Box::new(when_true),
                    when_false: Box::new(when_false),
                }
            };
            self.values.insert(name, value);
        }
        Some(())
    }

    fn resolve(&self, expression: KotlinExpr) -> KotlinExpr {
        let mut substitution = ParameterSubstitution {
            values: &self.values,
        };
        substitution.rewrite_expression(expression)
    }
}

/// Evaluates an expression under a proven state of one default-mask bit.
struct MaskBitFact<'a> {
    mask: &'a KotlinIdentifier,
    bit: u32,
    set: bool,
}

impl KotlinAstRewriter for MaskBitFact<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let Some(predicate_when_set) =
            KotlinDefaultArguments::mask_test(&expression, self.mask, self.bit)
        {
            return KotlinExpr::Literal(KotlinLiteral::Boolean(predicate_when_set == self.set));
        }
        let (condition, when_true, when_false) = match expression {
            KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            } => (condition, when_true, when_false),
            expression => return Self::fold_boolean(expression),
        };
        match KotlinDefaultArguments::proof_value(&condition) {
            KotlinExpr::Literal(KotlinLiteral::Boolean(true)) => *when_true,
            KotlinExpr::Literal(KotlinLiteral::Boolean(false)) => *when_false,
            _ => KotlinExpr::Conditional {
                condition,
                when_true,
                when_false,
            },
        }
    }
}

impl MaskBitFact<'_> {
    fn fold_boolean(expression: KotlinExpr) -> KotlinExpr {
        let (left, op, right) = match expression {
            KotlinExpr::Binary { left, op, right } => (left, op, right),
            expression => return expression,
        };
        let left_boolean = Self::boolean(&left);
        let right_boolean = Self::boolean(&right);
        match (op, left_boolean, right_boolean) {
            (KotlinBinaryOp::LogicalAnd, Some(false), _)
            | (KotlinBinaryOp::LogicalAnd, _, Some(false))
            | (KotlinBinaryOp::LogicalOr, Some(false), Some(false)) => {
                KotlinExpr::Literal(KotlinLiteral::Boolean(false))
            }
            (KotlinBinaryOp::LogicalOr, Some(true), _)
            | (KotlinBinaryOp::LogicalOr, _, Some(true))
            | (KotlinBinaryOp::LogicalAnd, Some(true), Some(true)) => {
                KotlinExpr::Literal(KotlinLiteral::Boolean(true))
            }
            (KotlinBinaryOp::LogicalAnd, Some(true), _)
            | (KotlinBinaryOp::LogicalOr, Some(false), _) => *right,
            (KotlinBinaryOp::LogicalAnd, _, Some(true))
            | (KotlinBinaryOp::LogicalOr, _, Some(false)) => *left,
            (op, _, _) => KotlinExpr::Binary { left, op, right },
        }
    }

    fn boolean(expression: &KotlinExpr) -> Option<bool> {
        match KotlinDefaultArguments::proof_value(expression) {
            KotlinExpr::Literal(KotlinLiteral::Boolean(value)) => Some(*value),
            _ => None,
        }
    }
}

struct ParameterSubstitution<'a> {
    values: &'a BTreeMap<KotlinIdentifier, KotlinExpr>,
}

impl KotlinAstRewriter for ParameterSubstitution<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match expression {
            KotlinExpr::Name(name) => self
                .values
                .get(&name)
                .cloned()
                .unwrap_or(KotlinExpr::Name(name)),
            expression => expression,
        }
    }
}

struct DispatchNames<'a> {
    names: &'a BTreeSet<KotlinIdentifier>,
    found: bool,
}

impl<'a> DispatchNames<'a> {
    fn contains(expression: &KotlinExpr, names: &'a BTreeSet<KotlinIdentifier>) -> bool {
        let mut analysis = Self {
            names,
            found: false,
        };
        analysis.rewrite_expression(expression.clone());
        analysis.found
    }
}

impl KotlinAstRewriter for DispatchNames<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if matches!(&expression, KotlinExpr::Name(name) if self.names.contains(name)) {
            self.found = true;
        }
        expression
    }
}
