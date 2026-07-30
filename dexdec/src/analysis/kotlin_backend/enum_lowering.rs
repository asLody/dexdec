use std::collections::{BTreeMap, BTreeSet};

use crate::ir::ArgType;
use crate::language::kotlin::{
    KotlinAssignOp, KotlinAstRewriter, KotlinConstructorTarget, KotlinEnumConstant, KotlinExpr,
    KotlinFieldDeclaration, KotlinIdentifier, KotlinLiteral, KotlinMethodDeclaration,
    KotlinMethodDeclarationKind, KotlinModifier, KotlinStmt, KotlinType, KotlinTypeDeclaration,
    KotlinTypeDeclarationKind,
};

use super::anonymous_lowering::LoweredNestedType;
use super::kotlin_model::{KotlinClassKind, KotlinClassModel};

pub(super) struct LoweredEnumDeclaration {
    pub constants: Vec<KotlinEnumConstant>,
    pub constant_implementations: Vec<Option<KotlinType>>,
    pub fields: Vec<KotlinFieldDeclaration>,
    pub methods: Vec<KotlinMethodDeclaration>,
}

pub(super) struct EnumDeclarationRecovery;

pub(super) struct EnumSwitchRecovery;

struct ValuesInitializer {
    helper: Option<KotlinIdentifier>,
}

struct EnumConstantInitializer {
    implementation: Option<KotlinType>,
    arguments: Vec<KotlinExpr>,
}

impl EnumDeclarationRecovery {
    pub(super) fn apply(
        class: &KotlinClassModel,
        fields: Vec<KotlinFieldDeclaration>,
        methods: Vec<KotlinMethodDeclaration>,
    ) -> LoweredEnumDeclaration {
        let unchanged = LoweredEnumDeclaration {
            constants: Vec::new(),
            constant_implementations: Vec::new(),
            fields: fields.clone(),
            methods: methods.clone(),
        };
        if class.declaration.kind != KotlinClassKind::Enum {
            return unchanged;
        }

        Self::recover(class, fields, methods).unwrap_or(unchanged)
    }

    fn recover(
        class: &KotlinClassModel,
        fields: Vec<KotlinFieldDeclaration>,
        mut methods: Vec<KotlinMethodDeclaration>,
    ) -> Option<LoweredEnumDeclaration> {
        let constant_indices = class
            .fields
            .iter()
            .enumerate()
            .filter_map(|(index, field)| field.access_flags.is_enum().then_some(index))
            .collect::<Vec<_>>();
        let values_indices = class
            .fields
            .iter()
            .enumerate()
            .filter_map(|(index, field)| {
                (field.access_flags.is_synthetic()
                    && Self::is_values_array(class, &field.field_type))
                .then_some(index)
            })
            .collect::<BTreeSet<_>>();
        let class_initializer = methods
            .iter()
            .position(|method| method.kind == KotlinMethodDeclarationKind::ClassInitializer)?;
        let mut initializer = methods.remove(class_initializer);
        let KotlinStmt::Block(statements) = &mut initializer.body.as_mut()?.root else {
            return None;
        };

        let constant_schedule = Self::constant_schedule(statements, &fields, &constant_indices)?;
        let mut constants = Vec::with_capacity(constant_indices.len());
        let mut constant_implementations = Vec::with_capacity(constant_indices.len());
        for (ordinal, index) in constant_schedule.into_iter().enumerate() {
            let field = fields.get(index)?;
            let initializer = Self::take_constant_initializer(statements, &field.name, ordinal)?;
            constants.push(KotlinEnumConstant {
                annotations: field.annotations.clone(),
                name: field.name.clone(),
                arguments: initializer.arguments,
                body: None,
            });
            constant_implementations.push(initializer.implementation);
        }
        let mut values_helpers = BTreeSet::new();
        for index in &values_indices {
            let field = fields.get(*index)?;
            let removed = Self::remove_values_initializer(statements, &field.name)?;
            if let Some(helper) = removed.helper {
                values_helpers.insert(helper);
            }
        }

        let constant_names = constants
            .iter()
            .map(|constant| constant.name.clone())
            .collect::<Vec<_>>();
        Self::normalize_constructors(&mut methods);
        methods.retain(|method| {
            !Self::is_redundant_constructor(method)
                && !Self::is_implicit_enum_method(method)
                && !Self::is_consumed_values_helper(method, &values_helpers, &constant_names)
        });
        if !statements.is_empty() {
            methods.insert(class_initializer.min(methods.len()), initializer);
        }

        let removed = constant_indices
            .into_iter()
            .chain(values_indices)
            .collect::<BTreeSet<_>>();
        Some(LoweredEnumDeclaration {
            constants,
            constant_implementations,
            fields: fields
                .into_iter()
                .enumerate()
                .filter_map(|(index, field)| (!removed.contains(&index)).then_some(field))
                .collect(),
            methods,
        })
    }

    fn is_values_array(class: &KotlinClassModel, field_type: &ArgType) -> bool {
        let Some(owner) = class.declaration.current_type() else {
            return false;
        };
        matches!(field_type, ArgType::Array(element) if element.as_ref() == &owner)
    }

    fn constant_schedule(
        statements: &[KotlinStmt],
        fields: &[KotlinFieldDeclaration],
        constant_indices: &[usize],
    ) -> Option<Vec<usize>> {
        let by_name = constant_indices
            .iter()
            .copied()
            .map(|index| Some((fields.get(index)?.name.clone(), index)))
            .collect::<Option<BTreeMap<_, _>>>()?;
        let mut scheduled = Vec::with_capacity(constant_indices.len());
        let mut seen = BTreeSet::new();
        for statement in statements {
            let KotlinStmt::Assign {
                target: KotlinExpr::StaticField { name, .. },
                op: KotlinAssignOp::Assign,
                value: KotlinExpr::New { .. },
            } = statement
            else {
                continue;
            };
            let Some(index) = by_name.get(name).copied() else {
                continue;
            };
            if !seen.insert(index) {
                return None;
            }
            scheduled.push(index);
        }
        (scheduled.len() == constant_indices.len()).then_some(scheduled)
    }

    fn take_constant_initializer(
        statements: &mut Vec<KotlinStmt>,
        field: &KotlinIdentifier,
        ordinal: usize,
    ) -> Option<EnumConstantInitializer> {
        let position = statements.iter().position(|statement| {
            matches!(
                statement,
                KotlinStmt::Assign {
                    target: KotlinExpr::StaticField { name, .. },
                    op: KotlinAssignOp::Assign,
                    value: KotlinExpr::New { .. },
                } if name == field
            )
        })?;
        let KotlinStmt::Assign {
            value:
                KotlinExpr::New {
                    ty,
                    mut args,
                    anonymous_body,
                    ..
                },
            ..
        } = statements.get(position)?.clone()
        else {
            return None;
        };
        let start = Self::inline_constant_dependencies(statements, position, &mut args)?;
        statements.drain(start..=position);
        if matches!(
            args.as_slice(),
            [
                KotlinExpr::Literal(KotlinLiteral::String(name)),
                KotlinExpr::Literal(KotlinLiteral::Integer(value)),
                ..
            ] if name.to_string_lossy() == field.to_string() && *value == ordinal as i32
        ) {
            args.drain(..2);
        }
        Some(EnumConstantInitializer {
            implementation: anonymous_body.is_none().then_some(ty),
            arguments: args,
        })
    }

    fn inline_constant_dependencies(
        statements: &[KotlinStmt],
        position: usize,
        arguments: &mut [KotlinExpr],
    ) -> Option<usize> {
        let mut needed = arguments
            .iter()
            .flat_map(Self::local_names)
            .collect::<BTreeSet<_>>();
        if needed.is_empty() {
            return Some(position);
        }

        let mut cursor = position;
        let mut definitions = Vec::new();
        while !needed.is_empty() {
            cursor = cursor.checked_sub(1)?;
            let KotlinStmt::Variable {
                name,
                value: Some(value),
                ..
            } = &statements[cursor]
            else {
                return None;
            };
            if !needed.remove(name)
                || statements[position + 1..]
                    .iter()
                    .any(|statement| StatementNameUse::contains(statement, name))
            {
                return None;
            }
            needed.extend(Self::local_names(value));
            definitions.push((name.clone(), value.clone()));
        }

        definitions.reverse();
        let mut resolved = BTreeMap::new();
        for (name, value) in definitions {
            let value = LocalSubstitution::new(&resolved).rewrite_expression(value);
            resolved.insert(name, value);
        }
        let mut substitution = LocalSubstitution::new(&resolved);
        for argument in arguments {
            *argument = substitution.rewrite_expression(argument.clone());
        }
        Some(cursor)
    }

    fn remove_values_initializer(
        statements: &mut Vec<KotlinStmt>,
        field: &KotlinIdentifier,
    ) -> Option<ValuesInitializer> {
        let Some(position) = statements.iter().position(|statement| {
            matches!(
                statement,
                KotlinStmt::Assign {
                    target: KotlinExpr::StaticField { name, .. },
                    op: KotlinAssignOp::Assign,
                    ..
                } if name == field
            )
        }) else {
            return None;
        };
        let KotlinStmt::Assign { value, .. } = statements.remove(position) else {
            return None;
        };
        let mut helper = Self::static_zero_argument_call(&value).cloned();
        let mut needed = Self::local_names(&value);
        let mut index = position;
        while index != 0 {
            index -= 1;
            let remove = match &statements[index] {
                KotlinStmt::Variable { name, value, .. } if needed.remove(name) => {
                    if let Some(value) = value {
                        Self::merge_values_helper(&mut helper, value)?;
                        needed.extend(Self::local_names(value));
                    }
                    true
                }
                KotlinStmt::Assign { target, value, .. }
                    if Self::assigned_local(target).is_some_and(|name| needed.contains(name)) =>
                {
                    Self::merge_values_helper(&mut helper, value)?;
                    needed.extend(Self::local_names(value));
                    true
                }
                _ => false,
            };
            if remove {
                statements.remove(index);
            }
        }
        needed.is_empty().then_some(ValuesInitializer { helper })
    }

    fn static_zero_argument_call(expression: &KotlinExpr) -> Option<&KotlinIdentifier> {
        match expression {
            KotlinExpr::Call {
                receiver: None,
                owner: Some(_),
                method,
                args,
                ..
            } if args.is_empty() => Some(method),
            _ => None,
        }
    }

    fn merge_values_helper(
        helper: &mut Option<KotlinIdentifier>,
        expression: &KotlinExpr,
    ) -> Option<()> {
        let Some(candidate) = Self::static_zero_argument_call(expression) else {
            return Some(());
        };
        match helper {
            Some(existing) if existing != candidate => None,
            Some(_) => Some(()),
            slot @ None => {
                *slot = Some(candidate.clone());
                Some(())
            }
        }
    }

    fn assigned_local(expression: &KotlinExpr) -> Option<&KotlinIdentifier> {
        match expression {
            KotlinExpr::Name(name) => Some(name),
            KotlinExpr::ArrayAccess { array, .. } => Self::assigned_local(array),
            _ => None,
        }
    }

    fn local_names(expression: &KotlinExpr) -> BTreeSet<KotlinIdentifier> {
        let mut names = BTreeSet::new();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                KotlinExpr::Name(name) => {
                    names.insert(name.clone());
                }
                KotlinExpr::SmartCast(value)
                | KotlinExpr::NonNullAssertion(value)
                | KotlinExpr::JvmIntrinsic {
                    expression: value, ..
                } => pending.push(value),
                KotlinExpr::Field { owner, .. } => pending.push(owner),
                KotlinExpr::StaticField { .. }
                | KotlinExpr::This
                | KotlinExpr::QualifiedThis(_)
                | KotlinExpr::Super
                | KotlinExpr::Literal(_)
                | KotlinExpr::ClassLiteral(_)
                | KotlinExpr::ObjectReference(_) => {}
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
                | KotlinExpr::Update {
                    target: operand, ..
                }
                | KotlinExpr::Cast { value: operand, .. }
                | KotlinExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                KotlinExpr::Binary { left, right, .. } => {
                    pending.extend([left.as_ref(), right.as_ref()]);
                }
                KotlinExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.extend([condition.as_ref(), when_true.as_ref(), when_false.as_ref()]);
                }
                KotlinExpr::Assignment { target, value, .. } => {
                    pending.extend([target.as_ref(), value.as_ref()]);
                }
            }
        }
        names
    }

    fn normalize_constructors(methods: &mut [KotlinMethodDeclaration]) {
        for method in methods
            .iter_mut()
            .filter(|method| method.kind == KotlinMethodDeclarationKind::Constructor)
        {
            method
                .modifiers
                .retain(|modifier| *modifier != KotlinModifier::Private);
            let Some(body) = method.body.as_mut() else {
                continue;
            };
            if let KotlinStmt::Block(statements) = &mut body.root {
                if matches!(
                    statements.first(),
                    Some(KotlinStmt::ConstructorInvocation {
                        target: KotlinConstructorTarget::Super,
                        ..
                    })
                ) {
                    statements.remove(0);
                }
            }
        }
    }

    fn is_redundant_constructor(method: &KotlinMethodDeclaration) -> bool {
        method.kind == KotlinMethodDeclarationKind::Constructor
            && method.annotations.is_empty()
            && method.type_parameters.is_empty()
            && method.parameters.is_empty()
            && method.throws.is_empty()
            && matches!(
                method.body.as_ref().map(|body| &body.root),
                Some(KotlinStmt::Block(statements)) if statements.is_empty()
            )
    }

    fn is_implicit_enum_method(method: &KotlinMethodDeclaration) -> bool {
        if method.kind != KotlinMethodDeclarationKind::Method {
            return false;
        }
        match method.name.as_ref().map(ToString::to_string).as_deref() {
            Some("values") => method.parameters.is_empty(),
            Some("valueOf") => {
                matches!(
                    method.parameters.as_slice(),
                    [parameter] if parameter.ty == KotlinType::source_class("String")
                )
            }
            _ => false,
        }
    }

    fn is_values_helper(method: &KotlinMethodDeclaration, constants: &[KotlinIdentifier]) -> bool {
        if method.kind != KotlinMethodDeclarationKind::Method
            || !method.parameters.is_empty()
            || !method.modifiers.contains(&KotlinModifier::Private)
            || !method.modifiers.contains(&KotlinModifier::Static)
            || !matches!(method.return_type, Some(KotlinType::Array(_)))
        {
            return false;
        }
        let Some(body) = method.body.as_ref() else {
            return false;
        };
        let Some(initializer) = Self::returned_array_initializer(&body.root) else {
            return false;
        };
        initializer.len() == constants.len()
            && initializer
                .iter()
                .zip(constants)
                .all(|(expression, expected)| {
                    matches!(
                        expression,
                        KotlinExpr::StaticField { name, .. } if name == expected
                    )
                })
    }

    fn is_consumed_values_helper(
        method: &KotlinMethodDeclaration,
        helpers: &BTreeSet<KotlinIdentifier>,
        constants: &[KotlinIdentifier],
    ) -> bool {
        method
            .name
            .as_ref()
            .is_some_and(|name| helpers.contains(name))
            && Self::is_values_helper(method, constants)
    }

    fn returned_array_initializer(statement: &KotlinStmt) -> Option<&[KotlinExpr]> {
        let KotlinStmt::Block(statements) = statement else {
            return None;
        };
        match statements.as_slice() {
            [KotlinStmt::Return(Some(KotlinExpr::NewArray { initializer, .. }))] => {
                Some(initializer)
            }
            [KotlinStmt::Variable {
                name,
                value: Some(KotlinExpr::NewArray { initializer, .. }),
                ..
            }, KotlinStmt::Return(Some(KotlinExpr::Name(returned)))]
                if name == returned =>
            {
                Some(initializer)
            }
            _ => None,
        }
    }
}

struct LocalSubstitution<'a> {
    values: &'a BTreeMap<KotlinIdentifier, KotlinExpr>,
}

impl<'a> LocalSubstitution<'a> {
    fn new(values: &'a BTreeMap<KotlinIdentifier, KotlinExpr>) -> Self {
        Self { values }
    }
}

impl KotlinAstRewriter for LocalSubstitution<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        match &expression {
            KotlinExpr::Name(name) => self.values.get(name).cloned().unwrap_or(expression),
            _ => expression,
        }
    }
}

struct StatementNameUse<'a> {
    target: &'a KotlinIdentifier,
    found: bool,
}

impl<'a> StatementNameUse<'a> {
    fn contains(statement: &KotlinStmt, target: &'a KotlinIdentifier) -> bool {
        let mut query = Self {
            target,
            found: false,
        };
        query.rewrite_statement(statement.clone());
        query.found
    }
}

impl KotlinAstRewriter for StatementNameUse<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if matches!(&expression, KotlinExpr::Name(name) if name == self.target) {
            self.found = true;
        }
        expression
    }
}

#[derive(Clone)]
struct EnumSwitchMap {
    field: KotlinIdentifier,
    enum_type: Option<KotlinType>,
    labels: BTreeMap<i32, KotlinExpr>,
}

impl EnumSwitchMap {
    fn owns(&self, field: &KotlinIdentifier) -> bool {
        self.field == *field
    }

    fn accepts_enum_type(&self, candidate: &KotlinType) -> bool {
        let Some(expected) = &self.enum_type else {
            return false;
        };
        if expected == candidate {
            return true;
        }
        let (KotlinType::Class(expected), KotlinType::Class(candidate)) = (expected, candidate)
        else {
            return false;
        };
        expected.segments.last().map(|segment| &segment.name)
            == candidate.segments.last().map(|segment| &segment.name)
    }
}

struct EnumSwitchMaps {
    maps: Vec<EnumSwitchMap>,
}

impl EnumSwitchRecovery {
    pub(super) fn apply(
        declaration: &mut KotlinTypeDeclaration,
        mut nested: Vec<LoweredNestedType>,
    ) -> Vec<LoweredNestedType> {
        let mut index = 0;
        while index < nested.len() {
            let Some(maps) = EnumSwitchMaps::analyze(&nested[index]) else {
                index += 1;
                continue;
            };
            let uses = maps.references_in(declaration)
                + nested
                    .iter()
                    .enumerate()
                    .filter(|(candidate, _)| *candidate != index)
                    .map(|(_, nested)| maps.references_in(&nested.declaration))
                    .sum::<usize>();
            if uses == 0 {
                index += 1;
                continue;
            }

            let mut recovery = EnumSwitchStatementRecovery {
                maps: &maps.maps,
                rewritten: 0,
            };
            Self::rewrite_declaration(declaration, &mut recovery);
            for (candidate, nested) in nested.iter_mut().enumerate() {
                if candidate != index {
                    Self::rewrite_declaration(&mut nested.declaration, &mut recovery);
                }
            }
            let remaining = maps.references_in(declaration)
                + nested
                    .iter()
                    .enumerate()
                    .filter(|(candidate, _)| *candidate != index)
                    .map(|(_, nested)| maps.references_in(&nested.declaration))
                    .sum::<usize>();
            if recovery.rewritten != 0 && remaining == 0 {
                nested.remove(index);
            } else {
                index += 1;
            }
        }
        nested
    }

    fn rewrite_declaration(
        declaration: &mut KotlinTypeDeclaration,
        rewriter: &mut impl KotlinAstRewriter,
    ) {
        for field in &mut declaration.fields {
            field.initializer = field
                .initializer
                .take()
                .map(|initializer| rewriter.rewrite_expression(initializer));
        }
        for method in &mut declaration.methods {
            if let Some(body) = &mut method.body {
                rewriter.rewrite_body(body);
            }
        }
    }
}

impl EnumSwitchMaps {
    fn analyze(candidate: &LoweredNestedType) -> Option<Self> {
        let declaration = &candidate.declaration;
        if declaration.kind != KotlinTypeDeclarationKind::Class
            || !declaration.enum_constants.is_empty()
            || !declaration.nested.is_empty()
            || declaration.fields.is_empty()
        {
            return None;
        }
        let mut maps = declaration
            .fields
            .iter()
            .map(|field| {
                if !field.modifiers.contains(&KotlinModifier::Static)
                    || !field.modifiers.contains(&KotlinModifier::Final)
                    || !matches!(
                        &field.ty,
                        KotlinType::Array(element) if element.as_type() == &KotlinType::int()
                    )
                {
                    return None;
                }
                let enum_type = match field.initializer.as_ref() {
                    Some(initializer) => Some(Self::enum_array_domain(initializer)?),
                    None => None,
                };
                Some(EnumSwitchMap {
                    field: field.name.clone(),
                    enum_type,
                    labels: BTreeMap::new(),
                })
            })
            .collect::<Option<Vec<_>>>()?;

        let [initializer] = declaration.methods.as_slice() else {
            return None;
        };
        if initializer.kind != KotlinMethodDeclarationKind::ClassInitializer {
            return None;
        }
        let KotlinStmt::Block(statements) = &initializer.body.as_ref()?.root else {
            return None;
        };
        for statement in statements {
            if matches!(statement, KotlinStmt::Empty) {
                continue;
            }
            if let Some((field, enum_type)) = Self::array_initializer(statement) {
                let map = maps.iter_mut().find(|map| map.field == field)?;
                if map
                    .enum_type
                    .replace(enum_type.clone())
                    .is_some_and(|existing| existing != enum_type)
                {
                    return None;
                }
                continue;
            }
            let (field, enum_type, constant, label) = Self::switch_map_assignment(statement)?;
            let map = maps.iter_mut().find(|map| map.field == field)?;
            if !map.accepts_enum_type(&enum_type)
                || map
                    .labels
                    .insert(label, KotlinExpr::Name(constant))
                    .is_some()
            {
                return None;
            }
        }
        maps.iter()
            .all(|map| map.enum_type.is_some() && !map.labels.is_empty())
            .then_some(Self { maps })
    }

    fn array_initializer(statement: &KotlinStmt) -> Option<(KotlinIdentifier, KotlinType)> {
        let KotlinStmt::Assign {
            target: KotlinExpr::StaticField { name, .. },
            op: KotlinAssignOp::Assign,
            value,
        } = statement
        else {
            return None;
        };
        Some((name.clone(), Self::enum_array_domain(value)?))
    }

    fn enum_array_domain(initializer: &KotlinExpr) -> Option<KotlinType> {
        let KotlinExpr::NewArray {
            element_type,
            dimensions,
            initializer,
        } = initializer
        else {
            return None;
        };
        if element_type != &KotlinType::int() || !initializer.is_empty() {
            return None;
        }
        let [KotlinExpr::Field {
            owner,
            name: length,
        }] = dimensions.as_slice()
        else {
            return None;
        };
        if length.to_string() != "length" {
            return None;
        }
        let KotlinExpr::Call {
            receiver: None,
            owner: Some(enum_type),
            method,
            args,
            ..
        } = owner.as_ref()
        else {
            return None;
        };
        (method.to_string() == "values" && args.is_empty()).then(|| enum_type.clone())
    }

    fn switch_map_assignment(
        statement: &KotlinStmt,
    ) -> Option<(KotlinIdentifier, KotlinType, KotlinIdentifier, i32)> {
        let KotlinStmt::Try {
            body,
            catches,
            finally: None,
        } = statement
        else {
            return None;
        };
        let [catch] = catches.as_slice() else {
            return None;
        };
        if catch.types.len() != 1
            || catch.types[0].to_string() != "NoSuchFieldError"
            || !Self::is_empty(&catch.body)
        {
            return None;
        }
        let KotlinStmt::Assign {
            target: KotlinExpr::ArrayAccess { array, index },
            op: KotlinAssignOp::Assign,
            value: KotlinExpr::Literal(KotlinLiteral::Integer(label)),
        } = Self::single_statement(body)?
        else {
            return None;
        };
        let KotlinExpr::StaticField { name: field, .. } = array.as_ref() else {
            return None;
        };
        if *label <= 0 {
            return None;
        }
        let KotlinExpr::Call {
            receiver: Some(receiver),
            owner: None,
            method,
            args,
            ..
        } = index.as_ref()
        else {
            return None;
        };
        if method.to_string() != "ordinal" || !args.is_empty() {
            return None;
        }
        let KotlinExpr::StaticField {
            owner: enum_type,
            name: constant,
        } = receiver.as_ref()
        else {
            return None;
        };
        Some((field.clone(), enum_type.clone(), constant.clone(), *label))
    }

    fn single_statement(statement: &KotlinStmt) -> Option<&KotlinStmt> {
        match statement {
            KotlinStmt::Block(statements) => {
                let [statement] = statements.as_slice() else {
                    return None;
                };
                Some(statement)
            }
            statement => Some(statement),
        }
    }

    fn is_empty(statement: &KotlinStmt) -> bool {
        matches!(statement, KotlinStmt::Empty)
            || matches!(statement, KotlinStmt::Block(statements) if statements.is_empty())
    }

    fn references_in(&self, declaration: &KotlinTypeDeclaration) -> usize {
        let mut counter = EnumSwitchMapReferences {
            maps: &self.maps,
            count: 0,
        };
        EnumSwitchRecovery::rewrite_declaration(&mut declaration.clone(), &mut counter);
        counter.count
    }
}

struct EnumSwitchMapReferences<'a> {
    maps: &'a [EnumSwitchMap],
    count: usize,
}

impl KotlinAstRewriter for EnumSwitchMapReferences<'_> {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::StaticField { name, .. } = &expression {
            if self.maps.iter().any(|map| map.owns(name)) {
                self.count += 1;
            }
        }
        expression
    }
}

struct EnumSwitchStatementRecovery<'a> {
    maps: &'a [EnumSwitchMap],
    rewritten: usize,
}

impl KotlinAstRewriter for EnumSwitchStatementRecovery<'_> {
    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        let KotlinStmt::Switch {
            label,
            selector,
            cases,
        } = &statement
        else {
            return statement;
        };
        let KotlinExpr::ArrayAccess { array, index } = selector else {
            return statement;
        };
        let KotlinExpr::StaticField { name, .. } = array.as_ref() else {
            return statement;
        };
        let Some(map) = self.maps.iter().find(|map| map.owns(name)) else {
            return statement;
        };
        let KotlinExpr::Call {
            receiver: Some(receiver),
            owner: None,
            method,
            args,
            ..
        } = index.as_ref()
        else {
            return statement;
        };
        if method.to_string() != "ordinal" || !args.is_empty() {
            return statement;
        }

        let mut recovered = cases.clone();
        for case in &mut recovered {
            for case_label in &mut case.labels {
                let KotlinExpr::Literal(KotlinLiteral::Integer(value)) = case_label else {
                    return statement;
                };
                let Some(enum_constant) = map.labels.get(value) else {
                    return statement;
                };
                *case_label = enum_constant.clone();
            }
        }
        self.rewritten += 1;
        KotlinStmt::Switch {
            label: label.clone(),
            selector: receiver.as_ref().clone(),
            cases: recovered,
        }
    }
}
