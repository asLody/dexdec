use std::collections::{BTreeMap, BTreeSet};

use crate::ir::ArgType;
use crate::language::java::{
    JavaAssignOp, JavaAstRewriter, JavaConstructorTarget, JavaEnumConstant, JavaExpr,
    JavaFieldDeclaration, JavaIdentifier, JavaLiteral, JavaMethodDeclaration,
    JavaMethodDeclarationKind, JavaModifier, JavaStmt, JavaType, JavaTypeDeclaration,
    JavaTypeDeclarationKind,
};

use super::anonymous_lowering::LoweredNestedType;
use super::java_model::{JavaClassKind, JavaClassModel};

pub(super) struct LoweredEnumDeclaration {
    pub constants: Vec<JavaEnumConstant>,
    pub constant_implementations: Vec<Option<JavaType>>,
    pub fields: Vec<JavaFieldDeclaration>,
    pub methods: Vec<JavaMethodDeclaration>,
}

pub(super) struct EnumDeclarationRecovery;

pub(super) struct EnumSwitchRecovery;

struct ValuesInitializer {
    helper: Option<JavaIdentifier>,
}

struct EnumConstantInitializer {
    implementation: Option<JavaType>,
    arguments: Vec<JavaExpr>,
}

impl EnumDeclarationRecovery {
    pub(super) fn apply(
        class: &JavaClassModel,
        fields: Vec<JavaFieldDeclaration>,
        methods: Vec<JavaMethodDeclaration>,
    ) -> LoweredEnumDeclaration {
        let unchanged = LoweredEnumDeclaration {
            constants: Vec::new(),
            constant_implementations: Vec::new(),
            fields: fields.clone(),
            methods: methods.clone(),
        };
        if class.declaration.kind != JavaClassKind::Enum {
            return unchanged;
        }

        Self::recover(class, fields, methods).unwrap_or(unchanged)
    }

    fn recover(
        class: &JavaClassModel,
        fields: Vec<JavaFieldDeclaration>,
        mut methods: Vec<JavaMethodDeclaration>,
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
            .position(|method| method.kind == JavaMethodDeclarationKind::ClassInitializer)?;
        let mut initializer = methods.remove(class_initializer);
        let JavaStmt::Block(statements) = &mut initializer.body.as_mut()?.root else {
            return None;
        };

        let constant_schedule = Self::constant_schedule(statements, &fields, &constant_indices)?;
        let mut constants = Vec::with_capacity(constant_indices.len());
        let mut constant_implementations = Vec::with_capacity(constant_indices.len());
        for (ordinal, index) in constant_schedule.into_iter().enumerate() {
            let field = fields.get(index)?;
            let initializer = Self::take_constant_initializer(statements, &field.name, ordinal)?;
            constants.push(JavaEnumConstant {
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

    fn is_values_array(class: &JavaClassModel, field_type: &ArgType) -> bool {
        let Some(owner) = class.declaration.current_type() else {
            return false;
        };
        matches!(field_type, ArgType::Array(element) if element.as_ref() == &owner)
    }

    fn constant_schedule(
        statements: &[JavaStmt],
        fields: &[JavaFieldDeclaration],
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
            let JavaStmt::Assign {
                target: JavaExpr::StaticField { name, .. },
                op: JavaAssignOp::Assign,
                value: JavaExpr::New { .. },
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
        statements: &mut Vec<JavaStmt>,
        field: &JavaIdentifier,
        ordinal: usize,
    ) -> Option<EnumConstantInitializer> {
        let position = statements.iter().position(|statement| {
            matches!(
                statement,
                JavaStmt::Assign {
                    target: JavaExpr::StaticField { name, .. },
                    op: JavaAssignOp::Assign,
                    value: JavaExpr::New { .. },
                } if name == field
            )
        })?;
        let JavaStmt::Assign {
            value:
                JavaExpr::New {
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
                JavaExpr::Literal(JavaLiteral::String(name)),
                JavaExpr::Literal(JavaLiteral::Integer(value)),
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
        statements: &[JavaStmt],
        position: usize,
        arguments: &mut [JavaExpr],
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
            let JavaStmt::Variable {
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
        statements: &mut Vec<JavaStmt>,
        field: &JavaIdentifier,
    ) -> Option<ValuesInitializer> {
        let Some(position) = statements.iter().position(|statement| {
            matches!(
                statement,
                JavaStmt::Assign {
                    target: JavaExpr::StaticField { name, .. },
                    op: JavaAssignOp::Assign,
                    ..
                } if name == field
            )
        }) else {
            return None;
        };
        let JavaStmt::Assign { value, .. } = statements.remove(position) else {
            return None;
        };
        let mut helper = Self::static_zero_argument_call(&value).cloned();
        let mut needed = Self::local_names(&value);
        let mut index = position;
        while index != 0 {
            index -= 1;
            let remove = match &statements[index] {
                JavaStmt::Variable { name, value, .. } if needed.remove(name) => {
                    if let Some(value) = value {
                        Self::merge_values_helper(&mut helper, value)?;
                        needed.extend(Self::local_names(value));
                    }
                    true
                }
                JavaStmt::Assign { target, value, .. }
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

    fn static_zero_argument_call(expression: &JavaExpr) -> Option<&JavaIdentifier> {
        match expression {
            JavaExpr::Call {
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
        helper: &mut Option<JavaIdentifier>,
        expression: &JavaExpr,
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

    fn assigned_local(expression: &JavaExpr) -> Option<&JavaIdentifier> {
        match expression {
            JavaExpr::Name(name) => Some(name),
            JavaExpr::ArrayAccess { array, .. } => Self::assigned_local(array),
            _ => None,
        }
    }

    fn local_names(expression: &JavaExpr) -> BTreeSet<JavaIdentifier> {
        let mut names = BTreeSet::new();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                JavaExpr::Name(name) => {
                    names.insert(name.clone());
                }
                JavaExpr::Field { owner, .. } => pending.push(owner),
                JavaExpr::StaticField { .. }
                | JavaExpr::This
                | JavaExpr::QualifiedThis(_)
                | JavaExpr::Super
                | JavaExpr::Literal(_)
                | JavaExpr::ClassLiteral(_) => {}
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
                | JavaExpr::Update {
                    target: operand, ..
                }
                | JavaExpr::Cast { value: operand, .. }
                | JavaExpr::InstanceOf { value: operand, .. } => pending.push(operand),
                JavaExpr::Binary { left, right, .. } => {
                    pending.extend([left.as_ref(), right.as_ref()]);
                }
                JavaExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                } => {
                    pending.extend([condition.as_ref(), when_true.as_ref(), when_false.as_ref()]);
                }
                JavaExpr::Assignment { target, value, .. } => {
                    pending.extend([target.as_ref(), value.as_ref()]);
                }
            }
        }
        names
    }

    fn normalize_constructors(methods: &mut [JavaMethodDeclaration]) {
        for method in methods
            .iter_mut()
            .filter(|method| method.kind == JavaMethodDeclarationKind::Constructor)
        {
            method
                .modifiers
                .retain(|modifier| *modifier != JavaModifier::Private);
            let Some(body) = method.body.as_mut() else {
                continue;
            };
            if let JavaStmt::Block(statements) = &mut body.root {
                if matches!(
                    statements.first(),
                    Some(JavaStmt::ConstructorInvocation {
                        target: JavaConstructorTarget::Super,
                        ..
                    })
                ) {
                    statements.remove(0);
                }
            }
        }
    }

    fn is_redundant_constructor(method: &JavaMethodDeclaration) -> bool {
        method.kind == JavaMethodDeclarationKind::Constructor
            && method.annotations.is_empty()
            && method.type_parameters.is_empty()
            && method.parameters.is_empty()
            && method.throws.is_empty()
            && matches!(
                method.body.as_ref().map(|body| &body.root),
                Some(JavaStmt::Block(statements)) if statements.is_empty()
            )
    }

    fn is_implicit_enum_method(method: &JavaMethodDeclaration) -> bool {
        if method.kind != JavaMethodDeclarationKind::Method {
            return false;
        }
        match method.name.as_ref().map(ToString::to_string).as_deref() {
            Some("values") => method.parameters.is_empty(),
            Some("valueOf") => {
                matches!(
                    method.parameters.as_slice(),
                    [parameter] if parameter.ty == JavaType::source_class("String")
                )
            }
            _ => false,
        }
    }

    fn is_values_helper(method: &JavaMethodDeclaration, constants: &[JavaIdentifier]) -> bool {
        if method.kind != JavaMethodDeclarationKind::Method
            || !method.parameters.is_empty()
            || !method.modifiers.contains(&JavaModifier::Private)
            || !method.modifiers.contains(&JavaModifier::Static)
            || !matches!(method.return_type, Some(JavaType::Array(_)))
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
                        JavaExpr::StaticField { name, .. } if name == expected
                    )
                })
    }

    fn is_consumed_values_helper(
        method: &JavaMethodDeclaration,
        helpers: &BTreeSet<JavaIdentifier>,
        constants: &[JavaIdentifier],
    ) -> bool {
        method
            .name
            .as_ref()
            .is_some_and(|name| helpers.contains(name))
            && Self::is_values_helper(method, constants)
    }

    fn returned_array_initializer(statement: &JavaStmt) -> Option<&[JavaExpr]> {
        let JavaStmt::Block(statements) = statement else {
            return None;
        };
        match statements.as_slice() {
            [JavaStmt::Return(Some(JavaExpr::NewArray { initializer, .. }))] => Some(initializer),
            [JavaStmt::Variable {
                name,
                value: Some(JavaExpr::NewArray { initializer, .. }),
                ..
            }, JavaStmt::Return(Some(JavaExpr::Name(returned)))]
                if name == returned =>
            {
                Some(initializer)
            }
            _ => None,
        }
    }
}

struct LocalSubstitution<'a> {
    values: &'a BTreeMap<JavaIdentifier, JavaExpr>,
}

impl<'a> LocalSubstitution<'a> {
    fn new(values: &'a BTreeMap<JavaIdentifier, JavaExpr>) -> Self {
        Self { values }
    }
}

impl JavaAstRewriter for LocalSubstitution<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match &expression {
            JavaExpr::Name(name) => self.values.get(name).cloned().unwrap_or(expression),
            _ => expression,
        }
    }
}

struct StatementNameUse<'a> {
    target: &'a JavaIdentifier,
    found: bool,
}

impl<'a> StatementNameUse<'a> {
    fn contains(statement: &JavaStmt, target: &'a JavaIdentifier) -> bool {
        let mut query = Self {
            target,
            found: false,
        };
        query.rewrite_statement(statement.clone());
        query.found
    }
}

impl JavaAstRewriter for StatementNameUse<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if matches!(&expression, JavaExpr::Name(name) if name == self.target) {
            self.found = true;
        }
        expression
    }
}

#[derive(Clone)]
struct EnumSwitchMap {
    field: JavaIdentifier,
    enum_type: Option<JavaType>,
    labels: BTreeMap<i32, JavaExpr>,
}

impl EnumSwitchMap {
    fn owns(&self, field: &JavaIdentifier) -> bool {
        self.field == *field
    }

    fn accepts_enum_type(&self, candidate: &JavaType) -> bool {
        let Some(expected) = &self.enum_type else {
            return false;
        };
        if expected == candidate {
            return true;
        }
        let (JavaType::Class(expected), JavaType::Class(candidate)) = (expected, candidate) else {
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
        declaration: &mut JavaTypeDeclaration,
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
        declaration: &mut JavaTypeDeclaration,
        rewriter: &mut impl JavaAstRewriter,
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
        if declaration.kind != JavaTypeDeclarationKind::Class
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
                if !field.modifiers.contains(&JavaModifier::Static)
                    || !field.modifiers.contains(&JavaModifier::Final)
                    || !matches!(
                        &field.ty,
                        JavaType::Array(element) if element.as_ref() == &JavaType::int()
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
        if initializer.kind != JavaMethodDeclarationKind::ClassInitializer {
            return None;
        }
        let JavaStmt::Block(statements) = &initializer.body.as_ref()?.root else {
            return None;
        };
        for statement in statements {
            if matches!(statement, JavaStmt::Empty) {
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
                || map.labels.insert(label, JavaExpr::Name(constant)).is_some()
            {
                return None;
            }
        }
        maps.iter()
            .all(|map| map.enum_type.is_some() && !map.labels.is_empty())
            .then_some(Self { maps })
    }

    fn array_initializer(statement: &JavaStmt) -> Option<(JavaIdentifier, JavaType)> {
        let JavaStmt::Assign {
            target: JavaExpr::StaticField { name, .. },
            op: JavaAssignOp::Assign,
            value,
        } = statement
        else {
            return None;
        };
        Some((name.clone(), Self::enum_array_domain(value)?))
    }

    fn enum_array_domain(initializer: &JavaExpr) -> Option<JavaType> {
        let JavaExpr::NewArray {
            element_type,
            dimensions,
            initializer,
        } = initializer
        else {
            return None;
        };
        if element_type != &JavaType::int() || !initializer.is_empty() {
            return None;
        }
        let [JavaExpr::Field {
            owner,
            name: length,
        }] = dimensions.as_slice()
        else {
            return None;
        };
        if length.to_string() != "length" {
            return None;
        }
        let JavaExpr::Call {
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
        statement: &JavaStmt,
    ) -> Option<(JavaIdentifier, JavaType, JavaIdentifier, i32)> {
        let JavaStmt::Try {
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
        let JavaStmt::Assign {
            target: JavaExpr::ArrayAccess { array, index },
            op: JavaAssignOp::Assign,
            value: JavaExpr::Literal(JavaLiteral::Integer(label)),
        } = Self::single_statement(body)?
        else {
            return None;
        };
        let JavaExpr::StaticField { name: field, .. } = array.as_ref() else {
            return None;
        };
        if *label <= 0 {
            return None;
        }
        let JavaExpr::Call {
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
        let JavaExpr::StaticField {
            owner: enum_type,
            name: constant,
        } = receiver.as_ref()
        else {
            return None;
        };
        Some((field.clone(), enum_type.clone(), constant.clone(), *label))
    }

    fn single_statement(statement: &JavaStmt) -> Option<&JavaStmt> {
        match statement {
            JavaStmt::Block(statements) => {
                let [statement] = statements.as_slice() else {
                    return None;
                };
                Some(statement)
            }
            statement => Some(statement),
        }
    }

    fn is_empty(statement: &JavaStmt) -> bool {
        matches!(statement, JavaStmt::Empty)
            || matches!(statement, JavaStmt::Block(statements) if statements.is_empty())
    }

    fn references_in(&self, declaration: &JavaTypeDeclaration) -> usize {
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

impl JavaAstRewriter for EnumSwitchMapReferences<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if let JavaExpr::StaticField { name, .. } = &expression {
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

impl JavaAstRewriter for EnumSwitchStatementRecovery<'_> {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        let JavaStmt::Switch {
            label,
            selector,
            cases,
        } = &statement
        else {
            return statement;
        };
        let JavaExpr::ArrayAccess { array, index } = selector else {
            return statement;
        };
        let JavaExpr::StaticField { name, .. } = array.as_ref() else {
            return statement;
        };
        let Some(map) = self.maps.iter().find(|map| map.owns(name)) else {
            return statement;
        };
        let JavaExpr::Call {
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
                let JavaExpr::Literal(JavaLiteral::Integer(value)) = case_label else {
                    return statement;
                };
                let Some(enum_constant) = map.labels.get(value) else {
                    return statement;
                };
                *case_label = enum_constant.clone();
            }
        }
        self.rewritten += 1;
        JavaStmt::Switch {
            label: label.clone(),
            selector: receiver.as_ref().clone(),
            cases: recovered,
        }
    }
}
