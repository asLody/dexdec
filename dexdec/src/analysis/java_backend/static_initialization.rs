use crate::language::java::{
    JavaAssignOp, JavaAstRewriter, JavaExpr, JavaFieldDeclaration, JavaIdentifier, JavaLiteral,
    JavaMethodBody, JavaMethodDeclaration, JavaMethodDeclarationKind, JavaModifier, JavaNameScope,
    JavaPrimitiveType, JavaStmt, JavaType, JavaTypeDeclaration, JavaTypeDeclarationKind,
};

/// Recovers the direct-assignment prefix of `<clinit>` as field initializers.
///
/// The recovered fields are ordered by the executable schedule, not by DEX
/// field-table order. No executable statement is crossed.
pub(super) struct StaticInitializationRecovery;

impl StaticInitializationRecovery {
    pub(super) fn apply(declaration: &mut JavaTypeDeclaration) {
        let Some(initializer_index) = declaration
            .methods
            .iter()
            .position(|method| method.kind == JavaMethodDeclarationKind::ClassInitializer)
        else {
            return;
        };
        let mut method_names = JavaNameScope::default();
        for name in declaration
            .methods
            .iter()
            .filter_map(|method| method.name.clone())
        {
            method_names.reserve(name);
        }
        let Some(body) = declaration.methods[initializer_index].body.as_mut() else {
            return;
        };
        let JavaStmt::Block(statements) = &mut body.root else {
            return;
        };
        if declaration.kind.is_interface() {
            InterfaceInitialization::inline_replayable_locals(statements);
        }
        let interface_snapshot = declaration
            .kind
            .is_interface()
            .then(|| (declaration.fields.clone(), statements.clone()));

        let mut assignments = Vec::new();
        let mut assigned_fields = std::collections::BTreeSet::new();
        let mut consumed = 0usize;
        while consumed < statements.len() {
            let Some(fact) = InitializationFact::analyze(&statements[consumed..]) else {
                break;
            };
            let Some(field_index) = declaration.fields.iter().position(|field| {
                field.name == fact.field
                    && (field.initializer.is_none() || Self::is_default_initializer(field))
                    && field.modifiers.contains(&JavaModifier::Static)
            }) else {
                break;
            };
            if !assigned_fields.insert(field_index) {
                break;
            }
            assignments.push((field_index, fact.value));
            consumed += fact.consumed;
        }
        if !assignments.is_empty() {
            let insertion_index = assignments
                .iter()
                .map(|(field_index, _)| *field_index)
                .min()
                .unwrap();
            let mut recovered = assignments
                .iter()
                .map(|(field_index, value)| {
                    let mut field = declaration.fields[*field_index].clone();
                    field.initializer = Some(value.clone());
                    field
                })
                .collect::<Vec<JavaFieldDeclaration>>();
            let selected = assignments
                .into_iter()
                .map(|(field_index, _)| field_index)
                .collect::<std::collections::BTreeSet<_>>();
            declaration.fields = declaration
                .fields
                .drain(..)
                .enumerate()
                .filter_map(|(index, field)| (!selected.contains(&index)).then_some(field))
                .collect();
            declaration
                .fields
                .splice(insertion_index..insertion_index, recovered.drain(..));
            statements.drain(..consumed);
        }

        if declaration.kind.is_interface() {
            if statements.is_empty() {
                declaration.methods.remove(initializer_index);
                return;
            }
            if let Some(initialization) = InterfaceInitialization::recover(
                &declaration.name,
                &mut declaration.fields,
                statements,
                &mut method_names,
            ) {
                declaration.methods[initializer_index] = initialization;
                return;
            }
            if let Some((fields, original_statements)) = interface_snapshot {
                declaration.fields = fields;
                *statements = original_statements;
                let mut type_names = JavaNameScope::default();
                type_names.reserve(declaration.name.clone());
                for nested in &declaration.nested {
                    type_names.reserve(nested.name.clone());
                }
                let holder_name =
                    type_names.claim(JavaIdentifier::from_dex("DexdecStaticInitialization"));
                if let Some(holder) = InterfaceInitialization::recover_with_holder(
                    &declaration.name,
                    holder_name,
                    &mut declaration.fields,
                    statements,
                ) {
                    declaration.methods.remove(initializer_index);
                    declaration.nested.push(holder);
                    return;
                }
            }
        }

        let remove_initializer = statements.is_empty();
        let mut writes = StaticInitializerWrites::new(
            declaration.name.clone(),
            declaration
                .fields
                .iter()
                .map(|field| field.name.clone())
                .collect(),
        );
        writes.rewrite_body(body);
        for field in &mut declaration.fields {
            if writes.fields.contains(&field.name)
                && field.modifiers.contains(&JavaModifier::Static)
                && field.modifiers.contains(&JavaModifier::Final)
                && Self::is_default_initializer(field)
            {
                field.initializer = None;
            }
        }
        if remove_initializer {
            declaration.methods.remove(initializer_index);
        }
    }

    fn is_default_initializer(field: &JavaFieldDeclaration) -> bool {
        match (&field.ty, field.initializer.as_ref()) {
            (
                JavaType::Class(_) | JavaType::Array(_),
                Some(JavaExpr::Literal(JavaLiteral::Null)),
            ) => true,
            (
                JavaType::Primitive(JavaPrimitiveType::Boolean),
                Some(JavaExpr::Literal(JavaLiteral::Boolean(false))),
            ) => true,
            (
                JavaType::Primitive(
                    JavaPrimitiveType::Byte
                    | JavaPrimitiveType::Short
                    | JavaPrimitiveType::Char
                    | JavaPrimitiveType::Int,
                ),
                Some(JavaExpr::Literal(JavaLiteral::Integer(0))),
            ) => true,
            (
                JavaType::Primitive(JavaPrimitiveType::Char),
                Some(JavaExpr::Literal(JavaLiteral::Character(0))),
            ) => true,
            (
                JavaType::Primitive(JavaPrimitiveType::Long),
                Some(JavaExpr::Literal(JavaLiteral::Long(0))),
            ) => true,
            (
                JavaType::Primitive(JavaPrimitiveType::Float),
                Some(JavaExpr::Literal(JavaLiteral::Float(value))),
            ) => *value == 0.0,
            (
                JavaType::Primitive(JavaPrimitiveType::Double),
                Some(JavaExpr::Literal(JavaLiteral::Double(value))),
            ) => *value == 0.0,
            _ => false,
        }
    }
}

struct InterfaceInitialization;

impl InterfaceInitialization {
    fn inline_replayable_locals(statements: &mut Vec<JavaStmt>) {
        let mut index = 0;
        while index < statements.len() {
            let JavaStmt::Variable {
                name,
                value: Some(value),
                ..
            } = &statements[index]
            else {
                index += 1;
                continue;
            };
            let name = name.clone();
            let value = value.clone();
            let following = &statements[index + 1..];
            let first_uses = following
                .first()
                .map(ExpressionNames::collect_statement)
                .unwrap_or_default();
            let uses = following
                .iter()
                .flat_map(ExpressionNames::collect_statement)
                .filter(|candidate| candidate == &name)
                .count();
            if uses < 2
                || !first_uses.contains(&name)
                || !ReplayableInitialization::check(&value)
                || LocalAssignment::check(&name, following)
            {
                index += 1;
                continue;
            }

            let mut substitution = NameSubstitution {
                values: std::collections::BTreeMap::from([(name, value)]),
            };
            for statement in &mut statements[index + 1..] {
                *statement =
                    substitution.rewrite_statement(std::mem::replace(statement, JavaStmt::Empty));
            }
            statements.remove(index);
        }
    }

    fn recover(
        owner: &JavaIdentifier,
        fields: &mut [JavaFieldDeclaration],
        statements: &mut Vec<JavaStmt>,
        method_names: &mut JavaNameScope,
    ) -> Option<JavaMethodDeclaration> {
        let (field_name, value) = Self::terminal_assignment(owner, statements.last()?)?;
        let field_index = fields.iter().position(|field| {
            field.name == field_name
                && field.modifiers.contains(&JavaModifier::Static)
                && field.modifiers.contains(&JavaModifier::Final)
                && StaticInitializationRecovery::is_default_initializer(field)
        })?;

        let mut writes = StaticInitializerWrites::new(
            owner.clone(),
            fields.iter().map(|field| field.name.clone()).collect(),
        );
        writes.rewrite_statement(JavaStmt::Block(statements.clone()));
        if writes.fields.len() != 1 || !writes.fields.contains(&field_name) {
            return None;
        }

        let field = &mut fields[field_index];
        let helper_name = method_names.claim(JavaIdentifier::from_dex("initialize"));
        let mut helper_statements = std::mem::take(statements);
        *helper_statements.last_mut()? = JavaStmt::Return(Some(value));
        field.initializer = Some(JavaExpr::Call {
            receiver: None,
            owner: None,
            type_arguments: Vec::new(),
            method: helper_name.clone(),
            args: Vec::new(),
        });

        Some(JavaMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Static],
            compiler_generated: true,
            kind: JavaMethodDeclarationKind::Method,
            type_parameters: Vec::new(),
            return_type: Some(field.ty.clone()),
            name: Some(helper_name),
            parameters: Vec::new(),
            throws: Vec::new(),
            body: Some(JavaMethodBody {
                root: JavaStmt::Block(helper_statements),
            }),
        })
    }

    fn recover_with_holder(
        owner: &JavaIdentifier,
        holder_name: JavaIdentifier,
        fields: &mut [JavaFieldDeclaration],
        statements: &mut Vec<JavaStmt>,
    ) -> Option<JavaTypeDeclaration> {
        let declared_fields = fields
            .iter()
            .map(|field| field.name.clone())
            .collect::<std::collections::BTreeSet<_>>();
        let mut writes = StaticInitializerWrites::new(owner.clone(), declared_fields);
        let mut analyzed = JavaMethodBody {
            root: JavaStmt::Block(statements.clone()),
        };
        writes.rewrite_body(&mut analyzed);
        if writes.fields.is_empty() {
            return None;
        }
        let selected = fields
            .iter()
            .enumerate()
            .filter_map(|(index, field)| writes.fields.contains(&field.name).then_some(index))
            .collect::<Vec<_>>();
        if selected.len() != writes.fields.len()
            || selected.iter().any(|index| {
                let field = &fields[*index];
                !field.modifiers.contains(&JavaModifier::Static)
                    || !field.modifiers.contains(&JavaModifier::Final)
                    || !StaticInitializationRecovery::is_default_initializer(field)
            })
        {
            return None;
        }

        let holder_type = JavaType::source_class(holder_name.as_str());
        let holder_fields = selected
            .iter()
            .map(|index| {
                let field = &fields[*index];
                JavaFieldDeclaration {
                    annotations: Vec::new(),
                    modifiers: vec![JavaModifier::Private, JavaModifier::Static],
                    ty: field.ty.clone(),
                    name: field.name.clone(),
                    initializer: None,
                }
            })
            .collect();
        for index in selected {
            let field = &mut fields[index];
            field.initializer = Some(JavaExpr::StaticField {
                owner: holder_type.clone(),
                name: field.name.clone(),
            });
        }
        let mut holder_body = JavaMethodBody {
            root: JavaStmt::Block(std::mem::take(statements)),
        };
        InterfaceStaticHolderReferences {
            owner,
            holder: holder_type,
            fields: &writes.fields,
        }
        .rewrite_body(&mut holder_body);

        Some(JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![
                JavaModifier::Public,
                JavaModifier::Static,
                JavaModifier::Final,
            ],
            kind: JavaTypeDeclarationKind::Class,
            name: holder_name,
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: holder_fields,
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Static],
                compiler_generated: true,
                kind: JavaMethodDeclarationKind::ClassInitializer,
                type_parameters: Vec::new(),
                return_type: None,
                name: None,
                parameters: Vec::new(),
                throws: Vec::new(),
                body: Some(holder_body),
            }],
            nested: Vec::new(),
        })
    }

    fn terminal_assignment(
        owner: &JavaIdentifier,
        statement: &JavaStmt,
    ) -> Option<(JavaIdentifier, JavaExpr)> {
        let JavaStmt::Assign {
            target:
                JavaExpr::StaticField {
                    owner: field_owner,
                    name,
                },
            op: JavaAssignOp::Assign,
            value,
        } = statement
        else {
            return None;
        };
        StaticInitializerWrites::is_own_owner(owner, field_owner)
            .then(|| (name.clone(), value.clone()))
    }
}

struct InterfaceStaticHolderReferences<'a> {
    owner: &'a JavaIdentifier,
    holder: JavaType,
    fields: &'a std::collections::BTreeSet<JavaIdentifier>,
}

impl JavaAstRewriter for InterfaceStaticHolderReferences<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::StaticField { owner, name }
                if self.fields.contains(&name)
                    && StaticInitializerWrites::is_own_owner(self.owner, &owner) =>
            {
                JavaExpr::StaticField {
                    owner: self.holder.clone(),
                    name,
                }
            }
            expression => expression,
        }
    }
}

struct ReplayableInitialization;

impl ReplayableInitialization {
    fn check(expression: &JavaExpr) -> bool {
        match expression {
            JavaExpr::Literal(_) | JavaExpr::ClassLiteral(_) => true,
            JavaExpr::StaticField { owner, name } => Self::stable_static_field(owner, name),
            JavaExpr::Cast { value, .. } => Self::check(value),
            JavaExpr::Call {
                receiver: None,
                owner: Some(JavaType::Class(owner)),
                method,
                args,
                ..
            } => Self::cached_boxing_value(owner.name().components(), method, args),
            _ => false,
        }
    }

    fn stable_static_field(owner: &JavaType, name: &JavaIdentifier) -> bool {
        if name.as_str() == "INSTANCE" {
            return true;
        }
        let JavaType::Class(owner) = owner else {
            return false;
        };
        let is_boolean = match owner.name().components() {
            [wrapper] => wrapper.as_str() == "Boolean",
            [package, module, wrapper] => {
                package.as_str() == "java"
                    && module.as_str() == "lang"
                    && wrapper.as_str() == "Boolean"
            }
            _ => false,
        };
        is_boolean && matches!(name.as_str(), "TRUE" | "FALSE")
    }

    fn cached_boxing_value(
        owner: &[JavaIdentifier],
        method: &JavaIdentifier,
        args: &[JavaExpr],
    ) -> bool {
        let wrapper = match owner {
            [wrapper] => wrapper,
            [package, module, wrapper]
                if package.as_str() == "java" && module.as_str() == "lang" =>
            {
                wrapper
            }
            _ => return false,
        };
        if method.as_str() != "valueOf" {
            return false;
        }
        let [value] = args else {
            return false;
        };
        match (wrapper.as_str(), value) {
            ("Boolean", JavaExpr::Literal(JavaLiteral::Boolean(_))) => true,
            ("Byte" | "Short" | "Integer", JavaExpr::Literal(JavaLiteral::Integer(-128..=127))) => {
                true
            }
            ("Long", JavaExpr::Literal(JavaLiteral::Long(-128..=127))) => true,
            ("Character", JavaExpr::Literal(JavaLiteral::Character(0..=127))) => true,
            _ => false,
        }
    }
}

struct LocalAssignment<'a> {
    name: &'a JavaIdentifier,
    assigned: bool,
}

impl<'a> LocalAssignment<'a> {
    fn check(name: &'a JavaIdentifier, statements: &[JavaStmt]) -> bool {
        let mut assignment = Self {
            name,
            assigned: false,
        };
        assignment.rewrite_statement(JavaStmt::Block(statements.to_vec()));
        assignment.assigned
    }
}

impl JavaAstRewriter for LocalAssignment<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if matches!(
            &expression,
            JavaExpr::Update { target, .. }
                | JavaExpr::Assignment { target, .. }
                    if matches!(target.as_ref(), JavaExpr::Name(name) if name == self.name)
        ) {
            self.assigned = true;
        }
        expression
    }

    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        if matches!(
            &statement,
            JavaStmt::Assign {
                target: JavaExpr::Name(name),
                ..
            } if name == self.name
        ) {
            self.assigned = true;
        }
        statement
    }
}

struct InitializationFact {
    field: crate::language::java::JavaIdentifier,
    value: JavaExpr,
    consumed: usize,
}

impl InitializationFact {
    fn analyze(statements: &[JavaStmt]) -> Option<Self> {
        Self::direct(statements).or_else(|| Self::straight_line(statements))
    }

    fn direct(statements: &[JavaStmt]) -> Option<Self> {
        let JavaStmt::Assign {
            target: JavaExpr::StaticField { name, .. },
            op: JavaAssignOp::Assign,
            value,
        } = statements.first()?
        else {
            return None;
        };
        Some(Self {
            field: name.clone(),
            value: value.clone(),
            consumed: 1,
        })
    }

    fn straight_line(statements: &[JavaStmt]) -> Option<Self> {
        let mut definitions = Vec::new();
        for statement in statements {
            let JavaStmt::Variable {
                name,
                value: Some(value),
                ..
            } = statement
            else {
                break;
            };
            definitions.push((name.clone(), value.clone()));
        }
        if definitions.is_empty() {
            return None;
        }
        let JavaStmt::Assign {
            target: JavaExpr::StaticField { name: field, .. },
            op: JavaAssignOp::Assign,
            value,
        } = statements.get(definitions.len())?
        else {
            return None;
        };

        let names = definitions
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<std::collections::BTreeSet<_>>();
        if definitions.iter().any(|(_, value)| {
            ExpressionNames::collect(value)
                .iter()
                .any(|name| names.contains(name))
        }) {
            return None;
        }
        let uses = ExpressionNames::collect(value)
            .into_iter()
            .filter(|name| names.contains(name))
            .collect::<Vec<_>>();
        if uses
            != definitions
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>()
        {
            return None;
        }
        let live_out = statements
            .iter()
            .skip(definitions.len() + 1)
            .flat_map(ExpressionNames::collect_statement)
            .collect::<std::collections::BTreeSet<_>>();
        if names.iter().any(|name| live_out.contains(name)) {
            return None;
        }

        let mut substitution = NameSubstitution {
            values: definitions.into_iter().collect(),
        };
        Some(Self {
            field: field.clone(),
            value: substitution.rewrite_expression(value.clone()),
            consumed: uses.len() + 1,
        })
    }
}

#[derive(Default)]
struct ExpressionNames {
    names: Vec<crate::language::java::JavaIdentifier>,
}

impl ExpressionNames {
    fn collect(expression: &JavaExpr) -> Vec<crate::language::java::JavaIdentifier> {
        let mut collector = Self::default();
        collector.rewrite_expression(expression.clone());
        collector.names
    }

    fn collect_statement(statement: &JavaStmt) -> Vec<crate::language::java::JavaIdentifier> {
        let mut collector = Self::default();
        collector.rewrite_statement(statement.clone());
        collector.names
    }
}

impl JavaAstRewriter for ExpressionNames {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if let JavaExpr::Name(name) = &expression {
            self.names.push(name.clone());
        }
        expression
    }
}

struct NameSubstitution {
    values: std::collections::BTreeMap<crate::language::java::JavaIdentifier, JavaExpr>,
}

impl JavaAstRewriter for NameSubstitution {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Name(name) => self
                .values
                .get(&name)
                .cloned()
                .unwrap_or(JavaExpr::Name(name)),
            expression => expression,
        }
    }
}

struct StaticInitializerWrites {
    owner: crate::language::java::JavaIdentifier,
    declared_fields: std::collections::BTreeSet<crate::language::java::JavaIdentifier>,
    fields: std::collections::BTreeSet<crate::language::java::JavaIdentifier>,
}

impl StaticInitializerWrites {
    fn new(
        owner: crate::language::java::JavaIdentifier,
        declared_fields: std::collections::BTreeSet<crate::language::java::JavaIdentifier>,
    ) -> Self {
        Self {
            owner,
            declared_fields,
            fields: std::collections::BTreeSet::new(),
        }
    }

    fn is_own_field(&self, owner: &JavaType, name: &crate::language::java::JavaIdentifier) -> bool {
        self.declared_fields.contains(name) && Self::is_own_owner(&self.owner, owner)
    }

    fn is_own_owner(owner: &JavaIdentifier, candidate: &JavaType) -> bool {
        matches!(
            candidate,
            JavaType::Class(class) if class.name().components().last() == Some(owner)
        )
    }
}

impl JavaAstRewriter for StaticInitializerWrites {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        if let JavaStmt::Assign {
            target: JavaExpr::StaticField { owner, name },
            op,
            value,
        } = statement
        {
            if !self.is_own_field(&owner, &name) {
                return JavaStmt::Assign {
                    target: JavaExpr::StaticField { owner, name },
                    op,
                    value,
                };
            }
            self.fields.insert(name.clone());
            return JavaStmt::Assign {
                target: JavaExpr::Name(name),
                op,
                value,
            };
        }
        statement
    }
}

#[cfg(test)]
mod tests {
    use super::StaticInitializationRecovery;
    use crate::language::java::{
        JavaAssignOp, JavaExpr, JavaFieldDeclaration, JavaIdentifier, JavaLiteral, JavaMethodBody,
        JavaMethodDeclaration, JavaMethodDeclarationKind, JavaModifier, JavaStmt, JavaType,
        JavaTypeDeclaration, JavaTypeDeclarationKind,
    };

    fn interface_with_shared_value(value: JavaExpr) -> JavaTypeDeclaration {
        let owner = JavaIdentifier::from_dex("Settings");
        let shared = JavaIdentifier::from_dex("shared");
        let first = JavaIdentifier::from_dex("FIRST");
        let second = JavaIdentifier::from_dex("SECOND");
        let field = |name| JavaFieldDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Static, JavaModifier::Final],
            ty: JavaType::source_class("java.lang.Object"),
            name,
            initializer: Some(JavaExpr::Literal(JavaLiteral::Null)),
        };
        let assignment = |name| JavaStmt::Assign {
            target: JavaExpr::StaticField {
                owner: JavaType::source_class("Settings"),
                name,
            },
            op: JavaAssignOp::Assign,
            value: JavaExpr::Name(shared.clone()),
        };
        JavaTypeDeclaration {
            annotations: Vec::new(),
            modifiers: vec![JavaModifier::Public],
            kind: JavaTypeDeclarationKind::Interface,
            name: owner,
            type_parameters: Vec::new(),
            extends: None,
            implements: Vec::new(),
            enum_constants: Vec::new(),
            fields: vec![field(first.clone()), field(second.clone())],
            methods: vec![JavaMethodDeclaration {
                annotations: Vec::new(),
                modifiers: vec![JavaModifier::Static],
                compiler_generated: true,
                kind: JavaMethodDeclarationKind::ClassInitializer,
                type_parameters: Vec::new(),
                return_type: None,
                name: None,
                parameters: Vec::new(),
                throws: Vec::new(),
                body: Some(JavaMethodBody {
                    root: JavaStmt::Block(vec![
                        JavaStmt::Variable {
                            ty: JavaType::source_class("java.lang.Object"),
                            name: shared.clone(),
                            value: Some(value),
                        },
                        assignment(first),
                        assignment(second),
                    ]),
                }),
            }],
            nested: Vec::new(),
        }
    }

    #[test]
    fn interface_static_singleton_aliases_become_field_initializers() {
        let value = JavaExpr::StaticField {
            owner: JavaType::source_class("java.lang.Boolean"),
            name: JavaIdentifier::from_dex("TRUE"),
        };
        let mut declaration = interface_with_shared_value(value.clone());

        StaticInitializationRecovery::apply(&mut declaration);

        assert!(declaration.methods.is_empty());
        assert!(declaration
            .fields
            .iter()
            .all(|field| field.initializer.as_ref() == Some(&value)));
    }

    #[test]
    fn interface_cached_boxing_aliases_become_field_initializers() {
        let value = JavaExpr::Call {
            receiver: None,
            owner: Some(JavaType::source_class("java.lang.Integer")),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("valueOf"),
            args: vec![JavaExpr::Literal(JavaLiteral::Integer(0))],
        };
        let mut declaration = interface_with_shared_value(value.clone());

        StaticInitializationRecovery::apply(&mut declaration);

        assert!(declaration.methods.is_empty());
        assert!(declaration
            .fields
            .iter()
            .all(|field| field.initializer.as_ref() == Some(&value)));
    }

    #[test]
    fn interface_allocated_aliases_use_a_static_holder() {
        let value = JavaExpr::New {
            enclosing: None,
            ty: JavaType::source_class("java.lang.Object"),
            target_type: None,
            args: Vec::new(),
            anonymous_body: None,
        };
        let mut declaration = interface_with_shared_value(value);

        StaticInitializationRecovery::apply(&mut declaration);

        assert!(declaration.methods.is_empty());
        assert_eq!(declaration.nested.len(), 1);
        assert_eq!(declaration.nested[0].fields.len(), 2);
        assert!(declaration
            .fields
            .iter()
            .all(|field| matches!(field.initializer, Some(JavaExpr::StaticField { .. }))));
        assert!(matches!(
            &declaration.nested[0].methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.first(),
                    Some(JavaStmt::Variable {
                        value: Some(JavaExpr::New { .. }),
                        ..
                    })
                )
        ));
    }

    #[test]
    fn interface_mutable_static_aliases_use_a_static_holder() {
        let value = JavaExpr::StaticField {
            owner: JavaType::source_class("com.example.State"),
            name: JavaIdentifier::from_dex("CURRENT"),
        };
        let mut declaration = interface_with_shared_value(value);

        StaticInitializationRecovery::apply(&mut declaration);

        assert!(declaration.methods.is_empty());
        assert_eq!(declaration.nested.len(), 1);
        assert_eq!(declaration.nested[0].fields.len(), 2);
        assert!(matches!(
            &declaration.nested[0].methods[0].body.as_ref().unwrap().root,
            JavaStmt::Block(statements)
                if matches!(
                    statements.first(),
                    Some(JavaStmt::Variable {
                        value: Some(JavaExpr::StaticField { .. }),
                        ..
                    })
                )
        ));
    }
}
