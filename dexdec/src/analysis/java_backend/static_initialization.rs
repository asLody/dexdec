use crate::language::java::{
    JavaAssignOp, JavaAstRewriter, JavaExpr, JavaFieldDeclaration, JavaIdentifier, JavaLiteral,
    JavaMethodBody, JavaMethodDeclaration, JavaMethodDeclarationKind, JavaModifier, JavaNameScope,
    JavaPrimitiveType, JavaStmt, JavaType, JavaTypeDeclaration,
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
            if let Some(initialization) = InterfaceInitialization::recover(
                &declaration.name,
                &mut declaration.fields,
                statements,
                &mut method_names,
            ) {
                declaration.methods[initializer_index] = initialization;
                return;
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
