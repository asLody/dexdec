use crate::language::kotlin::{
    KotlinAssignOp, KotlinAstRewriter, KotlinExpr, KotlinFieldDeclaration, KotlinIdentifier,
    KotlinLiteral, KotlinMethodBody, KotlinMethodDeclaration, KotlinMethodDeclarationKind,
    KotlinModifier, KotlinNameScope, KotlinPrimitiveType, KotlinStmt, KotlinType,
    KotlinTypeDeclaration,
};

/// Recovers the direct-assignment prefix of `<clinit>` as field initializers.
///
/// The recovered fields are ordered by the executable schedule, not by DEX
/// field-table order. No executable statement is crossed.
pub(super) struct StaticInitializationRecovery;

impl StaticInitializationRecovery {
    pub(super) fn apply(declaration: &mut KotlinTypeDeclaration) {
        let Some(initializer_index) = declaration
            .methods
            .iter()
            .position(|method| method.kind == KotlinMethodDeclarationKind::ClassInitializer)
        else {
            return;
        };
        let mut method_names = KotlinNameScope::default();
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
        let KotlinStmt::Block(statements) = &mut body.root else {
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
                    && field.modifiers.contains(&KotlinModifier::Static)
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
                .collect::<Vec<KotlinFieldDeclaration>>();
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
                && field.modifiers.contains(&KotlinModifier::Static)
                && field.modifiers.contains(&KotlinModifier::Final)
                && Self::is_default_initializer(field)
            {
                field.initializer = None;
            }
        }
        if remove_initializer {
            declaration.methods.remove(initializer_index);
        }
    }

    fn is_default_initializer(field: &KotlinFieldDeclaration) -> bool {
        match (&field.ty, field.initializer.as_ref()) {
            (
                KotlinType::Class(_) | KotlinType::Array(_),
                Some(KotlinExpr::Literal(KotlinLiteral::Null)),
            ) => true,
            (
                KotlinType::Primitive(KotlinPrimitiveType::Boolean),
                Some(KotlinExpr::Literal(KotlinLiteral::Boolean(false))),
            ) => true,
            (
                KotlinType::Primitive(
                    KotlinPrimitiveType::Byte
                    | KotlinPrimitiveType::Short
                    | KotlinPrimitiveType::Char
                    | KotlinPrimitiveType::Int,
                ),
                Some(KotlinExpr::Literal(KotlinLiteral::Integer(0))),
            ) => true,
            (
                KotlinType::Primitive(KotlinPrimitiveType::Char),
                Some(KotlinExpr::Literal(KotlinLiteral::Character(0))),
            ) => true,
            (
                KotlinType::Primitive(KotlinPrimitiveType::Long),
                Some(KotlinExpr::Literal(KotlinLiteral::Long(0))),
            ) => true,
            (
                KotlinType::Primitive(KotlinPrimitiveType::Float),
                Some(KotlinExpr::Literal(KotlinLiteral::Float(value))),
            ) => *value == 0.0,
            (
                KotlinType::Primitive(KotlinPrimitiveType::Double),
                Some(KotlinExpr::Literal(KotlinLiteral::Double(value))),
            ) => *value == 0.0,
            _ => false,
        }
    }
}

struct InterfaceInitialization;

impl InterfaceInitialization {
    fn recover(
        owner: &KotlinIdentifier,
        fields: &mut [KotlinFieldDeclaration],
        statements: &mut Vec<KotlinStmt>,
        method_names: &mut KotlinNameScope,
    ) -> Option<KotlinMethodDeclaration> {
        let (field_name, value) = Self::terminal_assignment(owner, statements.last()?)?;
        let field_index = fields.iter().position(|field| {
            field.name == field_name
                && field.modifiers.contains(&KotlinModifier::Static)
                && field.modifiers.contains(&KotlinModifier::Final)
                && StaticInitializationRecovery::is_default_initializer(field)
        })?;

        let mut writes = StaticInitializerWrites::new(
            owner.clone(),
            fields.iter().map(|field| field.name.clone()).collect(),
        );
        writes.rewrite_statement(KotlinStmt::Block(statements.clone()));
        if writes.fields.len() != 1 || !writes.fields.contains(&field_name) {
            return None;
        }

        let field = &mut fields[field_index];
        let helper_name = method_names.claim(KotlinIdentifier::from_dex("initialize"));
        let mut helper_statements = std::mem::take(statements);
        *helper_statements.last_mut()? = KotlinStmt::Return(Some(value));
        field.initializer = Some(KotlinExpr::Call {
            receiver: None,
            owner: None,
            type_arguments: Vec::new(),
            method: helper_name.clone(),
            args: Vec::new().into(),
        });

        Some(KotlinMethodDeclaration {
            annotations: Vec::new(),
            modifiers: vec![KotlinModifier::Static],
            compiler_generated: true,
            kind: KotlinMethodDeclarationKind::Method,
            type_parameters: Vec::new(),
            return_type: Some(field.ty.clone()),
            return_nullable: true,
            name: Some(helper_name),
            receiver: None,
            parameters: Vec::new(),
            throws: Vec::new(),
            body: Some(KotlinMethodBody {
                root: KotlinStmt::Block(helper_statements),
            }),
        })
    }

    fn terminal_assignment(
        owner: &KotlinIdentifier,
        statement: &KotlinStmt,
    ) -> Option<(KotlinIdentifier, KotlinExpr)> {
        let KotlinStmt::Assign {
            target:
                KotlinExpr::StaticField {
                    owner: field_owner,
                    name,
                },
            op: KotlinAssignOp::Assign,
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
    field: crate::language::kotlin::KotlinIdentifier,
    value: KotlinExpr,
    consumed: usize,
}

impl InitializationFact {
    fn analyze(statements: &[KotlinStmt]) -> Option<Self> {
        Self::direct(statements).or_else(|| Self::straight_line(statements))
    }

    fn direct(statements: &[KotlinStmt]) -> Option<Self> {
        let KotlinStmt::Assign {
            target: KotlinExpr::StaticField { name, .. },
            op: KotlinAssignOp::Assign,
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

    fn straight_line(statements: &[KotlinStmt]) -> Option<Self> {
        let mut definitions = Vec::new();
        for statement in statements {
            let KotlinStmt::Variable {
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
        let KotlinStmt::Assign {
            target: KotlinExpr::StaticField { name: field, .. },
            op: KotlinAssignOp::Assign,
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
    names: Vec<crate::language::kotlin::KotlinIdentifier>,
}

impl ExpressionNames {
    fn collect(expression: &KotlinExpr) -> Vec<crate::language::kotlin::KotlinIdentifier> {
        let mut collector = Self::default();
        collector.rewrite_expression(expression.clone());
        collector.names
    }

    fn collect_statement(statement: &KotlinStmt) -> Vec<crate::language::kotlin::KotlinIdentifier> {
        let mut collector = Self::default();
        collector.rewrite_statement(statement.clone());
        collector.names
    }
}

impl KotlinAstRewriter for ExpressionNames {
    fn finish_expression(&mut self, expression: KotlinExpr) -> KotlinExpr {
        if let KotlinExpr::Name(name) = &expression {
            self.names.push(name.clone());
        }
        expression
    }
}

struct NameSubstitution {
    values: std::collections::BTreeMap<crate::language::kotlin::KotlinIdentifier, KotlinExpr>,
}

impl KotlinAstRewriter for NameSubstitution {
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

struct StaticInitializerWrites {
    owner: crate::language::kotlin::KotlinIdentifier,
    declared_fields: std::collections::BTreeSet<crate::language::kotlin::KotlinIdentifier>,
    fields: std::collections::BTreeSet<crate::language::kotlin::KotlinIdentifier>,
}

impl StaticInitializerWrites {
    fn new(
        owner: crate::language::kotlin::KotlinIdentifier,
        declared_fields: std::collections::BTreeSet<crate::language::kotlin::KotlinIdentifier>,
    ) -> Self {
        Self {
            owner,
            declared_fields,
            fields: std::collections::BTreeSet::new(),
        }
    }

    fn is_own_field(
        &self,
        owner: &KotlinType,
        name: &crate::language::kotlin::KotlinIdentifier,
    ) -> bool {
        self.declared_fields.contains(name) && Self::is_own_owner(&self.owner, owner)
    }

    fn is_own_owner(owner: &KotlinIdentifier, candidate: &KotlinType) -> bool {
        matches!(
            candidate,
            KotlinType::Class(class) if class.name().components().last() == Some(owner)
        )
    }
}

impl KotlinAstRewriter for StaticInitializerWrites {
    fn finish_statement(&mut self, statement: KotlinStmt) -> KotlinStmt {
        if let KotlinStmt::Assign {
            target: KotlinExpr::StaticField { owner, name },
            op,
            value,
        } = statement
        {
            if !self.is_own_field(&owner, &name) {
                return KotlinStmt::Assign {
                    target: KotlinExpr::StaticField { owner, name },
                    op,
                    value,
                };
            }
            self.fields.insert(name.clone());
            return KotlinStmt::Assign {
                target: KotlinExpr::Name(name),
                op,
                value,
            };
        }
        statement
    }
}
