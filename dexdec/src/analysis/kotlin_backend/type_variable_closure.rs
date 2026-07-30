use std::collections::BTreeSet;

use crate::language::kotlin::{
    KotlinIdentifier, KotlinModifier, KotlinType, KotlinTypeArgument, KotlinTypeDeclaration,
    KotlinTypeParameter,
};

/// Closes free generic variables when a local or anonymous class remains as a
/// source-level nested declaration instead of being embedded at its allocation.
pub(super) struct TypeVariableClosure;

impl TypeVariableClosure {
    pub(super) fn close(root: &mut KotlinTypeDeclaration) {
        Self::close_declaration(root, &BTreeSet::new());
    }

    fn close_declaration(
        declaration: &mut KotlinTypeDeclaration,
        enclosing: &BTreeSet<KotlinIdentifier>,
    ) {
        let inherited = if declaration.modifiers.contains(&KotlinModifier::Static) {
            BTreeSet::new()
        } else {
            enclosing.clone()
        };
        let declared = declaration
            .type_parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect::<BTreeSet<_>>();
        let mut free = Self::declaration_variables(declaration);
        free.retain(|variable| !declared.contains(variable) && !inherited.contains(variable));
        declaration
            .type_parameters
            .extend(free.into_iter().map(|name| KotlinTypeParameter {
                name,
                bounds: Vec::new(),
            }));

        let mut visible = inherited;
        visible.extend(
            declaration
                .type_parameters
                .iter()
                .map(|parameter| parameter.name.clone()),
        );
        for nested in &mut declaration.nested {
            Self::close_declaration(nested, &visible);
        }
    }

    fn declaration_variables(declaration: &KotlinTypeDeclaration) -> BTreeSet<KotlinIdentifier> {
        let mut variables = BTreeSet::new();
        for parameter in &declaration.type_parameters {
            Self::types(&parameter.bounds, &mut variables);
        }
        if let Some(extends) = &declaration.extends {
            Self::ty(extends, &mut variables);
        }
        Self::types(&declaration.implements, &mut variables);
        for field in &declaration.fields {
            Self::ty(&field.ty, &mut variables);
        }
        for property in &declaration.properties {
            Self::ty(&property.ty, &mut variables);
        }
        for method in &declaration.methods {
            let local = method
                .type_parameters
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect::<BTreeSet<_>>();
            let mut method_variables = BTreeSet::new();
            for parameter in &method.type_parameters {
                Self::types(&parameter.bounds, &mut method_variables);
            }
            if let Some(return_type) = &method.return_type {
                Self::ty(return_type, &mut method_variables);
            }
            for parameter in &method.parameters {
                Self::ty(&parameter.ty, &mut method_variables);
            }
            Self::types(&method.throws, &mut method_variables);
            method_variables.retain(|variable| !local.contains(variable));
            variables.extend(method_variables);
        }
        variables
    }

    fn types(types: &[KotlinType], variables: &mut BTreeSet<KotlinIdentifier>) {
        for ty in types {
            Self::ty(ty, variables);
        }
    }

    fn ty(ty: &KotlinType, variables: &mut BTreeSet<KotlinIdentifier>) {
        match ty {
            KotlinType::Variable(variable) => {
                variables.insert(variable.clone());
            }
            KotlinType::Array(element) => Self::ty(element, variables),
            KotlinType::Class(class) => {
                for argument in class.segments.iter().flat_map(|segment| &segment.arguments) {
                    match argument {
                        KotlinTypeArgument::Any => {}
                        KotlinTypeArgument::Exact(value)
                        | KotlinTypeArgument::Extends(value)
                        | KotlinTypeArgument::Super(value) => Self::ty(value, variables),
                    }
                }
            }
            KotlinType::Primitive(_) => {}
        }
    }
}
