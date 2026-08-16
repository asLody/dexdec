//! Collection of class-wide member symbols before Java body lowering.

use crate::ir::{ArgType, MethodDescriptor};
use crate::language::java::{
    JavaConstructorLayout, JavaFieldSymbol, JavaIdentifier, JavaMemberNames, JavaMethodSymbol,
};

use super::java_model::method::{JavaMethodDeclarationKind, JavaMethodModel};
use super::java_model::JavaClassModel;

pub(super) struct ClassMemberNames;

impl ClassMemberNames {
    pub(super) fn collect(root: &JavaClassModel) -> JavaMemberNames {
        let mut fields = Vec::new();
        let mut hidden_fields = Vec::new();
        let mut methods = Vec::new();
        let mut constructors = Vec::new();
        let mut pending = vec![root];
        while let Some(class) = pending.pop() {
            pending.extend(class.nested.iter().rev());
            let Some(owner) = class.declaration.current_type() else {
                continue;
            };
            fields.extend(class.fields.iter().map(|field| {
                JavaFieldSymbol::new(owner.clone(), field.name.clone(), field.field_type.clone())
            }));
            hidden_fields.extend(class.outer_instance.iter().map(|outer| {
                let field = outer.reference();
                JavaFieldSymbol::new(
                    field.owner.clone(),
                    JavaIdentifier::from_dex(&field.name),
                    field.field_type.clone(),
                )
            }));
            methods.extend(
                class
                    .methods
                    .iter()
                    .filter_map(|method| Self::method(owner.clone(), method)),
            );
            constructors.extend(
                class
                    .methods
                    .iter()
                    .filter_map(|method| Self::constructor(owner.clone(), method)),
            );
        }
        JavaMemberNames::allocate(fields, methods)
            .with_hidden_fields(hidden_fields)
            .with_constructor_layouts(constructors)
    }

    pub(super) fn method_only(
        owner: Option<&ArgType>,
        method: &JavaMethodModel,
    ) -> JavaMemberNames {
        let constructor = owner
            .cloned()
            .and_then(|owner| Self::constructor(owner, method));
        JavaMemberNames::allocate(
            std::iter::empty(),
            owner.cloned().and_then(|owner| Self::method(owner, method)),
        )
        .with_constructor_layouts(constructor)
    }

    fn method(owner: ArgType, method: &JavaMethodModel) -> Option<JavaMethodSymbol> {
        let declaration = &method.declaration;
        (declaration.kind == JavaMethodDeclarationKind::Method).then(|| {
            JavaMethodSymbol::new(
                owner,
                declaration.name.clone(),
                MethodDescriptor {
                    parameters: declaration
                        .parameters
                        .iter()
                        .map(|parameter| parameter.ty.clone())
                        .collect(),
                    return_type: declaration.return_type.clone().unwrap_or(ArgType::VOID),
                },
            )
        })
    }

    fn constructor(owner: ArgType, method: &JavaMethodModel) -> Option<JavaConstructorLayout> {
        let declaration = &method.declaration;
        (declaration.kind == JavaMethodDeclarationKind::Constructor).then(|| {
            JavaConstructorLayout::new(
                owner,
                MethodDescriptor {
                    parameters: declaration
                        .parameters
                        .iter()
                        .map(|parameter| parameter.ty.clone())
                        .collect(),
                    return_type: ArgType::VOID,
                },
                declaration
                    .parameters
                    .iter()
                    .enumerate()
                    .filter_map(|(index, parameter)| parameter.hidden.then_some(index)),
            )
        })
    }
}
