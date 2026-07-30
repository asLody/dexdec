//! Collection of class-wide member symbols before Kotlin body lowering.

use crate::ir::{ArgType, MethodDescriptor};
use crate::language::kotlin::{
    KotlinConstructorLayout, KotlinFieldSymbol, KotlinMemberNames, KotlinMethodSymbol,
};

use super::kotlin_model::method::{KotlinMethodDeclarationKind, KotlinMethodModel};
use super::kotlin_model::KotlinClassModel;

pub(super) struct ClassMemberNames;

impl ClassMemberNames {
    pub(super) fn collect(root: &KotlinClassModel) -> KotlinMemberNames {
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut constructors = Vec::new();
        let mut pending = vec![root];
        while let Some(class) = pending.pop() {
            pending.extend(class.nested.iter().rev());
            let Some(owner) = class.declaration.current_type() else {
                continue;
            };
            fields.extend(class.fields.iter().map(|field| {
                KotlinFieldSymbol::new(owner.clone(), field.name.clone(), field.field_type.clone())
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
        KotlinMemberNames::allocate(fields, methods).with_constructor_layouts(constructors)
    }

    pub(super) fn method_only(
        owner: Option<&ArgType>,
        method: &KotlinMethodModel,
    ) -> KotlinMemberNames {
        let constructor = owner
            .cloned()
            .and_then(|owner| Self::constructor(owner, method));
        KotlinMemberNames::allocate(
            std::iter::empty(),
            owner.cloned().and_then(|owner| Self::method(owner, method)),
        )
        .with_constructor_layouts(constructor)
    }

    fn method(owner: ArgType, method: &KotlinMethodModel) -> Option<KotlinMethodSymbol> {
        let declaration = &method.declaration;
        (declaration.kind == KotlinMethodDeclarationKind::Method).then(|| {
            KotlinMethodSymbol::new(
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

    fn constructor(owner: ArgType, method: &KotlinMethodModel) -> Option<KotlinConstructorLayout> {
        let declaration = &method.declaration;
        (declaration.kind == KotlinMethodDeclarationKind::Constructor).then(|| {
            KotlinConstructorLayout::new(
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
