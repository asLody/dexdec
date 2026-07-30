use super::kotlin_model::{KotlinClassModel, KotlinSourceAbi};
use crate::language::kotlin::{
    KotlinFieldDeclaration, KotlinMethodDeclarationKind, KotlinModifier, KotlinType,
    KotlinTypeDeclaration, KotlinTypeDeclarationKind,
};

/// Converts JVM collection contracts to declarations understood by Kotlin's
/// mapped collection source types.
pub(super) struct KotlinMappedMembers;

impl KotlinMappedMembers {
    pub(super) fn apply(
        model: &KotlinClassModel,
        source_abi: &KotlinSourceAbi,
        declaration: &mut KotlinTypeDeclaration,
    ) {
        if declaration.kind != KotlinTypeDeclarationKind::Interface {
            return;
        }
        let Some(owner) = model.declaration.current_type() else {
            return;
        };
        if !source_abi.is_mapped_collection_size_owner(&owner) {
            return;
        }
        let mut retained = Vec::with_capacity(declaration.methods.len());
        for method in std::mem::take(&mut declaration.methods) {
            if Self::is_size_contract(&method) {
                let mut modifiers = method
                    .modifiers
                    .into_iter()
                    .filter(|modifier| {
                        matches!(
                            modifier,
                            KotlinModifier::Public
                                | KotlinModifier::Protected
                                | KotlinModifier::Private
                                | KotlinModifier::Abstract
                        )
                    })
                    .collect::<Vec<_>>();
                modifiers.push(KotlinModifier::Final);
                declaration.fields.push(KotlinFieldDeclaration {
                    annotations: method.annotations,
                    modifiers,
                    ty: KotlinType::int(),
                    name: method.name.expect("mapped member has a name"),
                    nullable: false,
                    initializer: None,
                });
            } else {
                retained.push(method);
            }
        }
        declaration.methods = retained;
    }

    fn is_size_contract(method: &crate::language::kotlin::KotlinMethodDeclaration) -> bool {
        method.kind == KotlinMethodDeclarationKind::Method
            && method
                .name
                .as_ref()
                .is_some_and(|name| name.as_str() == "size")
            && method.parameters.is_empty()
            && method.return_type.as_ref() == Some(&KotlinType::int())
    }
}
