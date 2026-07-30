use std::collections::BTreeSet;

use super::{
    KotlinAstRewriter, KotlinClassName, KotlinIdentifier, KotlinType, KotlinTypeDeclaration,
};

/// Computes the import closure of the final typed source tree.
///
/// Type-name resolution intentionally starts from a conservative superset so
/// every lowering can use stable short names. Declaration recovery may then
/// remove synthetic parameters, methods, or annotations; this final analysis
/// removes imports that no surviving source type references.
pub struct KotlinImportAnalysis;

impl KotlinImportAnalysis {
    pub fn retain_used(
        imports: &mut Vec<KotlinClassName>,
        declaration: &mut KotlinTypeDeclaration,
    ) {
        if imports.is_empty() {
            return;
        }
        let mut uses = TypeNameUses::default();
        uses.rewrite_type_declaration(declaration);
        imports.retain(|import| {
            import
                .components()
                .last()
                .is_some_and(|name| uses.names.contains(name))
        });
    }
}

#[derive(Default)]
struct TypeNameUses {
    names: BTreeSet<KotlinIdentifier>,
}

impl KotlinAstRewriter for TypeNameUses {
    fn finish_type(&mut self, ty: KotlinType) -> KotlinType {
        if let KotlinType::Class(class) = &ty {
            if let Some(segment) = class.segments.first() {
                self.names.insert(segment.name.clone());
            }
        }
        ty
    }
}
