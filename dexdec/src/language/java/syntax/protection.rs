use crate::ir::{
    analysis::{SubtypeRelation, TypeHierarchy},
    ArgType, SemanticFoldError, SemanticFolder, SemanticNode,
};

/// Normalizes DEX exception-handler groups to legal Java catch alternatives.
///
/// DEX permits related catch types to target the same handler. Java multi-catch
/// does not: no alternative may be a subtype of another. Since every type in a
/// grouped handler has the same body, a strictly narrower alternative is
/// redundant and can be removed without changing which code executes.
pub(super) struct ProtectionSyntax<'a> {
    hierarchy: &'a dyn TypeHierarchy,
    changed: bool,
}

impl<'a> ProtectionSyntax<'a> {
    pub(super) fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self {
            hierarchy,
            changed: false,
        }
    }

    pub(super) fn apply(&mut self, root: &mut SemanticNode) -> Result<bool, SemanticFoldError> {
        self.changed = false;
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = self.fold_node(body)?;
        Ok(self.changed)
    }

    fn is_strict_subtype(&self, candidate: &ArgType, alternative: &ArgType) -> bool {
        let (Some(candidate), Some(alternative)) = (candidate.as_object(), alternative.as_object())
        else {
            return false;
        };
        self.hierarchy.subtype_relation(candidate, alternative) == SubtypeRelation::Yes
            && self.hierarchy.subtype_relation(alternative, candidate) != SubtypeRelation::Yes
    }

    fn normalize_types(&mut self, types: &mut Vec<ArgType>) {
        if types.len() < 2 {
            return;
        }
        let original = types.clone();
        types.retain(|candidate| {
            !original.iter().any(|alternative| {
                candidate != alternative && self.is_strict_subtype(candidate, alternative)
            })
        });
        self.changed |= types.len() != original.len();
    }
}

impl SemanticFolder for ProtectionSyntax<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        if let SemanticNode::Try { catches, .. } = &mut node {
            for catch in catches {
                self.normalize_types(&mut catch.exception_types);
            }
        }
        Ok(node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::analysis::ClassHierarchyIndex;

    fn throwable_hierarchy() -> ClassHierarchyIndex {
        let mut hierarchy = ClassHierarchyIndex::default();
        hierarchy.add("java/lang/Throwable", vec!["java/lang/Object".to_string()]);
        hierarchy.add("java/lang/Error", vec!["java/lang/Throwable".to_string()]);
        hierarchy.add(
            "java/lang/VirtualMachineError",
            vec!["java/lang/Error".to_string()],
        );
        hierarchy.add(
            "java/lang/OutOfMemoryError",
            vec!["java/lang/VirtualMachineError".to_string()],
        );
        hierarchy.add(
            "java/lang/Exception",
            vec!["java/lang/Throwable".to_string()],
        );
        hierarchy.add(
            "java/io/IOException",
            vec!["java/lang/Exception".to_string()],
        );
        hierarchy
    }

    #[test]
    fn removes_related_multi_catch_alternative() {
        let hierarchy = throwable_hierarchy();
        let mut syntax = ProtectionSyntax::new(&hierarchy);
        let mut types = vec![
            ArgType::object("java/lang/Error"),
            ArgType::object("java/lang/OutOfMemoryError"),
        ];

        syntax.normalize_types(&mut types);

        assert_eq!(types, vec![ArgType::object("java/lang/Error")]);
    }

    #[test]
    fn keeps_unrelated_multi_catch_alternatives() {
        let hierarchy = throwable_hierarchy();
        let mut syntax = ProtectionSyntax::new(&hierarchy);
        let mut types = vec![
            ArgType::object("java/io/IOException"),
            ArgType::object("java/lang/Error"),
        ];

        syntax.normalize_types(&mut types);

        assert_eq!(
            types,
            vec![
                ArgType::object("java/io/IOException"),
                ArgType::object("java/lang/Error"),
            ]
        );
    }
}
