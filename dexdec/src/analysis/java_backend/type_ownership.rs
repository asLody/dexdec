use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::NestedClassInput;

/// Lexical ownership facts for the source type tree represented by one Java
/// compilation unit.
pub(crate) struct NestedTypeOwnership {
    parents: BTreeMap<String, Option<String>>,
}

impl NestedTypeOwnership {
    pub(crate) fn analyze(root: &str, nested: &[NestedClassInput]) -> Self {
        let mut ownership = Self {
            parents: BTreeMap::from([(root.to_string(), None)]),
        };
        ownership.collect(root, nested);
        ownership
    }

    /// Returns the nearest represented type that lexically owns every site.
    pub(crate) fn common_owner<'a>(
        &self,
        sites: impl IntoIterator<Item = &'a str>,
    ) -> Option<String> {
        let mut sites = sites.into_iter();
        let mut owner = sites.next()?.to_string();
        if !self.parents.contains_key(&owner) {
            return None;
        }
        for site in sites {
            owner = self.common_ancestor(&owner, site)?;
        }
        Some(owner)
    }

    fn collect(&mut self, parent: &str, nested: &[NestedClassInput]) {
        for input in nested {
            let child = input.class.type_descriptor().to_string();
            self.parents.insert(child.clone(), Some(parent.to_string()));
            self.collect(&child, &input.nested);
        }
    }

    fn common_ancestor(&self, left: &str, right: &str) -> Option<String> {
        let left_ancestors = self.ancestors(left)?;
        let mut candidate = Some(right);
        while let Some(current) = candidate {
            if left_ancestors.contains(current) {
                return Some(current.to_string());
            }
            candidate = self.parents.get(current)?.as_deref();
        }
        None
    }

    fn ancestors<'a>(&'a self, site: &'a str) -> Option<BTreeSet<&'a str>> {
        if !self.parents.contains_key(site) {
            return None;
        }
        let mut ancestors = BTreeSet::new();
        let mut candidate = Some(site);
        while let Some(current) = candidate {
            ancestors.insert(current);
            candidate = self.parents.get(current)?.as_deref();
        }
        Some(ancestors)
    }
}
