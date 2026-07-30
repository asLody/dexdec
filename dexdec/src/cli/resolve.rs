//! Deterministic symbol resolution shared by public commands.

use crate::{ArchiveCatalog, ClassSummary};

use super::error::{CliError, CliResult};

pub struct ClassResolver<'a> {
    catalog: &'a ArchiveCatalog,
}

impl<'a> ClassResolver<'a> {
    pub fn new(catalog: &'a ArchiveCatalog) -> Self {
        Self { catalog }
    }

    pub fn resolve(&self, query: &str) -> CliResult<&'a ClassSummary> {
        let query = query.trim();
        if query.is_empty() {
            return Err(CliError::usage("class selector cannot be empty"));
        }

        let descriptor_candidate = Self::descriptor_candidate(query);
        let exact = self
            .catalog
            .classes()
            .iter()
            .filter(|class| {
                class.descriptor == query
                    || class.qualified_name == query
                    || class.binary_name == query
                    || descriptor_candidate
                        .as_deref()
                        .is_some_and(|descriptor| class.descriptor == descriptor)
            })
            .collect::<Vec<_>>();
        if exact.len() == 1 {
            return Ok(exact[0]);
        }
        if exact.len() > 1 {
            return Err(self.ambiguous(query, exact));
        }

        let folded = query.to_ascii_lowercase();
        let insensitive = self
            .catalog
            .classes()
            .iter()
            .filter(|class| {
                class.descriptor.to_ascii_lowercase() == folded
                    || class.qualified_name.to_ascii_lowercase() == folded
            })
            .collect::<Vec<_>>();
        if insensitive.len() == 1 {
            return Ok(insensitive[0]);
        }
        if insensitive.len() > 1 {
            return Err(self.ambiguous(query, insensitive));
        }

        Err(CliError::not_found(format!("class not found: {query}"))
            .with_hint(format!(
                "Run `dexdec search <input> '{}' --kind class --format json` to find its exact descriptor.",
                query.replace('`', "")
            )))
    }

    fn descriptor_candidate(query: &str) -> Option<String> {
        (!query.starts_with('L') && query.contains('.'))
            .then(|| format!("L{};", query.replace('.', "/")))
    }

    fn ambiguous(&self, query: &str, classes: Vec<&ClassSummary>) -> CliError {
        let candidates = classes
            .into_iter()
            .take(12)
            .map(|class| class.descriptor.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        CliError::ambiguous(format!("class selector is ambiguous: {query}"))
            .with_hint(format!("Choose an exact descriptor: {candidates}"))
    }
}
