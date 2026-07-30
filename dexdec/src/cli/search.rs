//! Deterministic symbol and resource search.

use serde::Serialize;

use crate::{Decompiler, MemberKind};

use super::error::{CliError, CliResult};
use super::model::{SearchKind, SearchRequest};
use super::output::{CliHost, CommandContext};
use super::resources::ResourceArchive;

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
struct SearchResult {
    kind: &'static str,
    name: String,
    owner: Option<String>,
    descriptor: Option<String>,
    path: Option<String>,
    has_code: Option<bool>,
    #[serde(skip)]
    rank: u8,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SearchPage<'a> {
    query: &'a str,
    kind: &'static str,
    total: usize,
    offset: usize,
    limit: usize,
    results: &'a [SearchResult],
}

pub struct SearchCommand;

impl SearchCommand {
    pub fn run<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &SearchRequest,
    ) -> CliResult<()> {
        let query = request.query.trim();
        if query.is_empty() {
            return Err(CliError::usage("search query cannot be empty"));
        }
        let folded = query.to_ascii_lowercase();
        let decompiler = Decompiler::open(&request.input)?;
        let catalog = decompiler.catalog();
        let mut results = Vec::new();

        if matches!(request.kind, SearchKind::Any | SearchKind::Class) {
            for class in catalog.classes() {
                let rank = [
                    class.qualified_name.as_str(),
                    class.descriptor.as_str(),
                    class.display_name.as_str(),
                ]
                .into_iter()
                .filter_map(|candidate| Self::rank(candidate, &folded))
                .min();
                if let Some(rank) = rank {
                    results.push(SearchResult {
                        kind: "class",
                        name: class.qualified_name.clone(),
                        owner: None,
                        descriptor: Some(class.descriptor.clone()),
                        path: None,
                        has_code: None,
                        rank,
                    });
                }
            }
        }

        if matches!(
            request.kind,
            SearchKind::Any | SearchKind::Field | SearchKind::Method
        ) {
            let members = decompiler.member_catalog()?;
            for member in members.members() {
                let selected = match (request.kind, member.kind) {
                    (SearchKind::Any, _) => true,
                    (SearchKind::Field, MemberKind::Field) => true,
                    (SearchKind::Method, MemberKind::Method) => true,
                    _ => false,
                };
                if !selected {
                    continue;
                }
                let identity = format!("{}->{}{}", member.owner, member.name, member.descriptor);
                let Some(rank) = [
                    member.name.as_str(),
                    identity.as_str(),
                    member.owner.as_str(),
                ]
                .into_iter()
                .filter_map(|candidate| Self::rank(candidate, &folded))
                .min() else {
                    continue;
                };
                results.push(SearchResult {
                    kind: match member.kind {
                        MemberKind::Field => "field",
                        MemberKind::Method => "method",
                    },
                    name: member.name.clone(),
                    owner: Some(member.owner.clone()),
                    descriptor: Some(member.descriptor.clone()),
                    path: None,
                    has_code: (member.kind == MemberKind::Method).then_some(member.has_code),
                    rank,
                });
            }
        }

        if matches!(request.kind, SearchKind::Any | SearchKind::Resource) {
            if let Some(resources) = ResourceArchive::open_optional(&request.input)? {
                for entry in resources.entries() {
                    let Some(rank) = Self::rank(&entry.path, &folded) else {
                        continue;
                    };
                    results.push(SearchResult {
                        kind: "resource",
                        name: entry
                            .path
                            .rsplit('/')
                            .next()
                            .unwrap_or(&entry.path)
                            .to_string(),
                        owner: None,
                        descriptor: None,
                        path: Some(entry.path.clone()),
                        has_code: None,
                        rank,
                    });
                }
            }
        }

        results.sort_unstable_by(|left, right| {
            left.rank
                .cmp(&right.rank)
                .then_with(|| left.kind.cmp(right.kind))
                .then_with(|| left.name.cmp(&right.name))
                .then_with(|| left.owner.cmp(&right.owner))
                .then_with(|| left.descriptor.cmp(&right.descriptor))
        });
        let total = results.len();
        let results = results
            .into_iter()
            .skip(request.offset)
            .take(if request.limit == 0 {
                usize::MAX
            } else {
                request.limit
            })
            .collect::<Vec<_>>();
        let page = SearchPage {
            query,
            kind: match request.kind {
                SearchKind::Any => "any",
                SearchKind::Class => "class",
                SearchKind::Field => "field",
                SearchKind::Method => "method",
                SearchKind::Resource => "resource",
            },
            total,
            offset: request.offset,
            limit: request.limit,
            results: &results,
        };
        let mut text = String::new();
        for result in &results {
            let identity = result
                .path
                .as_deref()
                .unwrap_or_else(|| result.descriptor.as_deref().unwrap_or(result.name.as_str()));
            text.push_str(&format!(
                "{}\t{}\t{}\t{}\n",
                result.kind,
                result.owner.as_deref().unwrap_or(""),
                result.name,
                identity
            ));
        }
        context.respond("search", &page, &text)
    }

    fn rank(candidate: &str, folded_query: &str) -> Option<u8> {
        let candidate = candidate.to_ascii_lowercase();
        if candidate == folded_query {
            Some(0)
        } else if candidate.starts_with(folded_query) {
            Some(1)
        } else if candidate.contains(folded_query) {
            Some(2)
        } else {
            None
        }
    }
}
