use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

use dexdec::{ArchiveCatalog, MemberKind, MemberSummary, MemberVisitor};
use schemars::JsonSchema;
use serde::Serialize;

use crate::resources::ResourceEntryDto;

const MAX_RESULTS: usize = 200;

pub struct SymbolSearchIndex {
    owners: Vec<OwnerRecord>,
    names: Vec<SymbolName>,
    descriptors: Vec<Box<str>>,
    classes: Vec<ClassEntry>,
    members: Vec<MemberEntry>,
    resources: Vec<ResourceEntry>,
}

impl SymbolSearchIndex {
    pub fn builder(
        classes: &ArchiveCatalog,
        resources: &[ResourceEntryDto],
    ) -> SymbolSearchIndexBuilder {
        let mut owners = Vec::with_capacity(classes.len());
        let mut owner_indices = HashMap::with_capacity(classes.len());
        let mut class_entries = Vec::with_capacity(classes.len());
        for class in classes.classes() {
            let owner = owners.len() as u32;
            owner_indices.insert(class.descriptor.clone(), owner);
            owners.push(OwnerRecord {
                descriptor: class.descriptor.clone().into_boxed_str(),
                qualified_name: class.qualified_name.clone().into_boxed_str(),
                display_name: class.display_name.clone().into_boxed_str(),
                package: class.package.clone().into_boxed_str(),
            });
            class_entries.push(ClassEntry {
                owner,
                search_key: class.qualified_name.to_lowercase().into_boxed_str(),
            });
        }

        let resources = resources
            .iter()
            .map(|resource| ResourceEntry {
                search_key: resource.path.to_lowercase().into_boxed_str(),
                path: resource.path.clone().into_boxed_str(),
            })
            .collect();
        SymbolSearchIndexBuilder {
            owners,
            owner_indices,
            classes: class_entries,
            members: Vec::new(),
            resources,
            names: TextPoolBuilder::default(),
            descriptors: TextPoolBuilder::default(),
        }
    }

    pub fn search(&self, query: &str, limit: usize) -> Vec<SymbolSearchResultDto> {
        let query = query.trim().to_lowercase();
        if query.is_empty() {
            return Vec::new();
        }
        let limit = limit.clamp(1, MAX_RESULTS);
        if query.len() == 1 {
            let prefix = self.prefix_matches(&query, limit);
            if prefix.len() == limit {
                return self.materialize(prefix);
            }
        }

        let mut matches = RankedMatches::new(limit);
        for (index, entry) in self.classes.iter().enumerate() {
            matches.consider(entry.search_key.as_ref(), &query, SearchHit::Class(index));
        }
        for (index, entry) in self.members.iter().enumerate() {
            matches.consider(
                self.names[entry.name as usize].search_key.as_ref(),
                &query,
                SearchHit::Member(index),
            );
        }
        for (index, entry) in self.resources.iter().enumerate() {
            matches.consider(
                entry.search_key.as_ref(),
                &query,
                SearchHit::Resource(index),
            );
        }
        self.materialize(matches.finish())
    }

    fn prefix_matches(&self, query: &str, limit: usize) -> Vec<SearchHit> {
        self.classes
            .iter()
            .enumerate()
            .filter(|(_, entry)| entry.search_key.starts_with(query))
            .map(|(index, _)| SearchHit::Class(index))
            .chain(
                self.members
                    .iter()
                    .enumerate()
                    .filter(|(_, entry)| {
                        self.names[entry.name as usize]
                            .search_key
                            .starts_with(query)
                    })
                    .map(|(index, _)| SearchHit::Member(index)),
            )
            .chain(
                self.resources
                    .iter()
                    .enumerate()
                    .filter(|(_, entry)| entry.search_key.starts_with(query))
                    .map(|(index, _)| SearchHit::Resource(index)),
            )
            .take(limit)
            .collect()
    }

    fn materialize(&self, matches: Vec<SearchHit>) -> Vec<SymbolSearchResultDto> {
        matches
            .into_iter()
            .map(|hit| match hit {
                SearchHit::Class(index) => self.class_result(&self.classes[index]),
                SearchHit::Member(index) => self.member_result(&self.members[index]),
                SearchHit::Resource(index) => self.resource_result(&self.resources[index]),
            })
            .collect()
    }

    fn class_result(&self, entry: &ClassEntry) -> SymbolSearchResultDto {
        let owner = &self.owners[entry.owner as usize];
        SymbolSearchResultDto {
            kind: SymbolSearchKind::Class,
            name: owner.display_name.to_string(),
            detail: owner.package.to_string(),
            class_descriptor: Some(owner.descriptor.to_string()),
            descriptor: None,
            resource_path: None,
        }
    }

    fn member_result(&self, entry: &MemberEntry) -> SymbolSearchResultDto {
        let owner = &self.owners[entry.owner as usize];
        let descriptor = &self.descriptors[entry.descriptor as usize];
        SymbolSearchResultDto {
            kind: entry.kind,
            name: self.names[entry.name as usize].display.to_string(),
            detail: format!("{}  {descriptor}", owner.qualified_name),
            class_descriptor: Some(owner.descriptor.to_string()),
            descriptor: Some(descriptor.to_string()),
            resource_path: None,
        }
    }

    fn resource_result(&self, entry: &ResourceEntry) -> SymbolSearchResultDto {
        SymbolSearchResultDto {
            kind: SymbolSearchKind::Resource,
            name: entry
                .path
                .rsplit('/')
                .next()
                .unwrap_or(&entry.path)
                .to_string(),
            detail: entry.path.to_string(),
            class_descriptor: None,
            descriptor: None,
            resource_path: Some(entry.path.to_string()),
        }
    }
}

pub struct SymbolSearchIndexBuilder {
    owners: Vec<OwnerRecord>,
    owner_indices: HashMap<String, u32>,
    classes: Vec<ClassEntry>,
    members: Vec<MemberEntry>,
    resources: Vec<ResourceEntry>,
    names: TextPoolBuilder,
    descriptors: TextPoolBuilder,
}

impl SymbolSearchIndexBuilder {
    pub fn finish(self) -> SymbolSearchIndex {
        let names = self
            .names
            .finish()
            .into_iter()
            .map(|display| SymbolName {
                search_key: display.to_lowercase().into_boxed_str(),
                display,
            })
            .collect();
        SymbolSearchIndex {
            owners: self.owners,
            names,
            descriptors: self.descriptors.finish(),
            classes: self.classes,
            members: self.members,
            resources: self.resources,
        }
    }
}

impl MemberVisitor for SymbolSearchIndexBuilder {
    fn visit(&mut self, member: MemberSummary) {
        let Some(&owner) = self.owner_indices.get(&member.owner) else {
            return;
        };
        let kind = match member.kind {
            MemberKind::Field => SymbolSearchKind::Field,
            MemberKind::Method => SymbolSearchKind::Method,
            _ => return,
        };
        self.members.push(MemberEntry {
            owner,
            name: self.names.intern(member.name),
            descriptor: self.descriptors.intern(member.descriptor),
            kind,
        });
    }
}

#[derive(Default)]
struct TextPoolBuilder {
    ids: HashMap<String, u32>,
}

impl TextPoolBuilder {
    fn intern(&mut self, text: String) -> u32 {
        if let Some(&id) = self.ids.get(&text) {
            return id;
        }
        let id = self.ids.len() as u32;
        self.ids.insert(text, id);
        id
    }

    fn finish(self) -> Vec<Box<str>> {
        let mut values = vec![Box::<str>::default(); self.ids.len()];
        for (text, id) in self.ids {
            values[id as usize] = text.into_boxed_str();
        }
        values
    }
}

struct RankedMatches {
    limit: usize,
    sequence: usize,
    heap: BinaryHeap<Reverse<(i32, usize, SearchHit)>>,
}

impl RankedMatches {
    fn new(limit: usize) -> Self {
        Self {
            limit,
            sequence: 0,
            heap: BinaryHeap::with_capacity(limit + 1),
        }
    }

    fn consider(&mut self, search_key: &str, query: &str, hit: SearchHit) {
        let Some(score) = score_key(search_key, query) else {
            return;
        };
        self.heap
            .push(Reverse((score, usize::MAX - self.sequence, hit)));
        self.sequence += 1;
        if self.heap.len() > self.limit {
            self.heap.pop();
        }
    }

    fn finish(self) -> Vec<SearchHit> {
        let mut matches = self
            .heap
            .into_iter()
            .map(|Reverse((score, order, hit))| (score, usize::MAX - order, hit))
            .collect::<Vec<_>>();
        matches.sort_unstable_by(|left, right| {
            right.0.cmp(&left.0).then_with(|| left.1.cmp(&right.1))
        });
        matches.into_iter().map(|(_, _, hit)| hit).collect()
    }
}

struct OwnerRecord {
    descriptor: Box<str>,
    qualified_name: Box<str>,
    display_name: Box<str>,
    package: Box<str>,
}

struct SymbolName {
    display: Box<str>,
    search_key: Box<str>,
}

struct ClassEntry {
    owner: u32,
    search_key: Box<str>,
}

struct MemberEntry {
    owner: u32,
    name: u32,
    descriptor: u32,
    kind: SymbolSearchKind,
}

struct ResourceEntry {
    path: Box<str>,
    search_key: Box<str>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SearchHit {
    Class(usize),
    Member(usize),
    Resource(usize),
}

fn score_key(search_key: &str, query: &str) -> Option<i32> {
    if let Some(offset) = search_key.find(query) {
        let boundary = offset == 0
            || search_key.as_bytes()[offset - 1].is_ascii_whitespace()
            || matches!(search_key.as_bytes()[offset - 1], b'.' | b'/' | b'$');
        return Some(10_000 - offset as i32 + if boundary { 1_000 } else { 0 });
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub enum SymbolSearchKind {
    Class,
    Field,
    Method,
    Resource,
}

#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct SymbolSearchResultDto {
    pub kind: SymbolSearchKind,
    pub name: String,
    pub detail: String,
    pub class_descriptor: Option<String>,
    pub descriptor: Option<String>,
    pub resource_path: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn search_ranking_prefers_boundaries_and_substrings() {
        assert!(score_key("open archive", "open") > score_key("reopen archive", "open"));
        assert!(score_key("open archive", "oar").is_none());
    }

    #[test]
    fn text_pool_interns_equal_values() {
        let mut pool = TextPoolBuilder::default();
        let first = pool.intern("value".to_string());
        let second = pool.intern("value".to_string());
        assert_eq!(first, second);
        assert_eq!(pool.finish(), [Box::<str>::from("value")]);
    }
}
