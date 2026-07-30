use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::sync::{Arc, RwLock};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubtypeRelation {
    Yes,
    No,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReferenceTypeInfo {
    pub is_interface: bool,
    pub is_final: bool,
}

pub trait TypeHierarchy: Send + Sync {
    fn subtype_relation(&self, value: &str, expected: &str) -> SubtypeRelation;

    fn is_subtype(&self, value: &str, expected: &str) -> bool {
        self.subtype_relation(value, expected) == SubtypeRelation::Yes
    }

    fn least_common_supertype(&self, left: &str, right: &str) -> Option<String>;
}

#[derive(Debug, Default)]
pub struct ClassHierarchyIndex {
    parents: HashMap<String, BTreeSet<String>>,
    reference_types: HashMap<String, ReferenceTypeInfo>,
    base: Option<Arc<ClassHierarchyIndex>>,
    distances: Arc<RwLock<HashMap<String, Arc<BTreeMap<String, usize>>>>>,
}

impl Clone for ClassHierarchyIndex {
    fn clone(&self) -> Self {
        Self {
            parents: self.parents.clone(),
            reference_types: self.reference_types.clone(),
            base: self.base.clone(),
            distances: Arc::default(),
        }
    }
}

impl ClassHierarchyIndex {
    pub fn layered(base: Arc<ClassHierarchyIndex>) -> Self {
        Self {
            parents: HashMap::new(),
            reference_types: HashMap::new(),
            base: Some(base),
            distances: Arc::default(),
        }
    }

    pub fn add(&mut self, class: impl Into<String>, parents: impl IntoIterator<Item = String>) {
        self.parents
            .entry(class.into())
            .or_default()
            .extend(parents);
        Self::write_cache(&self.distances).clear();
    }

    pub fn add_declared_type(
        &mut self,
        class: impl Into<String>,
        parents: impl IntoIterator<Item = String>,
        info: ReferenceTypeInfo,
    ) {
        let class = class.into();
        self.add(class.clone(), parents);
        self.reference_types.insert(class, info);
    }

    pub fn extend_declared_types(
        &mut self,
        declarations: impl IntoIterator<Item = (String, Vec<String>, ReferenceTypeInfo)>,
    ) {
        for (class, parents, info) in declarations {
            self.parents
                .entry(class.clone())
                .or_default()
                .extend(parents);
            self.reference_types.insert(class, info);
        }
        Self::write_cache(&self.distances).clear();
    }

    pub fn is_cast_convertible(&self, source: &str, target: &str) -> bool {
        if self.is_subtype(source, target) || self.is_subtype(target, source) {
            return true;
        }
        let (Some(source), Some(target)) =
            (self.reference_type(source), self.reference_type(target))
        else {
            return false;
        };
        match (source.is_interface, target.is_interface) {
            (true, true) => true,
            (true, false) => !target.is_final,
            (false, true) => !source.is_final,
            (false, false) => false,
        }
    }

    fn distances(&self, start: &str) -> Arc<BTreeMap<String, usize>> {
        if let Some(distances) = self.read_cache().get(start).cloned() {
            return distances;
        }
        let mut distances = BTreeMap::from([(start.to_string(), 0)]);
        let mut pending = VecDeque::from([(start.to_string(), 0)]);
        while let Some((class, distance)) = pending.pop_front() {
            for parent in self.direct_parents(&class) {
                if distances.contains_key(parent) {
                    continue;
                }
                distances.insert(parent.clone(), distance + 1);
                pending.push_back((parent.clone(), distance + 1));
            }
        }
        distances
            .entry("java/lang/Object".to_string())
            .or_insert(usize::MAX / 4);
        let distances = Arc::new(distances);
        Self::write_cache(&self.distances).insert(start.to_string(), Arc::clone(&distances));
        distances
    }

    fn read_cache(
        &self,
    ) -> std::sync::RwLockReadGuard<'_, HashMap<String, Arc<BTreeMap<String, usize>>>> {
        match self.distances.read() {
            Ok(cache) => cache,
            Err(poisoned) => poisoned.into_inner(),
        }
    }

    fn write_cache(
        cache: &RwLock<HashMap<String, Arc<BTreeMap<String, usize>>>>,
    ) -> std::sync::RwLockWriteGuard<'_, HashMap<String, Arc<BTreeMap<String, usize>>>> {
        match cache.write() {
            Ok(cache) => cache,
            Err(poisoned) => poisoned.into_inner(),
        }
    }

    fn direct_parents<'a>(&'a self, class: &str) -> impl Iterator<Item = &'a String> {
        self.parent_set(class).into_iter().flatten()
    }

    fn parent_set(&self, class: &str) -> Option<&BTreeSet<String>> {
        self.parents
            .get(class)
            .or_else(|| self.base.as_deref().and_then(|base| base.parent_set(class)))
    }

    fn reference_type(&self, class: &str) -> Option<ReferenceTypeInfo> {
        self.reference_types.get(class).copied().or_else(|| {
            self.base
                .as_deref()
                .and_then(|base| base.reference_type(class))
        })
    }
}

impl TypeHierarchy for ClassHierarchyIndex {
    fn subtype_relation(&self, value: &str, expected: &str) -> SubtypeRelation {
        if value == expected || expected == "java/lang/Object" {
            return SubtypeRelation::Yes;
        }
        let mut visited = BTreeSet::new();
        let mut pending = VecDeque::from([value]);
        let mut incomplete = false;
        while let Some(class) = pending.pop_front() {
            if !visited.insert(class) {
                continue;
            }
            let Some(parents) = self.parent_set(class) else {
                incomplete = true;
                continue;
            };
            if parents.contains(expected) {
                return SubtypeRelation::Yes;
            }
            pending.extend(parents.iter().map(String::as_str));
        }
        if incomplete {
            SubtypeRelation::Unknown
        } else {
            SubtypeRelation::No
        }
    }

    fn least_common_supertype(&self, left: &str, right: &str) -> Option<String> {
        if self.is_subtype(left, right) {
            return Some(right.to_string());
        }
        if self.is_subtype(right, left) {
            return Some(left.to_string());
        }
        let left_distances = self.distances(left);
        let right_distances = self.distances(right);
        let candidates = left_distances
            .iter()
            .filter_map(|(candidate, left_distance)| {
                let right_distance = right_distances.get(candidate)?;
                Some((
                    (*left_distance).max(*right_distance),
                    left_distance.saturating_add(*right_distance),
                    candidate,
                ))
            })
            .collect::<Vec<_>>();
        candidates
            .iter()
            .filter(|(_, _, candidate)| {
                !candidates.iter().any(|(_, _, other)| {
                    other != candidate
                        && self.is_subtype(other, candidate)
                        && !self.is_subtype(candidate, other)
                })
            })
            .min()
            .map(|(_, _, candidate)| (*candidate).clone())
    }
}
