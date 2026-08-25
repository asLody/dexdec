use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::{Arc, RwLock};

use rayon::prelude::*;

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

    /// Recorded ancestor names of `class` — the closure its subtype queries
    /// walk — so repeated questions about one owner can be answered by
    /// membership instead of per-pair traversals.
    fn ancestor_names(&self, class: &str) -> Vec<String>;
}

#[derive(Debug)]
enum DistanceTable {
    Building(RwLock<HashMap<String, Arc<BTreeMap<String, usize>>>>),
    Frozen(Arc<HashMap<String, Arc<BTreeMap<String, usize>>>>),
}

impl Default for DistanceTable {
    fn default() -> Self {
        Self::Building(RwLock::new(HashMap::new()))
    }
}

#[derive(Debug, Default)]
pub struct ClassHierarchyIndex {
    parents: HashMap<String, BTreeSet<String>>,
    reference_types: HashMap<String, ReferenceTypeInfo>,
    base: Option<Arc<ClassHierarchyIndex>>,
    distances: DistanceTable,
    frozen_required: bool,
}

impl Clone for ClassHierarchyIndex {
    fn clone(&self) -> Self {
        Self {
            parents: self.parents.clone(),
            reference_types: self.reference_types.clone(),
            base: self.base.clone(),
            distances: match &self.distances {
                DistanceTable::Frozen(map) => DistanceTable::Frozen(Arc::clone(map)),
                DistanceTable::Building(cache) => {
                    DistanceTable::Building(RwLock::new(Self::read_cache(cache).clone()))
                }
            },
            frozen_required: self.frozen_required,
        }
    }
}

impl ClassHierarchyIndex {
    pub fn layered(base: Arc<ClassHierarchyIndex>) -> Self {
        Self {
            parents: HashMap::new(),
            reference_types: HashMap::new(),
            base: Some(base),
            distances: DistanceTable::default(),
            frozen_required: false,
        }
    }

    /// Precompute ancestor distances for every known type and freeze the table.
    ///
    /// After freeze, lookups are lock-free. Unknown starts still run a one-shot
    /// BFS and are not stored. Further graph mutation panics.
    pub fn freeze_distances(&mut self) {
        if matches!(self.distances, DistanceTable::Frozen(_)) {
            return;
        }

        let starts = self.distance_start_names();
        let computed = starts
            .into_par_iter()
            .map(|start| {
                let distances = self.compute_distances(&start);
                (start, distances)
            })
            .collect::<Vec<_>>();
        let mut map = HashMap::with_capacity(computed.len());
        for (start, distances) in computed {
            map.insert(start, distances);
        }
        self.distances = DistanceTable::Frozen(Arc::new(map));
    }

    pub(crate) fn set_frozen_required(&mut self, required: bool) {
        self.frozen_required = required;
    }

    /// Record `class` and its direct parents.
    ///
    /// # Panics
    ///
    /// Panics if distances have been frozen.
    pub fn add(&mut self, class: impl Into<String>, parents: impl IntoIterator<Item = String>) {
        self.require_building();
        self.parents
            .entry(class.into())
            .or_default()
            .extend(parents);
        self.clear_building_distances();
    }

    /// Record a declared reference type and its direct parents.
    ///
    /// # Panics
    ///
    /// Panics if distances have been frozen.
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

    /// Record many declared reference types.
    ///
    /// # Panics
    ///
    /// Panics if distances have been frozen.
    pub fn extend_declared_types(
        &mut self,
        declarations: impl IntoIterator<Item = (String, Vec<String>, ReferenceTypeInfo)>,
    ) {
        self.require_building();
        for (class, parents, info) in declarations {
            self.parents
                .entry(class.clone())
                .or_default()
                .extend(parents);
            self.reference_types.insert(class, info);
        }
        self.clear_building_distances();
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
        debug_assert!(
            !self.frozen_required || matches!(self.distances, DistanceTable::Frozen(_)),
            "ClassHierarchyIndex distances must be frozen before sharing"
        );
        match &self.distances {
            DistanceTable::Frozen(map) => {
                if let Some(distances) = map.get(start) {
                    return Arc::clone(distances);
                }
                if !self.owns_start(start) {
                    if let Some(base) = self.base.as_deref() {
                        return base.distances(start);
                    }
                }
                self.compute_distances(start)
            }
            DistanceTable::Building(cache) => {
                if let Some(distances) = Self::read_cache(cache).get(start).cloned() {
                    return distances;
                }
                let distances = self.compute_distances(start);
                Self::write_cache(cache).insert(start.to_string(), Arc::clone(&distances));
                distances
            }
        }
    }

    fn compute_distances(&self, start: &str) -> Arc<BTreeMap<String, usize>> {
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
        Arc::new(distances)
    }

    fn distance_start_names(&self) -> HashSet<String> {
        self.parents
            .keys()
            .chain(self.reference_types.keys())
            .cloned()
            .collect()
    }

    fn owns_start(&self, class: &str) -> bool {
        self.parents.contains_key(class) || self.reference_types.contains_key(class)
    }

    fn require_building(&self) {
        if matches!(self.distances, DistanceTable::Frozen(_)) {
            panic!("cannot mutate a frozen ClassHierarchyIndex");
        }
    }

    fn clear_building_distances(&self) {
        if let DistanceTable::Building(cache) = &self.distances {
            Self::write_cache(cache).clear();
        }
    }

    fn read_cache(
        cache: &RwLock<HashMap<String, Arc<BTreeMap<String, usize>>>>,
    ) -> std::sync::RwLockReadGuard<'_, HashMap<String, Arc<BTreeMap<String, usize>>>> {
        match cache.read() {
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

impl ClassHierarchyIndex {
    /// True when `expected` is a recorded ancestor of `value`.
    ///
    /// A hit is definitive Yes. A miss still has to BFS so incomplete graphs
    /// can return Unknown instead of No.
    fn recorded_ancestor(&self, value: &str, expected: &str) -> bool {
        if value == expected || expected == "java/lang/Object" {
            return true;
        }
        self.distances(value).contains_key(expected)
    }

    /// Recorded ancestor names of `class` — the same closure its subtype
    /// queries walk — so repeated questions about one owner can be answered
    /// by membership instead of per-pair walks. Includes `class` itself and
    /// the `java/lang/Object` fallback entry.
    pub fn ancestor_names(&self, class: &str) -> Vec<String> {
        self.distances(class).keys().cloned().collect()
    }
}

impl TypeHierarchy for ClassHierarchyIndex {
    fn subtype_relation(&self, value: &str, expected: &str) -> SubtypeRelation {
        if self.recorded_ancestor(value, expected) {
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

    fn ancestor_names(&self, class: &str) -> Vec<String> {
        Self::ancestor_names(self, class)
    }

    fn least_common_supertype(&self, left: &str, right: &str) -> Option<String> {
        if self.recorded_ancestor(left, right) {
            return Some(right.to_string());
        }
        if self.recorded_ancestor(right, left) {
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
                        && self.recorded_ancestor(other, candidate)
                        && !self.recorded_ancestor(candidate, other)
                })
            })
            .min()
            .map(|(_, _, candidate)| (*candidate).clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_hierarchy() -> ClassHierarchyIndex {
        let mut index = ClassHierarchyIndex::default();
        index.add("pkg/Child", ["pkg/Parent".to_string()]);
        index.add("pkg/Parent", ["java/lang/Object".to_string()]);
        index.add("java/lang/Object", Vec::<String>::new());
        index.add("pkg/Orphan", Vec::<String>::new());
        index
    }

    #[test]
    fn freeze_clone_shares_distance_table() {
        let mut index = sample_hierarchy();
        index.freeze_distances();
        let cloned = index.clone();
        match (&index.distances, &cloned.distances) {
            (DistanceTable::Frozen(left), DistanceTable::Frozen(right)) => {
                assert!(Arc::ptr_eq(left, right));
            }
            _ => panic!("expected frozen distance tables"),
        }
    }

    #[test]
    fn freeze_distances_includes_object_sentinel() {
        let mut index = sample_hierarchy();
        index.freeze_distances();
        assert_eq!(
            index
                .distances("pkg/Orphan")
                .get("java/lang/Object")
                .copied(),
            Some(usize::MAX / 4)
        );
        assert_eq!(
            index
                .distances("java/lang/Object")
                .get("java/lang/Object")
                .copied(),
            Some(0)
        );
    }

    #[test]
    #[should_panic(expected = "cannot mutate a frozen ClassHierarchyIndex")]
    fn add_on_frozen_panics() {
        let mut index = sample_hierarchy();
        index.freeze_distances();
        index.add("pkg/Other", Vec::<String>::new());
    }

    #[test]
    fn freeze_preserves_subtype_and_lcs() {
        let mut index = sample_hierarchy();
        index.add("pkg/Left", ["pkg/Shared".to_string()]);
        index.add("pkg/Right", ["pkg/Shared".to_string()]);
        index.add("pkg/Shared", ["java/lang/Object".to_string()]);
        let pairs = [
            ("pkg/Child", "pkg/Parent"),
            ("pkg/Parent", "pkg/Child"),
            ("pkg/Child", "java/lang/Object"),
            ("pkg/Orphan", "pkg/Child"),
            ("pkg/Left", "pkg/Right"),
            ("pkg/Right", "pkg/Left"),
            ("pkg/Left", "pkg/Shared"),
        ];
        let before_rel: Vec<_> = pairs
            .iter()
            .map(|(left, right)| index.subtype_relation(left, right))
            .collect();
        let before_lcs: Vec<_> = pairs
            .iter()
            .map(|(left, right)| index.least_common_supertype(left, right))
            .collect();
        index.freeze_distances();
        let after_rel: Vec<_> = pairs
            .iter()
            .map(|(left, right)| index.subtype_relation(left, right))
            .collect();
        let after_lcs: Vec<_> = pairs
            .iter()
            .map(|(left, right)| index.least_common_supertype(left, right))
            .collect();
        assert_eq!(before_rel, after_rel);
        assert_eq!(before_lcs, after_lcs);
        assert_eq!(
            index.least_common_supertype("pkg/Left", "pkg/Right"),
            Some("pkg/Shared".to_string())
        );
        assert!(index.recorded_ancestor("pkg/Child", "pkg/Parent"));
        assert!(index.recorded_ancestor("pkg/Child", "java/lang/Object"));
        assert!(!index.recorded_ancestor("pkg/Orphan", "pkg/Child"));
    }

    #[test]
    fn frozen_miss_does_not_grow_the_map() {
        let mut index = sample_hierarchy();
        index.freeze_distances();
        let keys_before = frozen_keys(&index);
        assert!(!keys_before.contains("not/A/Key"));
        let first = index.distances("not/A/Key");
        let second = index.distances("not/A/Key");
        assert_eq!(first.get("not/A/Key").copied(), Some(0));
        assert_eq!(*first, *second);
        assert_eq!(frozen_keys(&index), keys_before);
    }

    #[test]
    fn layered_freeze_delegates_base_starts() {
        let mut base = ClassHierarchyIndex::default();
        base.add("android/view/View", ["java/lang/Object".to_string()]);
        base.add("java/lang/Object", Vec::<String>::new());
        base.freeze_distances();
        let mut index = ClassHierarchyIndex::layered(Arc::new(base));
        index.add("pkg/MyView", ["android/view/View".to_string()]);
        index.freeze_distances();
        let keys = frozen_keys(&index);
        assert!(keys.contains("pkg/MyView"));
        assert!(
            !keys.contains("android/view/View"),
            "APK-layer freeze must not copy platform starts"
        );
        assert_eq!(
            index
                .distances("android/view/View")
                .get("java/lang/Object")
                .copied(),
            Some(1)
        );
        assert_eq!(
            index.least_common_supertype("pkg/MyView", "android/view/View"),
            Some("android/view/View".to_string())
        );
    }

    #[test]
    #[should_panic(expected = "cannot mutate a frozen ClassHierarchyIndex")]
    fn extend_declared_types_on_frozen_panics() {
        let mut index = sample_hierarchy();
        index.freeze_distances();
        index.extend_declared_types([(
            "pkg/Other".to_string(),
            Vec::new(),
            ReferenceTypeInfo {
                is_interface: false,
                is_final: false,
            },
        )]);
    }

    fn frozen_keys(index: &ClassHierarchyIndex) -> HashSet<String> {
        match &index.distances {
            DistanceTable::Frozen(map) => map.keys().cloned().collect(),
            DistanceTable::Building(_) => panic!("expected frozen distance table"),
        }
    }
}
