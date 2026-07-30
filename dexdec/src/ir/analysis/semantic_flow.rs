//! Occurrence-sensitive control flow over structured Semantic IR.
//!
//! Every numbered semantic site owns a before/after program point. Structural
//! nodes connect those points without projecting cloned occurrences back onto
//! one original CFG block.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::{
    RegionId, SemanticExpression, SemanticLabel, SemanticLeave, SemanticLeaveKind,
    SemanticLoopControl, SemanticLoopKind, SemanticNode, SemanticPredicate, SemanticSiteId,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SemanticFlowPoint {
    Before(SemanticSiteId),
    After(SemanticSiteId),
    Synthetic(u64),
}

impl SemanticFlowPoint {
    pub fn before(site: SemanticSiteId) -> Self {
        Self::Before(site)
    }

    pub fn after(site: SemanticSiteId) -> Self {
        Self::After(site)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SemanticFlowEdgeKind {
    Normal,
    Exceptional,
    LoopBack,
    FinallyEnter(u64),
    FinallyResume(u64),
    FinallyOverride,
}

#[derive(Debug, Clone, Default)]
pub struct SemanticFlowGraph {
    predecessors: BTreeMap<SemanticFlowPoint, Vec<(SemanticFlowPoint, SemanticFlowEdgeKind)>>,
    successors: BTreeMap<SemanticFlowPoint, Vec<SemanticFlowPoint>>,
    entries: BTreeSet<SemanticFlowPoint>,
    complete: bool,
}

#[derive(Debug, Clone)]
pub struct SemanticReachability {
    components: BTreeMap<SemanticFlowPoint, usize>,
    reachable: Vec<DefinitionSet>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct DefinitionSet {
    words: Vec<u64>,
}

impl DefinitionSet {
    fn new(definitions: usize) -> Self {
        Self {
            words: vec![0; definitions.div_ceil(u64::BITS as usize)],
        }
    }

    fn insert(&mut self, definition: usize) {
        self.words[definition / u64::BITS as usize] |= 1 << (definition % u64::BITS as usize);
    }

    fn contains(&self, definition: usize) -> bool {
        self.words
            .get(definition / u64::BITS as usize)
            .is_some_and(|word| word & (1 << (definition % u64::BITS as usize)) != 0)
    }

    fn union_with(&mut self, other: &Self) {
        for (word, other) in self.words.iter_mut().zip(&other.words) {
            *word |= other;
        }
    }

    fn union_delta(&mut self, other: &Self, delta: &mut Self) -> bool {
        let mut changed = false;
        for ((word, other), delta) in self
            .words
            .iter_mut()
            .zip(&other.words)
            .zip(&mut delta.words)
        {
            let added = *other & !*word;
            *word |= added;
            *delta |= added;
            changed |= added != 0;
        }
        changed
    }

    fn union_delta_without(&mut self, other: &Self, excluded: &Self, delta: &mut Self) -> bool {
        let mut changed = false;
        for (((word, other), excluded), delta) in self
            .words
            .iter_mut()
            .zip(&other.words)
            .zip(&excluded.words)
            .zip(&mut delta.words)
        {
            let added = (*other & !*excluded) & !*word;
            *word |= added;
            *delta |= added;
            changed |= added != 0;
        }
        changed
    }

    fn remove_with(&mut self, other: &Self) {
        for (word, other) in self.words.iter_mut().zip(&other.words) {
            *word &= !other;
        }
    }

    fn differs_under(&self, other: &Self, mask: &Self) -> bool {
        self.words
            .iter()
            .zip(&other.words)
            .zip(&mask.words)
            .any(|((left, right), mask)| ((left ^ right) & mask) != 0)
    }

    fn members(&self) -> impl Iterator<Item = usize> + '_ {
        self.words
            .iter()
            .enumerate()
            .flat_map(|(word_index, word)| {
                let mut remaining = *word;
                std::iter::from_fn(move || {
                    if remaining == 0 {
                        return None;
                    }
                    let bit = remaining.trailing_zeros() as usize;
                    remaining &= remaining - 1;
                    Some(word_index * u64::BITS as usize + bit)
                })
            })
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SemanticValueDefinition {
    point: SemanticFlowPoint,
    value: usize,
    ordinal: usize,
}

impl SemanticValueDefinition {
    pub fn new(point: SemanticFlowPoint, value: usize, ordinal: usize) -> Self {
        Self {
            point,
            value,
            ordinal,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct SemanticReachingValues {
    reaching: BTreeMap<SemanticFlowPoint, DefinitionSet>,
    definitions: Vec<(usize, usize)>,
    value_masks: Vec<DefinitionSet>,
}

impl SemanticReachingValues {
    pub fn at(&self, value: usize, point: SemanticFlowPoint) -> Option<Vec<usize>> {
        let reaching = self.reaching.get(&point)?;
        Some(
            reaching
                .members()
                .filter_map(|definition| {
                    let (definition_value, ordinal) = self.definitions[definition];
                    (definition_value == value).then_some(ordinal)
                })
                .collect(),
        )
    }

    pub fn unchanged(
        &self,
        value: usize,
        source: SemanticFlowPoint,
        target: SemanticFlowPoint,
    ) -> Option<bool> {
        let source = self.reaching.get(&source)?;
        let target = self.reaching.get(&target)?;
        let mask = self.value_masks.get(value)?;
        Some(!source.differs_under(target, mask))
    }
}

impl SemanticReachability {
    fn analyze(graph: &SemanticFlowGraph) -> Self {
        let points = graph
            .predecessors
            .keys()
            .chain(graph.successors.keys())
            .chain(graph.successors.values().flatten())
            .chain(
                graph
                    .predecessors
                    .values()
                    .flatten()
                    .map(|(predecessor, _)| predecessor),
            )
            .chain(graph.entries.iter())
            .copied()
            .collect::<BTreeSet<_>>();
        let mut visited = BTreeSet::new();
        let mut finish = Vec::with_capacity(points.len());
        for root in &points {
            if !visited.insert(*root) {
                continue;
            }
            let mut stack = vec![(*root, 0usize)];
            while let Some((point, successor_index)) = stack.last_mut() {
                let successors = graph
                    .successors
                    .get(point)
                    .map(Vec::as_slice)
                    .unwrap_or_default();
                if *successor_index < successors.len() {
                    let successor = successors[*successor_index];
                    *successor_index += 1;
                    if visited.insert(successor) {
                        stack.push((successor, 0));
                    }
                } else {
                    finish.push(*point);
                    stack.pop();
                }
            }
        }

        let mut components = BTreeMap::new();
        let mut component_count = 0usize;
        for root in finish.into_iter().rev() {
            if components.contains_key(&root) {
                continue;
            }
            let component = component_count;
            component_count += 1;
            components.insert(root, component);
            let mut stack = vec![root];
            while let Some(point) = stack.pop() {
                for (predecessor, _) in graph
                    .predecessors
                    .get(&point)
                    .into_iter()
                    .flat_map(Vec::as_slice)
                {
                    if !components.contains_key(predecessor) {
                        components.insert(*predecessor, component);
                        stack.push(*predecessor);
                    }
                }
            }
        }

        let mut successors = vec![BTreeSet::new(); component_count];
        let mut indegree = vec![0usize; component_count];
        for (point, point_successors) in &graph.successors {
            let source = components[point];
            for successor in point_successors {
                let target = components[successor];
                if source != target && successors[source].insert(target) {
                    indegree[target] += 1;
                }
            }
        }
        let mut ready = indegree
            .iter()
            .enumerate()
            .filter_map(|(component, degree)| (*degree == 0).then_some(component))
            .collect::<BTreeSet<_>>();
        let mut topological = Vec::with_capacity(component_count);
        while let Some(component) = ready.pop_first() {
            topological.push(component);
            for successor in &successors[component] {
                indegree[*successor] -= 1;
                if indegree[*successor] == 0 {
                    ready.insert(*successor);
                }
            }
        }
        debug_assert_eq!(topological.len(), component_count);

        let mut reachable = (0..component_count)
            .map(|component| {
                let mut set = DefinitionSet::new(component_count);
                set.insert(component);
                set
            })
            .collect::<Vec<_>>();
        for component in topological.into_iter().rev() {
            for successor in &successors[component] {
                let successor_reachability = reachable[*successor].clone();
                reachable[component].union_with(&successor_reachability);
            }
        }
        Self {
            components,
            reachable,
        }
    }

    pub fn reaches(&self, source: SemanticFlowPoint, target: SemanticFlowPoint) -> bool {
        let (Some(source), Some(target)) =
            (self.components.get(&source), self.components.get(&target))
        else {
            return false;
        };
        self.reachable[*source].contains(*target)
    }

    pub fn reaches_any_between(
        &self,
        source: SemanticFlowPoint,
        target: SemanticFlowPoint,
        candidates: &BTreeSet<SemanticFlowPoint>,
    ) -> bool {
        candidates
            .iter()
            .any(|candidate| self.reaches(source, *candidate) && self.reaches(*candidate, target))
    }
}

impl SemanticFlowGraph {
    pub fn analyze(root: &SemanticNode) -> Self {
        SemanticFlowBuilder::new().build(root)
    }

    pub fn is_complete(&self) -> bool {
        self.complete
    }

    pub fn points(&self) -> BTreeSet<SemanticFlowPoint> {
        self.predecessors
            .keys()
            .chain(self.successors.keys())
            .chain(self.successors.values().flatten())
            .chain(
                self.predecessors
                    .values()
                    .flatten()
                    .map(|(predecessor, _)| predecessor),
            )
            .chain(&self.entries)
            .copied()
            .collect()
    }

    pub fn successors(&self, point: SemanticFlowPoint) -> &[SemanticFlowPoint] {
        self.successors
            .get(&point)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn predecessors(
        &self,
        point: SemanticFlowPoint,
    ) -> impl Iterator<Item = SemanticFlowPoint> + '_ {
        self.predecessors
            .get(&point)
            .into_iter()
            .flatten()
            .map(|(predecessor, _)| *predecessor)
    }

    pub fn reachability(&self) -> SemanticReachability {
        SemanticReachability::analyze(self)
    }

    /// Returns whether at least one path connects `source` to `target`.
    pub fn reaches(&self, source: SemanticFlowPoint, target: SemanticFlowPoint) -> bool {
        if source == target {
            return true;
        }
        let mut visited = BTreeSet::new();
        let mut pending = vec![source];
        while let Some(point) = pending.pop() {
            if !visited.insert(point) {
                continue;
            }
            let Some(successors) = self.successors.get(&point) else {
                continue;
            };
            if successors.contains(&target) {
                return true;
            }
            pending.extend(successors.iter().copied());
        }
        false
    }

    /// Proves that every maximal path leaving `source` reaches `target`.
    ///
    /// A terminal path or a cycle that avoids `target` rejects the proof. This
    /// is intentionally stronger than ordinary reachability because sinking a
    /// throwing or observable expression must preserve execution count.
    pub fn must_reach(&self, source: SemanticFlowPoint, target: SemanticFlowPoint) -> bool {
        if source == target {
            return true;
        }
        let mut colors = BTreeMap::<SemanticFlowPoint, VisitColor>::new();
        let mut pending = vec![(source, false)];
        while let Some((point, leaving)) = pending.pop() {
            if point == target {
                continue;
            }
            if leaving {
                colors.insert(point, VisitColor::Complete);
                continue;
            }
            match colors.get(&point) {
                Some(VisitColor::Active) => return false,
                Some(VisitColor::Complete) => continue,
                None => {}
            }
            let Some(successors) = self.successors.get(&point) else {
                return false;
            };
            if successors.is_empty() {
                return false;
            }
            colors.insert(point, VisitColor::Active);
            pending.push((point, true));
            pending.extend(
                successors
                    .iter()
                    .rev()
                    .copied()
                    .map(|successor| (successor, false)),
            );
        }
        true
    }

    pub fn reaching_values(
        &self,
        definitions: &[SemanticValueDefinition],
        value_count: usize,
        targets: &BTreeSet<SemanticFlowPoint>,
    ) -> SemanticReachingValues {
        let definition_count = definitions.len();
        let mut generated = BTreeMap::<SemanticFlowPoint, DefinitionSet>::new();
        let mut value_masks = (0..value_count)
            .map(|_| DefinitionSet::new(definition_count))
            .collect::<Vec<_>>();
        for (index, definition) in definitions.iter().enumerate() {
            generated
                .entry(definition.point)
                .or_insert_with(|| DefinitionSet::new(definition_count))
                .insert(index);
            value_masks[definition.value].insert(index);
        }
        let mut killed = BTreeMap::<SemanticFlowPoint, DefinitionSet>::new();
        for (point, generated_at_point) in &generated {
            let killed_at_point = killed
                .entry(*point)
                .or_insert_with(|| DefinitionSet::new(definition_count));
            for definition in generated_at_point.members() {
                killed_at_point.union_with(&value_masks[definitions[definition].value]);
            }
        }
        if !self.has_cleanup_continuations() {
            return self.reaching_values_plain(
                definitions,
                targets,
                generated,
                killed,
                value_masks,
            );
        }
        self.reaching_values_with_cleanup(definitions, targets, generated, killed, value_masks)
    }

    fn has_cleanup_continuations(&self) -> bool {
        self.predecessors.values().flatten().any(|(_, edge)| {
            matches!(
                edge,
                SemanticFlowEdgeKind::FinallyEnter(_)
                    | SemanticFlowEdgeKind::FinallyResume(_)
                    | SemanticFlowEdgeKind::FinallyOverride
            )
        })
    }

    fn reaching_values_plain(
        &self,
        definitions: &[SemanticValueDefinition],
        targets: &BTreeSet<SemanticFlowPoint>,
        generated: BTreeMap<SemanticFlowPoint, DefinitionSet>,
        killed: BTreeMap<SemanticFlowPoint, DefinitionSet>,
        value_masks: Vec<DefinitionSet>,
    ) -> SemanticReachingValues {
        let definition_count = definitions.len();
        let nodes = self.reaching_slice(targets);
        let points = nodes.iter().copied().collect::<Vec<_>>();
        let ids = points
            .iter()
            .copied()
            .enumerate()
            .map(|(index, point)| (point, index))
            .collect::<BTreeMap<_, _>>();
        let mut successors = vec![Vec::new(); points.len()];
        for (index, point) in points.iter().enumerate() {
            for successor in self
                .successors
                .get(point)
                .into_iter()
                .flat_map(Vec::as_slice)
            {
                if let Some(&successor) = ids.get(successor) {
                    successors[index].push(successor);
                }
            }
        }
        let entries = points
            .iter()
            .map(|point| self.entries.contains(point))
            .collect::<Vec<_>>();
        let mut facts = vec![DefinitionSet::new(definition_count); points.len()];
        let mut deltas = vec![DefinitionSet::new(definition_count); points.len()];
        let mut reachable = vec![false; points.len()];
        let mut pending = VecDeque::new();
        let mut queued = vec![false; points.len()];
        for (node, entry) in entries.iter().copied().enumerate() {
            if !entry {
                continue;
            }
            reachable[node] = true;
            if let Some(generated) = generated.get(&points[node]) {
                facts[node].union_delta(generated, &mut deltas[node]);
            }
            queued[node] = true;
            pending.push_back(node);
        }
        while let Some(node) = pending.pop_front() {
            queued[node] = false;
            let delta = std::mem::replace(&mut deltas[node], DefinitionSet::new(definition_count));
            for successor in &successors[node] {
                let first_reach = !reachable[*successor];
                if first_reach {
                    reachable[*successor] = true;
                    if let Some(generated) = generated.get(&points[*successor]) {
                        facts[*successor].union_delta(generated, &mut deltas[*successor]);
                    }
                }
                let changed = match killed.get(&points[*successor]) {
                    Some(killed) => facts[*successor].union_delta_without(
                        &delta,
                        killed,
                        &mut deltas[*successor],
                    ),
                    None => facts[*successor].union_delta(&delta, &mut deltas[*successor]),
                };
                if (first_reach || changed) && !queued[*successor] {
                    queued[*successor] = true;
                    pending.push_back(*successor);
                }
            }
        }
        let mut reaching = points
            .into_iter()
            .enumerate()
            .filter_map(|(index, point)| {
                (reachable[index] && targets.contains(&point))
                    .then(|| (point, facts[index].clone()))
            })
            .collect::<BTreeMap<_, _>>();
        self.insert_unreachable_target_bottoms(&mut reaching, targets, definition_count);
        SemanticReachingValues {
            reaching,
            definitions: definitions
                .iter()
                .map(|definition| (definition.value, definition.ordinal))
                .collect(),
            value_masks,
        }
    }

    fn reaching_values_with_cleanup(
        &self,
        definitions: &[SemanticValueDefinition],
        targets: &BTreeSet<SemanticFlowPoint>,
        generated: BTreeMap<SemanticFlowPoint, DefinitionSet>,
        killed: BTreeMap<SemanticFlowPoint, DefinitionSet>,
        value_masks: Vec<DefinitionSet>,
    ) -> SemanticReachingValues {
        let definition_count = definitions.len();
        let nodes = self.reaching_slice(targets);
        let mut outgoing =
            BTreeMap::<SemanticFlowPoint, Vec<(SemanticFlowPoint, SemanticFlowEdgeKind)>>::new();
        for (target, predecessors) in &self.predecessors {
            if !nodes.contains(target) {
                continue;
            }
            for (predecessor, edge) in predecessors {
                if nodes.contains(predecessor) {
                    outgoing
                        .entry(*predecessor)
                        .or_default()
                        .push((*target, *edge));
                }
            }
        }

        let mut states = Vec::<(SemanticFlowPoint, Vec<u64>)>::new();
        let mut state_ids = BTreeMap::<(SemanticFlowPoint, Vec<u64>), usize>::new();
        let mut successors = Vec::<Vec<usize>>::new();
        let mut predecessors = Vec::<Vec<usize>>::new();
        let mut entries = Vec::<bool>::new();
        let mut pending = VecDeque::new();
        for entry in self.entries.iter().filter(|entry| nodes.contains(entry)) {
            let id = states.len();
            let state = (*entry, Vec::new());
            if state_ids.insert(state.clone(), id).is_none() {
                states.push(state);
                successors.push(Vec::new());
                predecessors.push(Vec::new());
                entries.push(true);
                pending.push_back(id);
            }
        }
        while let Some(state_id) = pending.pop_front() {
            let (point, continuation) = states[state_id].clone();
            for (successor, edge) in outgoing.get(&point).into_iter().flat_map(Vec::as_slice) {
                let Some(next_continuation) = edge.transfer(&continuation) else {
                    continue;
                };
                let next_state = (*successor, next_continuation);
                let next_id = if let Some(id) = state_ids.get(&next_state) {
                    *id
                } else {
                    let id = states.len();
                    state_ids.insert(next_state.clone(), id);
                    states.push(next_state);
                    successors.push(Vec::new());
                    predecessors.push(Vec::new());
                    entries.push(false);
                    pending.push_back(id);
                    id
                };
                if !successors[state_id].contains(&next_id) {
                    successors[state_id].push(next_id);
                    predecessors[next_id].push(state_id);
                }
            }
        }

        let mut facts = vec![DefinitionSet::new(definition_count); states.len()];
        let mut initialized = vec![false; states.len()];
        let mut pending = (0..states.len()).collect::<VecDeque<_>>();
        let mut queued = vec![true; states.len()];
        while let Some(state_id) = pending.pop_front() {
            queued[state_id] = false;
            let mut next = DefinitionSet::new(definition_count);
            let mut reachable = entries[state_id];
            for predecessor in &predecessors[state_id] {
                if initialized[*predecessor] {
                    reachable = true;
                    next.union_with(&facts[*predecessor]);
                }
            }
            if !reachable {
                continue;
            }
            let point = states[state_id].0;
            if let Some(generated_at_point) = generated.get(&point) {
                next.remove_with(&killed[&point]);
                next.union_with(generated_at_point);
            }
            if initialized[state_id] && facts[state_id] == next {
                continue;
            }
            facts[state_id] = next;
            initialized[state_id] = true;
            for successor in &successors[state_id] {
                if !queued[*successor] {
                    queued[*successor] = true;
                    pending.push_back(*successor);
                }
            }
        }

        let mut reaching = BTreeMap::<SemanticFlowPoint, DefinitionSet>::new();
        for (state_id, (point, _)) in states.into_iter().enumerate() {
            if initialized[state_id] && targets.contains(&point) {
                reaching
                    .entry(point)
                    .or_insert_with(|| DefinitionSet::new(definition_count))
                    .union_with(&facts[state_id]);
            }
        }
        self.insert_unreachable_target_bottoms(&mut reaching, targets, definition_count);
        SemanticReachingValues {
            reaching,
            definitions: definitions
                .iter()
                .map(|definition| (definition.value, definition.ordinal))
                .collect(),
            value_masks,
        }
    }

    fn insert_unreachable_target_bottoms(
        &self,
        reaching: &mut BTreeMap<SemanticFlowPoint, DefinitionSet>,
        targets: &BTreeSet<SemanticFlowPoint>,
        definition_count: usize,
    ) {
        for target in targets.iter().copied().filter(|target| {
            self.entries.contains(target)
                || self.predecessors.contains_key(target)
                || self.successors.contains_key(target)
        }) {
            reaching
                .entry(target)
                .or_insert_with(|| DefinitionSet::new(definition_count));
        }
    }

    fn reaching_slice(&self, targets: &BTreeSet<SemanticFlowPoint>) -> BTreeSet<SemanticFlowPoint> {
        let mut nodes = targets.clone();
        let mut ancestors = targets.iter().copied().collect::<VecDeque<_>>();
        while let Some(node) = ancestors.pop_front() {
            for (predecessor, _) in self
                .predecessors
                .get(&node)
                .into_iter()
                .flat_map(Vec::as_slice)
            {
                if nodes.insert(*predecessor) {
                    ancestors.push_back(*predecessor);
                }
            }
        }
        nodes
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitColor {
    Active,
    Complete,
}

impl SemanticFlowEdgeKind {
    fn transfer(self, continuation: &[u64]) -> Option<Vec<u64>> {
        let mut result = continuation.to_vec();
        match self {
            Self::Normal | Self::Exceptional | Self::LoopBack => {}
            Self::FinallyEnter(token) => {
                if result.contains(&token) {
                    return None;
                }
                result.push(token);
            }
            Self::FinallyResume(token) => {
                if result.pop() != Some(token) {
                    return None;
                }
            }
            Self::FinallyOverride => {
                result.pop()?;
            }
        }
        Some(result)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Completion {
    Return,
    Throw,
    Break(RegionId),
    Continue(RegionId),
    BreakLabel(SemanticLabel),
    ContinueLabel(SemanticLabel),
    Open,
}

enum FinallyContinuation {
    Normal,
    Abrupt(Completion),
    Throwing,
}

#[derive(Default)]
struct FlowFragment {
    entry: Option<SemanticFlowPoint>,
    normal: bool,
    exits: BTreeSet<SemanticFlowPoint>,
    abrupt: BTreeMap<Completion, BTreeSet<SemanticFlowPoint>>,
    throwing: BTreeSet<SemanticFlowPoint>,
}

impl FlowFragment {
    fn identity() -> Self {
        Self {
            normal: true,
            ..Self::default()
        }
    }

    fn is_identity(&self) -> bool {
        self.entry.is_none()
            && self.normal
            && self.exits.is_empty()
            && self.abrupt.is_empty()
            && self.throwing.is_empty()
    }

    fn site(site: SemanticSiteId, may_throw: bool) -> Self {
        let before = SemanticFlowPoint::before(site);
        let after = SemanticFlowPoint::after(site);
        Self {
            entry: Some(before),
            normal: true,
            exits: BTreeSet::from([after]),
            abrupt: BTreeMap::new(),
            throwing: may_throw
                .then(|| BTreeSet::from([before]))
                .unwrap_or_default(),
        }
    }

    fn add_abrupt(&mut self, completion: Completion, point: SemanticFlowPoint) {
        self.abrupt.entry(completion).or_default().insert(point);
    }

    fn merge_abrupt(&mut self, other: BTreeMap<Completion, BTreeSet<SemanticFlowPoint>>) {
        for (completion, points) in other {
            self.abrupt.entry(completion).or_default().extend(points);
        }
    }

    fn take_abrupt(&mut self, completion: &Completion) -> BTreeSet<SemanticFlowPoint> {
        self.abrupt.remove(completion).unwrap_or_default()
    }
}

enum BuildTask<'a> {
    Visit(&'a SemanticNode),
    Combine(BuildFrame<'a>),
}

enum BuildFrame<'a> {
    Sequence(usize),
    If {
        condition: &'a crate::ir::SemanticOperand<SemanticPredicate>,
        has_else: bool,
    },
    Loop {
        control: SemanticLoopControl,
        kind: SemanticLoopKind,
        condition: &'a crate::ir::SemanticOperand<SemanticPredicate>,
    },
    For {
        control: SemanticLoopControl,
        init: &'a crate::ir::SemanticStatement,
        condition: &'a crate::ir::SemanticOperand<SemanticPredicate>,
        update: &'a crate::ir::SemanticStatement,
    },
    ForEach {
        control: SemanticLoopControl,
        iterable: &'a crate::ir::SemanticOperand<SemanticExpression>,
    },
    Switch {
        region: Option<RegionId>,
        selector: &'a crate::ir::SemanticOperand<SemanticExpression>,
        cases: usize,
        has_default: bool,
    },
    Try {
        catches: usize,
        has_finally: bool,
    },
    Synchronized {
        lock: &'a crate::ir::SemanticOperand<SemanticExpression>,
    },
    Label(SemanticLabel),
}

impl BuildFrame<'_> {
    fn child_count(&self) -> usize {
        match self {
            Self::Sequence(count) => *count,
            Self::If { has_else, .. } => 1 + usize::from(*has_else),
            Self::Loop { .. } => 2,
            Self::For { .. }
            | Self::ForEach { .. }
            | Self::Synchronized { .. }
            | Self::Label(_) => 1,
            Self::Switch { cases, .. } => *cases,
            Self::Try {
                catches,
                has_finally,
            } => 1 + catches + usize::from(*has_finally),
        }
    }
}

struct SemanticFlowBuilder {
    graph: SemanticFlowGraph,
    next_synthetic: u64,
    next_continuation: u64,
}

impl SemanticFlowBuilder {
    fn new() -> Self {
        Self {
            graph: SemanticFlowGraph {
                complete: true,
                ..SemanticFlowGraph::default()
            },
            next_synthetic: 0,
            next_continuation: 0,
        }
    }

    fn mark_incomplete(&mut self, _reason: &'static str) {
        self.graph.complete = false;
    }

    fn build(mut self, root: &SemanticNode) -> SemanticFlowGraph {
        let mut pending = vec![BuildTask::Visit(root)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                BuildTask::Visit(node) => self.schedule(node, &mut pending, &mut results),
                BuildTask::Combine(frame) => {
                    let count = frame.child_count();
                    if results.len() < count {
                        self.mark_incomplete("semantic flow combine stack underflow");
                        continue;
                    }
                    let children = results.split_off(results.len() - count);
                    results.push(self.combine(frame, children));
                }
            }
        }
        if let Some(result) = results.pop() {
            self.graph.entries.extend(result.entry);
        }
        self.graph
    }

    fn schedule<'a>(
        &mut self,
        node: &'a SemanticNode,
        pending: &mut Vec<BuildTask<'a>>,
        results: &mut Vec<FlowFragment>,
    ) {
        match node {
            SemanticNode::Empty => results.push(self.empty_node()),
            SemanticNode::BasicBlock(block) => {
                let fragments = block
                    .statements
                    .iter()
                    .map(|statement| self.site(statement.site, statement.effects().may_throw()))
                    .collect();
                results.push(self.sequence(fragments));
            }
            SemanticNode::Sequence(children) => {
                pending.push(BuildTask::Combine(BuildFrame::Sequence(children.len())));
                pending.extend(children.iter().rev().map(BuildTask::Visit));
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                pending.push(BuildTask::Combine(BuildFrame::If {
                    condition,
                    has_else: else_node.is_some(),
                }));
                if let Some(else_node) = else_node {
                    pending.push(BuildTask::Visit(else_node));
                }
                pending.push(BuildTask::Visit(then_node));
            }
            SemanticNode::Loop {
                control,
                kind,
                test,
                body,
                ..
            } => {
                pending.push(BuildTask::Combine(BuildFrame::Loop {
                    control: *control,
                    kind: *kind,
                    condition: &test.condition,
                }));
                pending.push(BuildTask::Visit(body));
                pending.push(BuildTask::Visit(&test.setup));
            }
            SemanticNode::For {
                control,
                init,
                condition,
                update,
                body,
            } => {
                pending.push(BuildTask::Combine(BuildFrame::For {
                    control: *control,
                    init,
                    condition,
                    update,
                }));
                pending.push(BuildTask::Visit(body));
            }
            SemanticNode::ForEach {
                control,
                iterable,
                body,
                ..
            } => {
                pending.push(BuildTask::Combine(BuildFrame::ForEach {
                    control: *control,
                    iterable,
                }));
                pending.push(BuildTask::Visit(body));
            }
            SemanticNode::Switch {
                region,
                selector,
                cases,
            } => {
                pending.push(BuildTask::Combine(BuildFrame::Switch {
                    region: *region,
                    selector,
                    cases: cases.len(),
                    has_default: cases.iter().any(|case| case.is_default),
                }));
                pending.extend(cases.iter().rev().map(|case| BuildTask::Visit(&case.body)));
            }
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                pending.push(BuildTask::Combine(BuildFrame::Try {
                    catches: catches.len(),
                    has_finally: finally.is_some(),
                }));
                if let Some(finally) = finally {
                    pending.push(BuildTask::Visit(&finally.body));
                }
                pending.extend(
                    catches
                        .iter()
                        .rev()
                        .map(|catch| BuildTask::Visit(&catch.body)),
                );
                pending.push(BuildTask::Visit(body));
            }
            SemanticNode::Synchronized { lock, body, .. } => {
                pending.push(BuildTask::Combine(BuildFrame::Synchronized { lock }));
                pending.push(BuildTask::Visit(body));
            }
            SemanticNode::Label { label, body } => {
                pending.push(BuildTask::Combine(BuildFrame::Label(*label)));
                pending.push(BuildTask::Visit(body));
            }
            SemanticNode::Leave(leave) => results.push(self.leave(leave)),
        }
    }

    fn combine(&mut self, frame: BuildFrame<'_>, mut children: Vec<FlowFragment>) -> FlowFragment {
        match frame {
            BuildFrame::Sequence(_) => self.sequence(children),
            BuildFrame::If {
                condition,
                has_else,
            } => {
                let then_fragment = children.remove(0);
                let else_fragment = has_else.then(|| children.remove(0));
                self.branch(condition, then_fragment, else_fragment)
            }
            BuildFrame::Loop {
                control,
                kind,
                condition,
            } => {
                let setup = children.remove(0);
                let body = children.remove(0);
                self.loop_node(control, kind, condition, setup, body)
            }
            BuildFrame::For {
                control,
                init,
                condition,
                update,
            } => self.for_node(control, init, condition, update, children.remove(0)),
            BuildFrame::ForEach { control, iterable } => {
                self.for_each_node(control, iterable, children.remove(0))
            }
            BuildFrame::Switch {
                region,
                selector,
                cases,
                has_default,
            } => self.switch_node(
                region,
                selector,
                children.drain(..cases).collect(),
                has_default,
            ),
            BuildFrame::Try {
                catches,
                has_finally,
            } => self.try_node(catches, has_finally, children),
            BuildFrame::Synchronized { lock } => {
                let lock = self.site(lock.site, expression_may_throw(&lock.value));
                self.sequence(vec![lock, children.remove(0)])
            }
            BuildFrame::Label(label) => self.label(label, children.remove(0)),
        }
    }

    fn site(&mut self, site: Option<SemanticSiteId>, may_throw: bool) -> FlowFragment {
        let Some(site) = site else {
            self.mark_incomplete("semantic node has no numbered site");
            return FlowFragment::identity();
        };
        let fragment = FlowFragment::site(site, may_throw);
        self.add_edge(
            SemanticFlowPoint::before(site),
            SemanticFlowPoint::after(site),
            SemanticFlowEdgeKind::Normal,
        );
        fragment
    }

    fn leave(&mut self, leave: &SemanticLeave) -> FlowFragment {
        let mut fragment = self.site(
            leave.site,
            leave.value().is_some_and(expression_may_throw)
                || leave.condition.as_ref().is_some_and(predicate_may_throw),
        );
        let Some(point) = fragment.exits.iter().next().copied() else {
            self.mark_incomplete("semantic leave has no flow point");
            return fragment;
        };
        fragment.normal = false;
        fragment.exits.clear();
        fragment.add_abrupt(
            match &leave.kind {
                SemanticLeaveKind::Return(_) => Completion::Return,
                SemanticLeaveKind::Throw(_) => Completion::Throw,
                SemanticLeaveKind::Break => Completion::Break(leave.target),
                SemanticLeaveKind::Continue => Completion::Continue(leave.target),
                SemanticLeaveKind::BreakLabel(label) => Completion::BreakLabel(*label),
                SemanticLeaveKind::ContinueLabel(label) => Completion::ContinueLabel(*label),
                SemanticLeaveKind::FallThrough(_) | SemanticLeaveKind::Jump(_) => {
                    self.mark_incomplete("semantic tree contains an open transfer");
                    Completion::Open
                }
            },
            point,
        );
        fragment
    }

    fn sequence(&mut self, fragments: Vec<FlowFragment>) -> FlowFragment {
        let mut result = FlowFragment::identity();
        for fragment in fragments {
            if !result.normal {
                break;
            }
            if result.entry.is_none() {
                result.entry = fragment.entry;
            }
            if let Some(entry) = fragment.entry {
                self.connect(&result.exits, entry, SemanticFlowEdgeKind::Normal);
                result.exits = fragment.exits;
            }
            result.normal = fragment.normal;
            result.merge_abrupt(fragment.abrupt);
            result.throwing.extend(fragment.throwing);
        }
        result
    }

    fn branch(
        &mut self,
        condition: &crate::ir::SemanticOperand<SemanticPredicate>,
        then_fragment: FlowFragment,
        else_fragment: Option<FlowFragment>,
    ) -> FlowFragment {
        let mut condition_fragment =
            self.site(condition.site, predicate_may_throw(&condition.value));
        let sources = condition_fragment.exits.clone();
        let mut result = FlowFragment {
            entry: condition_fragment.entry,
            normal: false,
            exits: BTreeSet::new(),
            abrupt: std::mem::take(&mut condition_fragment.abrupt),
            throwing: condition_fragment.throwing,
        };
        self.add_alternative(&sources, then_fragment, &mut result);
        match else_fragment {
            Some(fragment) => self.add_alternative(&sources, fragment, &mut result),
            None => {
                result.normal = true;
                result.exits.extend(sources);
            }
        }
        result
    }

    fn loop_node(
        &mut self,
        control: SemanticLoopControl,
        kind: SemanticLoopKind,
        condition: &crate::ir::SemanticOperand<SemanticPredicate>,
        setup: FlowFragment,
        mut body: FlowFragment,
    ) -> FlowFragment {
        let condition_fragment = self.site(condition.site, predicate_may_throw(&condition.value));
        let break_points = body.take_abrupt(&break_completion(control));
        let continue_points = body.take_abrupt(&continue_completion(control));
        let condition_true = condition.value.constant_value() == Some(true);
        let condition_false = condition.value.constant_value() == Some(false);
        let mut result = FlowFragment::identity();

        match kind {
            SemanticLoopKind::PreTested => {
                let header = self.sequence(vec![setup, condition_fragment]);
                if !condition_false {
                    self.connect_to_fragment(&header.exits, &body, SemanticFlowEdgeKind::Normal);
                }
                result.entry = header.entry;
                result.throwing.extend(header.throwing);
                result.throwing.extend(body.throwing);
                result.merge_abrupt(header.abrupt);
                result.merge_abrupt(body.abrupt);
                let mut back = body.exits;
                back.extend(continue_points);
                if let Some(entry) = header.entry {
                    self.connect(&back, entry, SemanticFlowEdgeKind::LoopBack);
                }
                result.exits.extend(break_points);
                if !condition_true {
                    result.exits.extend(header.exits);
                }
            }
            SemanticLoopKind::PostTested => {
                let test = self.sequence(vec![setup, condition_fragment]);
                result.entry = body.entry.or(test.entry);
                result.throwing.extend(body.throwing);
                result.throwing.extend(test.throwing);
                result.merge_abrupt(body.abrupt);
                result.merge_abrupt(test.abrupt);
                let mut reaches_test = body.exits;
                reaches_test.extend(continue_points);
                if let Some(entry) = test.entry {
                    self.connect(&reaches_test, entry, SemanticFlowEdgeKind::Normal);
                }
                if !condition_false {
                    if let Some(entry) = result.entry {
                        self.connect(&test.exits, entry, SemanticFlowEdgeKind::LoopBack);
                    }
                }
                result.exits.extend(break_points);
                if !condition_true {
                    result.exits.extend(test.exits);
                }
            }
            SemanticLoopKind::Endless => {
                let iteration = self.sequence(vec![setup, body]);
                result.entry = iteration.entry;
                result.throwing = iteration.throwing;
                result.abrupt = iteration.abrupt;
                let mut back = iteration.exits;
                back.extend(continue_points);
                if let Some(entry) = iteration.entry {
                    self.connect(&back, entry, SemanticFlowEdgeKind::LoopBack);
                }
                result.exits = break_points;
            }
        }
        result.normal = !result.exits.is_empty();
        result
    }

    fn for_node(
        &mut self,
        control: SemanticLoopControl,
        init: &crate::ir::SemanticStatement,
        condition: &crate::ir::SemanticOperand<SemanticPredicate>,
        update: &crate::ir::SemanticStatement,
        mut body: FlowFragment,
    ) -> FlowFragment {
        let init = self.site(init.site, init.effects().may_throw());
        let condition_fragment = self.site(condition.site, predicate_may_throw(&condition.value));
        let update = self.site(update.site, update.effects().may_throw());
        let break_points = body.take_abrupt(&break_completion(control));
        let continue_points = body.take_abrupt(&continue_completion(control));
        let prefix = self.sequence(vec![init, condition_fragment]);
        self.connect_to_fragment(&prefix.exits, &body, SemanticFlowEdgeKind::Normal);
        let mut reaches_update = body.exits.clone();
        reaches_update.extend(continue_points);
        self.connect_to_fragment(&reaches_update, &update, SemanticFlowEdgeKind::Normal);
        if let Some(condition_entry) = prefix
            .entry
            .and_then(|_| condition.site.map(SemanticFlowPoint::before))
        {
            self.connect(
                &update.exits,
                condition_entry,
                SemanticFlowEdgeKind::LoopBack,
            );
        }
        let mut result = FlowFragment {
            entry: prefix.entry,
            normal: condition.value.constant_value() != Some(true) || !break_points.is_empty(),
            exits: break_points,
            abrupt: prefix.abrupt,
            throwing: prefix.throwing,
        };
        if condition.value.constant_value() != Some(true) {
            result.exits.extend(prefix.exits);
        }
        result.merge_abrupt(body.abrupt);
        result.merge_abrupt(update.abrupt);
        result.throwing.extend(body.throwing);
        result.throwing.extend(update.throwing);
        result
    }

    fn for_each_node(
        &mut self,
        control: SemanticLoopControl,
        iterable: &crate::ir::SemanticOperand<SemanticExpression>,
        mut body: FlowFragment,
    ) -> FlowFragment {
        let iterable_fragment = self.site(iterable.site, expression_may_throw(&iterable.value));
        let break_points = body.take_abrupt(&break_completion(control));
        let continue_points = body.take_abrupt(&continue_completion(control));
        self.connect_to_fragment(
            &iterable_fragment.exits,
            &body,
            SemanticFlowEdgeKind::Normal,
        );
        let mut back = body.exits.clone();
        back.extend(continue_points);
        for point in &iterable_fragment.exits {
            self.connect(&back, *point, SemanticFlowEdgeKind::LoopBack);
        }
        let mut result = FlowFragment {
            entry: iterable_fragment.entry,
            normal: true,
            exits: iterable_fragment.exits,
            abrupt: iterable_fragment.abrupt,
            throwing: iterable_fragment.throwing,
        };
        result.exits.extend(break_points);
        result.merge_abrupt(body.abrupt);
        result.throwing.extend(body.throwing);
        result
    }

    fn switch_node(
        &mut self,
        region: Option<RegionId>,
        selector: &crate::ir::SemanticOperand<SemanticExpression>,
        mut cases: Vec<FlowFragment>,
        has_default: bool,
    ) -> FlowFragment {
        let selector = self.site(selector.site, expression_may_throw(&selector.value));
        let mut result = FlowFragment {
            entry: selector.entry,
            normal: !has_default,
            exits: if has_default {
                BTreeSet::new()
            } else {
                selector.exits.clone()
            },
            abrupt: selector.abrupt,
            throwing: selector.throwing,
        };
        for mut case in cases.drain(..) {
            if let Some(region) = region {
                let breaks = case.take_abrupt(&Completion::Break(region));
                if !breaks.is_empty() {
                    case.normal = true;
                    case.exits.extend(breaks);
                }
            }
            self.add_alternative(&selector.exits, case, &mut result);
        }
        result
    }

    fn try_node(
        &mut self,
        catches: usize,
        has_finally: bool,
        mut children: Vec<FlowFragment>,
    ) -> FlowFragment {
        let body = children.remove(0);
        let mut catch_fragments = children.drain(..catches).collect::<Vec<_>>();
        for catch in &catch_fragments {
            if let Some(entry) = catch.entry {
                self.connect(&body.throwing, entry, SemanticFlowEdgeKind::Exceptional);
                if let Some(throws) = body.abrupt.get(&Completion::Throw) {
                    self.connect(throws, entry, SemanticFlowEdgeKind::Exceptional);
                }
            }
        }
        let mut result = FlowFragment {
            entry: body.entry,
            normal: body.normal,
            exits: body.exits,
            abrupt: body.abrupt,
            throwing: body.throwing,
        };
        for catch in catch_fragments.drain(..) {
            result.normal |= catch.normal;
            result.exits.extend(catch.exits);
            result.merge_abrupt(catch.abrupt);
            result.throwing.extend(catch.throwing);
        }
        if !has_finally {
            return result;
        }

        let finally = children.remove(0);
        let Some(finally_entry) = finally.entry else {
            if finally.is_identity() {
                return result;
            }
            self.mark_incomplete("finally body has no semantic entry");
            return result;
        };
        let mut output = FlowFragment {
            entry: result.entry,
            normal: false,
            exits: BTreeSet::new(),
            abrupt: BTreeMap::new(),
            throwing: BTreeSet::new(),
        };

        if result.normal {
            self.resume_after_finally(
                &result.exits,
                finally_entry,
                &finally,
                FinallyContinuation::Normal,
                &mut output,
            );
        }
        for (completion, sources) in result.abrupt {
            self.resume_after_finally(
                &sources,
                finally_entry,
                &finally,
                FinallyContinuation::Abrupt(completion),
                &mut output,
            );
        }
        if !result.throwing.is_empty() {
            self.resume_after_finally(
                &result.throwing,
                finally_entry,
                &finally,
                FinallyContinuation::Throwing,
                &mut output,
            );
        }

        for (completion, sources) in finally.abrupt {
            let point = self.synthetic_point();
            self.connect(&sources, point, SemanticFlowEdgeKind::FinallyOverride);
            output.add_abrupt(completion, point);
        }
        if !finally.throwing.is_empty() {
            let point = self.synthetic_point();
            self.connect(
                &finally.throwing,
                point,
                SemanticFlowEdgeKind::FinallyOverride,
            );
            output.throwing.insert(point);
        }
        output
    }

    fn resume_after_finally(
        &mut self,
        sources: &BTreeSet<SemanticFlowPoint>,
        finally_entry: SemanticFlowPoint,
        finally: &FlowFragment,
        continuation: FinallyContinuation,
        output: &mut FlowFragment,
    ) {
        if sources.is_empty() {
            return;
        }
        let token = self.next_continuation;
        self.next_continuation += 1;
        self.connect(
            sources,
            finally_entry,
            SemanticFlowEdgeKind::FinallyEnter(token),
        );
        if !finally.normal {
            return;
        }
        let resume = self.synthetic_point();
        self.connect(
            &finally.exits,
            resume,
            SemanticFlowEdgeKind::FinallyResume(token),
        );
        match continuation {
            FinallyContinuation::Normal => {
                output.normal = true;
                output.exits.insert(resume);
            }
            FinallyContinuation::Abrupt(completion) => {
                output.add_abrupt(completion, resume);
            }
            FinallyContinuation::Throwing => {
                output.throwing.insert(resume);
            }
        }
    }

    fn label(&mut self, label: SemanticLabel, mut body: FlowFragment) -> FlowFragment {
        let breaks = body.take_abrupt(&Completion::BreakLabel(label));
        if !breaks.is_empty() {
            body.normal = true;
            body.exits.extend(breaks);
        }
        body
    }

    fn add_alternative(
        &mut self,
        sources: &BTreeSet<SemanticFlowPoint>,
        fragment: FlowFragment,
        result: &mut FlowFragment,
    ) {
        if let Some(entry) = fragment.entry {
            self.connect(sources, entry, SemanticFlowEdgeKind::Normal);
            if fragment.normal {
                result.normal = true;
                result.exits.extend(fragment.exits);
            }
        } else if fragment.normal {
            result.normal = true;
            result.exits.extend(sources);
        }
        result.merge_abrupt(fragment.abrupt);
        result.throwing.extend(fragment.throwing);
    }

    fn empty_node(&mut self) -> FlowFragment {
        let point = self.synthetic_point();
        FlowFragment {
            entry: Some(point),
            normal: true,
            exits: BTreeSet::from([point]),
            abrupt: BTreeMap::new(),
            throwing: BTreeSet::new(),
        }
    }

    fn synthetic_point(&mut self) -> SemanticFlowPoint {
        let point = SemanticFlowPoint::Synthetic(self.next_synthetic);
        self.next_synthetic += 1;
        point
    }

    fn connect_to_fragment(
        &mut self,
        sources: &BTreeSet<SemanticFlowPoint>,
        fragment: &FlowFragment,
        kind: SemanticFlowEdgeKind,
    ) {
        if let Some(entry) = fragment.entry {
            self.connect(sources, entry, kind);
        }
    }

    fn connect(
        &mut self,
        sources: &BTreeSet<SemanticFlowPoint>,
        target: SemanticFlowPoint,
        kind: SemanticFlowEdgeKind,
    ) {
        for source in sources {
            self.add_edge(*source, target, kind);
        }
    }

    fn add_edge(
        &mut self,
        source: SemanticFlowPoint,
        target: SemanticFlowPoint,
        kind: SemanticFlowEdgeKind,
    ) {
        let predecessors = self.graph.predecessors.entry(target).or_default();
        if !predecessors.contains(&(source, kind)) {
            predecessors.push((source, kind));
            predecessors.sort();
            let successors = self.graph.successors.entry(source).or_default();
            if !successors.contains(&target) {
                successors.push(target);
                successors.sort();
            }
        }
    }
}

fn break_completion(control: SemanticLoopControl) -> Completion {
    match control {
        SemanticLoopControl::Region(region) => Completion::Break(region),
        SemanticLoopControl::Label(label) => Completion::BreakLabel(label),
    }
}

fn continue_completion(control: SemanticLoopControl) -> Completion {
    match control {
        SemanticLoopControl::Region(region) => Completion::Continue(region),
        SemanticLoopControl::Label(label) => Completion::ContinueLabel(label),
    }
}

fn expression_may_throw(expression: &SemanticExpression) -> bool {
    expression.effects().may_throw()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point(id: u64) -> SemanticFlowPoint {
        SemanticFlowPoint::before(SemanticSiteId(id))
    }

    #[test]
    fn must_reach_accepts_linear_flow() {
        let source = point(0);
        let middle = point(1);
        let target = point(2);
        let graph = SemanticFlowGraph {
            successors: BTreeMap::from([(source, vec![middle]), (middle, vec![target])]),
            complete: true,
            ..SemanticFlowGraph::default()
        };

        assert!(graph.must_reach(source, target));
    }

    #[test]
    fn must_reach_rejects_terminal_bypass() {
        let source = point(0);
        let target = point(1);
        let terminal = point(2);
        let graph = SemanticFlowGraph {
            successors: BTreeMap::from([(source, vec![target, terminal])]),
            complete: true,
            ..SemanticFlowGraph::default()
        };

        assert!(!graph.must_reach(source, target));
    }

    #[test]
    fn must_reach_rejects_target_avoiding_cycle() {
        let source = point(0);
        let cycle = point(1);
        let target = point(2);
        let graph = SemanticFlowGraph {
            successors: BTreeMap::from([(source, vec![cycle]), (cycle, vec![target, cycle])]),
            complete: true,
            ..SemanticFlowGraph::default()
        };

        assert!(!graph.must_reach(source, target));
    }
}

fn predicate_may_throw(predicate: &SemanticPredicate) -> bool {
    let mut pending = vec![predicate];
    while let Some(predicate) = pending.pop() {
        match predicate {
            SemanticPredicate::Test(instruction) if instruction.effects().may_throw() => {
                return true;
            }
            SemanticPredicate::Test(_) | SemanticPredicate::True | SemanticPredicate::False => {}
            SemanticPredicate::Not(inner) => pending.push(inner),
            SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                pending.extend(terms);
            }
        }
    }
    false
}
