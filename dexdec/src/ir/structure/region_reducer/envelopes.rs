use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    RegionGraph, RegionId, SemanticCatch, SemanticFinally, SemanticFoldControl, SemanticFoldError,
    SemanticFolder, SemanticLabel, SemanticLeaveKind, SemanticLoopControl, SemanticNode,
    SemanticVisitor, CFG,
};

use super::{super::StructureError, labels::LexicalLabels};

/// Places one lexical exception envelope for every structured exception
/// region. A region can expose several reduction ports, but those ports are
/// alternate views of one source try statement and must not each retain a
/// cloned catch/finally envelope.
pub(super) struct ExceptionEnvelopeCanonicalizer<'a> {
    cfg: &'a CFG,
    regions: &'a RegionGraph,
}

impl<'a> ExceptionEnvelopeCanonicalizer<'a> {
    pub(super) fn new(cfg: &'a CFG, regions: &'a RegionGraph) -> Self {
        Self { cfg, regions }
    }

    pub(super) fn apply(&self, mut root: SemanticNode) -> Result<SemanticNode, StructureError> {
        loop {
            let duplicates = TryMultiplicity::collect(&root)
                .into_iter()
                .filter_map(|(region, count)| (count > 1).then_some(region))
                .collect::<Vec<_>>();
            if duplicates.is_empty() {
                return self.merge_families(root);
            }

            let mut changed = false;
            for region in duplicates {
                let original = root.clone();
                let mut canonicalizer = CanonicalizeTarget {
                    envelopes: self,
                    target: region,
                    changed: false,
                };
                let candidate = canonicalizer.fold_node(root)?;
                let region_changed = canonicalizer.changed;
                if region_changed && LexicalLabels::escaped_loop(&candidate).is_some() {
                    root = original;
                } else {
                    root = candidate;
                    changed |= region_changed;
                }
            }
            if !changed {
                return self.merge_families(root);
            }
        }
    }

    fn merge_families(&self, mut root: SemanticNode) -> Result<SemanticNode, StructureError> {
        loop {
            let families = EnvelopeFamilies::collect(&root)
                .into_values()
                .filter(|family| family.count > 1 && family.envelope.is_some())
                .collect::<Vec<_>>();
            if families.is_empty() {
                return Ok(root);
            }
            let mut changed = false;
            for family in &families {
                let original = root.clone();
                let mut family_changed = false;
                let candidate = self.merge_family(root, family, &mut family_changed)?;
                if family_changed && LexicalLabels::escaped_loop(&candidate).is_some() {
                    root = original;
                } else {
                    root = candidate;
                    changed |= family_changed;
                }
            }
            if !changed {
                return Ok(root);
            }
        }
    }

    fn merge_family(
        &self,
        node: SemanticNode,
        family: &EnvelopeFamily,
        changed: &mut bool,
    ) -> Result<SemanticNode, StructureError> {
        MergeEnvelopeFamily {
            canonicalizer: self,
            family,
            changed,
        }
        .fold_node(node)
    }

    fn family_count(&self, root: &SemanticNode, key: &EnvelopeKey) -> usize {
        let mut count = 0;
        self.family_body(root, key, &mut |node| {
            if EnvelopeKey::of(node).as_ref() == Some(key) {
                count += 1;
            }
        });
        count
    }

    fn family_domain_contains(
        &self,
        node: &SemanticNode,
        family: &EnvelopeFamily,
    ) -> Result<bool, StructureError> {
        let mut allowed = BTreeSet::new();
        let mut coverage = BTreeSet::new();
        for owner in &family.regions {
            let owner = self
                .regions
                .tree()
                .region(*owner)
                .ok_or(StructureError::UnknownRegion(*owner))?;
            allowed.extend(owner.blocks.iter().copied());
            coverage.extend(
                owner
                    .blocks
                    .iter()
                    .flat_map(|block| self.cfg.exception_coverage(*block).iter().copied()),
            );
        }
        if !coverage.is_empty() {
            allowed.extend(
                self.cfg
                    .blocks
                    .keys()
                    .copied()
                    .filter(|block| !self.cfg.exception_coverage(*block).is_disjoint(&coverage)),
            );
        }
        let mut blocks = BTreeSet::new();
        self.family_body(node, &family.key, &mut |node| {
            if let SemanticNode::BasicBlock(block) = node {
                if !block.statements.is_empty() {
                    blocks.insert(block.id);
                }
            }
        });
        Ok(!blocks.is_empty() && blocks.is_subset(&allowed))
    }

    fn family_region(&self, family: &EnvelopeFamily) -> Result<RegionId, StructureError> {
        if let Some(owner) = self.family_handler_owner(family)? {
            return Ok(owner);
        }
        let region = family
            .regions
            .iter()
            .map(|region| {
                let entry = self
                    .regions
                    .tree()
                    .region(*region)
                    .ok_or(StructureError::UnknownRegion(*region))?
                    .entry;
                let offset = entry
                    .and_then(|entry| self.cfg.block(entry))
                    .map(|block| block.offset)
                    .unwrap_or(u32::MAX);
                Ok((offset, entry, *region))
            })
            .collect::<Result<Vec<_>, StructureError>>()?
            .into_iter()
            .min()
            .map(|(_, _, region)| region)
            .expect("an exception envelope family contains at least one region");
        Ok(region)
    }

    fn family_handler_owner(
        &self,
        family: &EnvelopeFamily,
    ) -> Result<Option<RegionId>, StructureError> {
        let handlers = family
            .key
            .catches
            .iter()
            .copied()
            .chain(family.key.finally)
            .collect::<Vec<_>>();
        self.handler_owner(&handlers, &family.regions)
    }

    fn handler_owner(
        &self,
        handlers: &[RegionId],
        protected: &BTreeSet<RegionId>,
    ) -> Result<Option<RegionId>, StructureError> {
        if handlers.is_empty() {
            return Ok(None);
        }
        let mut regions = handlers
            .iter()
            .flat_map(|handler| self.regions.handler_owners(*handler))
            .chain(protected.iter().copied());
        let Some(mut owner) = regions.next() else {
            return Ok(None);
        };
        for region in regions {
            owner = self
                .regions
                .tree()
                .common_ancestor(owner, region)
                .map_err(StructureError::from)?;
        }
        let descriptor = self
            .regions
            .tree()
            .region(owner)
            .ok_or(StructureError::UnknownRegion(owner))?;
        let lexical_owner = matches!(
            &descriptor.kind,
            crate::ir::RegionKind::Try | crate::ir::RegionKind::Synchronized(_)
        ) && handlers.iter().all(|handler| {
            self.regions
                .tree()
                .region(*handler)
                .is_some_and(|region| region.parent == Some(owner))
                || self.regions.handlers_of(owner).contains(handler)
        });
        Ok(lexical_owner.then_some(owner))
    }

    fn envelope_owner(
        &self,
        fallback: RegionId,
        envelope: &ExceptionEnvelope,
    ) -> Result<RegionId, StructureError> {
        let handlers = envelope
            .catches
            .iter()
            .map(|catch| catch.region)
            .chain(envelope.finally.as_ref().map(|finally| finally.region))
            .collect::<Vec<_>>();
        self.handler_owner(&handlers, &BTreeSet::from([fallback]))
            .map(|owner| owner.unwrap_or(fallback))
    }

    fn place_envelope(
        &self,
        body: SemanticNode,
        region: RegionId,
        envelope: ExceptionEnvelope,
    ) -> Result<SemanticNode, StructureError> {
        let mut placement = SynchronizedEnvelopePlacement {
            region,
            envelope: Some(envelope),
        };
        let body = placement.fold_node(body).map_err(StructureError::from)?;
        Ok(match placement.envelope {
            Some(envelope) => envelope.attach(region, body),
            None => body,
        })
    }

    fn family_body(
        &self,
        root: &SemanticNode,
        key: &EnvelopeKey,
        visitor: &mut impl FnMut(&SemanticNode),
    ) {
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            visitor(node);
            match node {
                SemanticNode::Sequence(children) => pending.extend(children),
                SemanticNode::If {
                    then_node,
                    else_node,
                    ..
                } => {
                    pending.push(then_node);
                    if let Some(else_node) = else_node {
                        pending.push(else_node);
                    }
                }
                SemanticNode::Loop { body, .. }
                | SemanticNode::For { body, .. }
                | SemanticNode::ForEach { body, .. }
                | SemanticNode::Synchronized { body, .. }
                | SemanticNode::Label { body, .. } => pending.push(body),
                SemanticNode::Switch { cases, .. } => {
                    pending.extend(cases.iter().map(|case| &case.body));
                }
                SemanticNode::Try {
                    body,
                    catches,
                    finally,
                    ..
                } => {
                    pending.push(body);
                    if EnvelopeKey::of(node).as_ref() == Some(key) {
                        continue;
                    }
                    pending.extend(catches.iter().map(|catch| &catch.body));
                    if let Some(finally) = finally {
                        pending.push(&finally.body);
                    }
                }
                SemanticNode::Empty | SemanticNode::BasicBlock(_) | SemanticNode::Leave(_) => {}
            }
        }
    }

    fn strip_family(
        &self,
        node: SemanticNode,
        key: &EnvelopeKey,
    ) -> Result<SemanticNode, StructureError> {
        StripEnvelopeFamily { key }.fold_node(node)
    }

    fn canonicalize_node(
        &self,
        node: SemanticNode,
        target: RegionId,
        changed: &mut bool,
    ) -> Result<SemanticNode, StructureError> {
        if self.count(&node, target)? < 2 || !self.domain_contains(&node, target)? {
            return Ok(node);
        }
        let EnvelopeSet::One(envelope) = self.envelopes(&node, target)? else {
            return Ok(node);
        };
        if !envelope.can_wrap(&node) {
            return Ok(node);
        }
        let original = node.clone();
        let body = self.strip(node, target)?;
        let region = self.envelope_owner(target, &envelope)?;
        let candidate = self.place_envelope(body, region, envelope)?;
        if LexicalLabels::escaped_loop(&candidate).is_some() {
            return Ok(original);
        }
        *changed = true;
        Ok(candidate)
    }

    fn count(&self, node: &SemanticNode, target: RegionId) -> Result<usize, StructureError> {
        let mut count = 0;
        self.visit(node, target, &mut |node| {
            if matches!(node, SemanticNode::Try { region, .. } if *region == target) {
                count += 1;
            }
        })?;
        Ok(count)
    }

    fn envelopes(
        &self,
        node: &SemanticNode,
        target: RegionId,
    ) -> Result<EnvelopeSet, StructureError> {
        let mut set = EnvelopeSet::None;
        self.visit(node, target, &mut |node| {
            let SemanticNode::Try {
                region,
                catches,
                finally,
                ..
            } = node
            else {
                return;
            };
            if *region == target {
                set.merge(ExceptionEnvelope {
                    catches: catches.clone(),
                    finally: finally.clone(),
                });
            }
        })?;
        Ok(set)
    }

    fn strip(&self, node: SemanticNode, target: RegionId) -> Result<SemanticNode, StructureError> {
        Ok(match node {
            SemanticNode::Try {
                region,
                body,
                catches,
                finally,
            } if region == target => self.strip(*body, target)?,
            SemanticNode::Sequence(children) => SemanticNode::sequence(
                children
                    .into_iter()
                    .map(|child| self.strip(child, target))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::If {
                condition,
                then_node: Box::new(self.strip(*then_node, target)?),
                else_node: else_node
                    .map(|node| self.strip(*node, target).map(Box::new))
                    .transpose()?,
            },
            SemanticNode::Loop {
                control,
                header,
                kind,
                test,
                body,
            } => SemanticNode::Loop {
                control,
                header,
                kind,
                test,
                body: Box::new(self.strip(*body, target)?),
            },
            SemanticNode::For {
                control,
                init,
                condition,
                update,
                body,
            } => SemanticNode::For {
                control,
                init,
                condition,
                update,
                body: Box::new(self.strip(*body, target)?),
            },
            SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body,
            } => SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body: Box::new(self.strip(*body, target)?),
            },
            SemanticNode::Switch {
                region,
                selector,
                cases,
            } => SemanticNode::Switch {
                region,
                selector,
                cases: cases
                    .into_iter()
                    .map(|mut case| {
                        case.body = self.strip(case.body, target)?;
                        Ok(case)
                    })
                    .collect::<Result<Vec<_>, StructureError>>()?,
            },
            SemanticNode::Try {
                region,
                body,
                catches,
                finally,
            } => {
                let cross = self.crosses(target, region)?;
                SemanticNode::Try {
                    region,
                    body: Box::new(self.strip(*body, target)?),
                    catches: if cross {
                        catches
                            .into_iter()
                            .map(|mut catch| {
                                catch.body = self.strip(catch.body, target)?;
                                Ok(catch)
                            })
                            .collect::<Result<Vec<_>, StructureError>>()?
                    } else {
                        catches
                    },
                    finally: if cross {
                        finally
                            .map(|mut finally| {
                                finally.body = Box::new(self.strip(*finally.body, target)?);
                                Ok::<_, StructureError>(finally)
                            })
                            .transpose()?
                    } else {
                        finally
                    },
                }
            }
            SemanticNode::Synchronized {
                region,
                lock,
                method,
                body,
            } => SemanticNode::Synchronized {
                region,
                lock,
                method,
                body: Box::new(self.strip(*body, target)?),
            },
            SemanticNode::Label { label, body } => SemanticNode::Label {
                label,
                body: Box::new(self.strip(*body, target)?),
            },
            leaf => leaf,
        })
    }

    fn domain_contains(
        &self,
        node: &SemanticNode,
        target: RegionId,
    ) -> Result<bool, StructureError> {
        let allowed = &self
            .regions
            .tree()
            .region(target)
            .ok_or(StructureError::UnknownRegion(target))?
            .blocks;
        let mut blocks = BTreeSet::new();
        self.visit(node, target, &mut |node| {
            if let SemanticNode::BasicBlock(block) = node {
                blocks.insert(block.id);
            }
        })?;
        Ok(!blocks.is_empty() && blocks.is_subset(allowed))
    }

    fn visit(
        &self,
        node: &SemanticNode,
        target: RegionId,
        visitor: &mut impl FnMut(&SemanticNode),
    ) -> Result<(), StructureError> {
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            visitor(node);
            match node {
                SemanticNode::Empty | SemanticNode::BasicBlock(_) | SemanticNode::Leave(_) => {}
                SemanticNode::Sequence(children) => pending.extend(children.iter().rev()),
                SemanticNode::If {
                    then_node,
                    else_node,
                    ..
                } => {
                    if let Some(else_node) = else_node {
                        pending.push(else_node);
                    }
                    pending.push(then_node);
                }
                SemanticNode::Loop { body, .. }
                | SemanticNode::For { body, .. }
                | SemanticNode::ForEach { body, .. }
                | SemanticNode::Synchronized { body, .. }
                | SemanticNode::Label { body, .. } => pending.push(body),
                SemanticNode::Switch { cases, .. } => {
                    pending.extend(cases.iter().rev().map(|case| &case.body));
                }
                SemanticNode::Try {
                    region,
                    body,
                    catches,
                    finally,
                } => {
                    if *region != target && self.crosses(target, *region)? {
                        if let Some(finally) = finally {
                            pending.push(&finally.body);
                        }
                        pending.extend(catches.iter().rev().map(|catch| &catch.body));
                    }
                    pending.push(body);
                }
            }
        }
        Ok(())
    }

    fn crosses(&self, target: RegionId, nested: RegionId) -> Result<bool, StructureError> {
        self.regions
            .tree()
            .is_ancestor(target, nested)
            .map_err(StructureError::from)
    }
}

struct CanonicalizeTarget<'canonicalizer, 'graph> {
    envelopes: &'canonicalizer ExceptionEnvelopeCanonicalizer<'graph>,
    target: RegionId,
    changed: bool,
}

impl SemanticFolder for CanonicalizeTarget<'_, '_> {
    type Error = StructureError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        self.envelopes
            .canonicalize_node(node, self.target, &mut self.changed)
    }
}

struct MergeEnvelopeFamily<'canonicalizer, 'graph, 'family, 'changed> {
    canonicalizer: &'canonicalizer ExceptionEnvelopeCanonicalizer<'graph>,
    family: &'family EnvelopeFamily,
    changed: &'changed mut bool,
}

impl SemanticFolder for MergeEnvelopeFamily<'_, '_, '_, '_> {
    type Error = StructureError;

    fn begin_node(&mut self, node: SemanticNode) -> Result<SemanticFoldControl, Self::Error> {
        if self.canonicalizer.family_count(&node, &self.family.key) < 2
            || !self
                .canonicalizer
                .family_domain_contains(&node, self.family)?
        {
            return Ok(SemanticFoldControl::Descend(node));
        }

        let region = self.canonicalizer.family_region(self.family)?;
        let envelope = self
            .family
            .envelope
            .clone()
            .ok_or(StructureError::UnknownRegion(region))?;
        if !envelope.can_wrap(&node) {
            return Ok(SemanticFoldControl::Descend(node));
        }

        let original = node.clone();
        let body = self.canonicalizer.strip_family(node, &self.family.key)?;
        let candidate = self.canonicalizer.place_envelope(body, region, envelope)?;
        if LexicalLabels::escaped_loop(&candidate).is_some() {
            return Ok(SemanticFoldControl::Descend(original));
        }

        *self.changed = true;
        Ok(SemanticFoldControl::Emit(candidate))
    }
}

struct StripEnvelopeFamily<'key> {
    key: &'key EnvelopeKey,
}

impl SemanticFolder for StripEnvelopeFamily<'_> {
    type Error = StructureError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        if EnvelopeKey::of(&node).as_ref() != Some(self.key) {
            return Ok(node);
        }
        let SemanticNode::Try { body, .. } = node else {
            unreachable!("exception envelope key matched a non-try node");
        };
        Ok(*body)
    }
}

struct TryMultiplicity;

impl TryMultiplicity {
    fn collect(root: &SemanticNode) -> BTreeMap<RegionId, usize> {
        let mut counts = BTreeMap::new();
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Try {
                    region,
                    body,
                    catches,
                    finally,
                } => {
                    *counts.entry(*region).or_default() += 1;
                    pending.push(body);
                    pending.extend(catches.iter().map(|catch| &catch.body));
                    if let Some(finally) = finally {
                        pending.push(&finally.body);
                    }
                }
                SemanticNode::Sequence(children) => pending.extend(children),
                SemanticNode::If {
                    then_node,
                    else_node,
                    ..
                } => {
                    pending.push(then_node);
                    if let Some(else_node) = else_node {
                        pending.push(else_node);
                    }
                }
                SemanticNode::Loop { body, .. }
                | SemanticNode::For { body, .. }
                | SemanticNode::ForEach { body, .. }
                | SemanticNode::Synchronized { body, .. }
                | SemanticNode::Label { body, .. } => pending.push(body),
                SemanticNode::Switch { cases, .. } => {
                    pending.extend(cases.iter().map(|case| &case.body));
                }
                SemanticNode::Empty | SemanticNode::BasicBlock(_) | SemanticNode::Leave(_) => {}
            }
        }
        counts
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct EnvelopeKey {
    catches: Vec<RegionId>,
    finally: Option<RegionId>,
}

impl EnvelopeKey {
    fn of(node: &SemanticNode) -> Option<Self> {
        let SemanticNode::Try {
            catches, finally, ..
        } = node
        else {
            return None;
        };
        Some(Self {
            catches: catches.iter().map(|catch| catch.region).collect(),
            finally: finally.as_ref().map(|finally| finally.region),
        })
    }
}

struct EnvelopeFamily {
    key: EnvelopeKey,
    regions: BTreeSet<RegionId>,
    count: usize,
    envelope: Option<ExceptionEnvelope>,
}

struct EnvelopeFamilies;

impl EnvelopeFamilies {
    fn collect(root: &SemanticNode) -> BTreeMap<EnvelopeKey, EnvelopeFamily> {
        let mut families = BTreeMap::new();
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Try {
                    region,
                    body,
                    catches,
                    finally,
                } => {
                    let key = EnvelopeKey {
                        catches: catches.iter().map(|catch| catch.region).collect(),
                        finally: finally.as_ref().map(|finally| finally.region),
                    };
                    let envelope = ExceptionEnvelope {
                        catches: catches.clone(),
                        finally: finally.clone(),
                    };
                    let family = families
                        .entry(key.clone())
                        .or_insert_with(|| EnvelopeFamily {
                            key,
                            regions: BTreeSet::new(),
                            count: 0,
                            envelope: Some(envelope.clone()),
                        });
                    family.count += 1;
                    family.regions.insert(*region);
                    if family
                        .envelope
                        .as_ref()
                        .is_some_and(|current| !current.same_shape(&envelope))
                    {
                        family.envelope = None;
                    }
                    pending.push(body);
                    pending.extend(catches.iter().map(|catch| &catch.body));
                    if let Some(finally) = finally {
                        pending.push(&finally.body);
                    }
                }
                SemanticNode::Sequence(children) => pending.extend(children),
                SemanticNode::If {
                    then_node,
                    else_node,
                    ..
                } => {
                    pending.push(then_node);
                    if let Some(else_node) = else_node {
                        pending.push(else_node);
                    }
                }
                SemanticNode::Loop { body, .. }
                | SemanticNode::For { body, .. }
                | SemanticNode::ForEach { body, .. }
                | SemanticNode::Synchronized { body, .. }
                | SemanticNode::Label { body, .. } => pending.push(body),
                SemanticNode::Switch { cases, .. } => {
                    pending.extend(cases.iter().map(|case| &case.body));
                }
                SemanticNode::Empty | SemanticNode::BasicBlock(_) | SemanticNode::Leave(_) => {}
            }
        }
        families
    }
}

#[derive(Clone)]
struct ExceptionEnvelope {
    catches: Vec<SemanticCatch>,
    finally: Option<SemanticFinally>,
}

impl ExceptionEnvelope {
    fn attach(self, region: RegionId, body: SemanticNode) -> SemanticNode {
        SemanticNode::Try {
            region,
            body: Box::new(body),
            catches: self.catches,
            finally: self.finally,
        }
    }

    fn same_shape(&self, other: &Self) -> bool {
        self.catches.len() == other.catches.len()
            && self
                .catches
                .iter()
                .zip(&other.catches)
                .all(|(left, right)| {
                    left.region == right.region
                        && left.exception_types == right.exception_types
                        && left.exception_value == right.exception_value
                })
            && self.finally.as_ref().map(|finally| finally.region)
                == other.finally.as_ref().map(|finally| finally.region)
    }

    fn can_wrap(&self, node: &SemanticNode) -> bool {
        let bindings = LabelBindings::collect(node);
        if bindings.is_empty() {
            return true;
        }
        self.label_dependencies().is_disjoint(&bindings)
    }

    fn label_dependencies(&self) -> BTreeSet<SemanticLabel> {
        let mut dependencies = FreeLabelDependencies::default();
        for catch in &self.catches {
            dependencies.visit_node(&catch.body);
        }
        if let Some(finally) = &self.finally {
            dependencies.visit_node(&finally.body);
        }
        dependencies.free
    }
}

#[derive(Default)]
struct LabelBindings {
    labels: BTreeSet<SemanticLabel>,
}

impl LabelBindings {
    fn collect(node: &SemanticNode) -> BTreeSet<SemanticLabel> {
        let mut bindings = Self::default();
        bindings.visit_node(node);
        bindings.labels
    }
}

impl SemanticVisitor for LabelBindings {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::Label { label, .. } => {
                self.labels.insert(*label);
            }
            SemanticNode::Loop {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: SemanticLoopControl::Label(label),
                ..
            } => {
                self.labels.insert(*label);
            }
            _ => {}
        }
    }
}

#[derive(Default)]
struct FreeLabelDependencies {
    active: BTreeMap<SemanticLabel, usize>,
    free: BTreeSet<SemanticLabel>,
}

impl FreeLabelDependencies {
    fn binding(node: &SemanticNode) -> Option<SemanticLabel> {
        match node {
            SemanticNode::Label { label, .. } => Some(*label),
            SemanticNode::Loop {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: SemanticLoopControl::Label(label),
                ..
            } => Some(*label),
            _ => None,
        }
    }
}

impl SemanticVisitor for FreeLabelDependencies {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let Some(label) = Self::binding(node) {
            *self.active.entry(label).or_default() += 1;
        }
        if let SemanticNode::Leave(leave) = node {
            let label = match leave.kind {
                SemanticLeaveKind::BreakLabel(label) | SemanticLeaveKind::ContinueLabel(label) => {
                    label
                }
                _ => return,
            };
            if !self.active.contains_key(&label) {
                self.free.insert(label);
            }
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let Some(label) = Self::binding(node) else {
            return;
        };
        let Some(depth) = self.active.get_mut(&label) else {
            return;
        };
        *depth -= 1;
        if *depth == 0 {
            self.active.remove(&label);
        }
    }
}

struct SynchronizedEnvelopePlacement {
    region: RegionId,
    envelope: Option<ExceptionEnvelope>,
}

impl SemanticFolder for SynchronizedEnvelopePlacement {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::Synchronized {
            region,
            lock,
            method,
            body,
        } = node
        else {
            return Ok(node);
        };
        if region != self.region {
            return Ok(SemanticNode::Synchronized {
                region,
                lock,
                method,
                body,
            });
        }
        let Some(envelope) = self.envelope.take() else {
            return Ok(SemanticNode::Synchronized {
                region,
                lock,
                method,
                body,
            });
        };
        Ok(SemanticNode::Synchronized {
            region,
            lock,
            method,
            body: Box::new(envelope.attach(region, *body)),
        })
    }
}

enum EnvelopeSet {
    None,
    One(ExceptionEnvelope),
    Conflict,
}

impl EnvelopeSet {
    fn merge(&mut self, incoming: ExceptionEnvelope) {
        match self {
            Self::None => *self = Self::One(incoming),
            Self::One(current) if current.same_shape(&incoming) => {}
            Self::One(_) | Self::Conflict => *self = Self::Conflict,
        }
    }
}
