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
                let root = self.merge_families(root)?;
                return self.finalize(root);
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
                if region_changed && escapes_structured_control(&candidate) {
                    root = original;
                } else {
                    root = candidate;
                    changed |= region_changed;
                }
            }
            if !changed {
                let root = self.merge_families(root)?;
                return self.finalize(root);
            }
        }
    }

    fn finalize(&self, root: SemanticNode) -> Result<SemanticNode, StructureError> {
        let root = ExternalMonitorHandlerPlacement::apply(self.cfg, self.regions.tree(), root)?;
        HandlerCleanupEnvelopePlacement::apply(self.regions, root)
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
                if family_changed && escapes_structured_control(&candidate) {
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
        if escapes_structured_control(&candidate) {
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
        if escapes_structured_control(&candidate) {
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
            // Catch/finally continuations are part of envelope identity. A loop
            // may rewrite BreakLabel into Break(region) inside its body; merging
            // that rewritten catch onto a try outside the loop leaves the break
            // targeting inactive control.
            && self.label_dependencies() == other.label_dependencies()
            && self.control_dependencies() == other.control_dependencies()
    }

    fn can_wrap(&self, node: &SemanticNode) -> bool {
        self.label_dependencies()
            .is_disjoint(&LabelBindings::collect(node))
            && self
                .control_dependencies()
                .is_disjoint(&ControlBindings::collect(node))
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

    fn control_dependencies(&self) -> BTreeSet<RegionId> {
        let mut dependencies = FreeControlDependencies::default();
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

#[derive(Default)]
struct ControlBindings {
    regions: BTreeSet<RegionId>,
}

impl ControlBindings {
    fn collect(node: &SemanticNode) -> BTreeSet<RegionId> {
        let mut bindings = Self::default();
        bindings.visit_node(node);
        bindings.regions
    }

    fn binding(node: &SemanticNode) -> Option<RegionId> {
        match node {
            SemanticNode::Loop {
                control: SemanticLoopControl::Region(region),
                ..
            }
            | SemanticNode::For {
                control: SemanticLoopControl::Region(region),
                ..
            }
            | SemanticNode::ForEach {
                control: SemanticLoopControl::Region(region),
                ..
            } => Some(*region),
            SemanticNode::Switch { region, .. } => *region,
            _ => None,
        }
    }
}

impl SemanticVisitor for ControlBindings {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let Some(region) = Self::binding(node) {
            self.regions.insert(region);
        }
    }
}

#[derive(Default)]
struct FreeControlDependencies {
    active: BTreeMap<RegionId, usize>,
    free: BTreeSet<RegionId>,
}

impl FreeControlDependencies {
    fn collect(node: &SemanticNode) -> BTreeSet<RegionId> {
        let mut dependencies = Self::default();
        dependencies.visit_node(node);
        dependencies.free
    }
}

impl SemanticVisitor for FreeControlDependencies {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let Some(region) = ControlBindings::binding(node) {
            *self.active.entry(region).or_default() += 1;
        }
        if let SemanticNode::Leave(leave) = node {
            if matches!(
                leave.kind,
                SemanticLeaveKind::Break | SemanticLeaveKind::Continue
            ) && !self.active.contains_key(&leave.target)
            {
                self.free.insert(leave.target);
            }
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let Some(region) = ControlBindings::binding(node) else {
            return;
        };
        let Some(depth) = self.active.get_mut(&region) else {
            return;
        };
        *depth -= 1;
        if *depth == 0 {
            self.active.remove(&region);
        }
    }
}

/// True when a candidate envelope placement leaves a loop label or region
/// break/continue without an active binder — the same class of defect as
/// `LexicalLabels::escaped_loop`, for region-controlled loops.
fn escapes_structured_control(root: &SemanticNode) -> bool {
    LexicalLabels::escaped_loop(root).is_some()
        || !FreeControlDependencies::collect(root).is_empty()
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

/// A source-level handler outside an explicit synchronized statement runs only
/// after the synthetic monitor-release handler has completed. Exception-region
/// partitioning can leave such a handler attached to a try fragment nested in
/// the recovered synchronized region. Keep the protected fragment, but move
/// its source handler envelope outside the monitor scope.
struct ExternalMonitorHandlerPlacement<'cfg, 'tree> {
    cfg: &'cfg CFG,
    tree: &'tree crate::ir::RegionTree,
    changed: bool,
}

enum ExternalEnvelopePlan {
    Direct,
    Sequence(usize),
}

impl<'cfg, 'tree> ExternalMonitorHandlerPlacement<'cfg, 'tree> {
    fn apply(
        cfg: &'cfg CFG,
        tree: &'tree crate::ir::RegionTree,
        mut root: SemanticNode,
    ) -> Result<SemanticNode, StructureError> {
        loop {
            let mut placement = Self {
                cfg,
                tree,
                changed: false,
            };
            root = placement.fold_node(root)?;
            if !placement.changed {
                return Ok(root);
            }
        }
    }

    fn plan(
        &self,
        synchronized: RegionId,
        body: &SemanticNode,
    ) -> Result<Option<ExternalEnvelopePlan>, StructureError> {
        if self.external_envelope(synchronized, body)? {
            return Ok(Some(ExternalEnvelopePlan::Direct));
        }
        let SemanticNode::Sequence(nodes) = body else {
            return Ok(None);
        };
        let mut candidate = None;
        for (index, node) in nodes.iter().enumerate() {
            if self.external_envelope(synchronized, node)? {
                let SemanticNode::Try { finally: None, .. } = node else {
                    return Ok(None);
                };
                if candidate.replace(index).is_some() {
                    return Ok(None);
                }
            } else if !self.non_throwing(node) {
                return Ok(None);
            }
        }
        Ok(candidate.map(ExternalEnvelopePlan::Sequence))
    }

    fn external_envelope(
        &self,
        synchronized: RegionId,
        node: &SemanticNode,
    ) -> Result<bool, StructureError> {
        let SemanticNode::Try {
            region,
            catches,
            finally,
            ..
        } = node
        else {
            return Ok(false);
        };
        if !self
            .tree
            .is_ancestor(synchronized, *region)
            .map_err(StructureError::from)?
        {
            return Ok(false);
        }
        let handlers = catches
            .iter()
            .map(|catch| catch.region)
            .chain(finally.as_ref().map(|finally| finally.region))
            .collect::<Vec<_>>();
        if handlers.is_empty() {
            return Ok(false);
        }
        for handler in handlers {
            if self
                .tree
                .is_ancestor(synchronized, handler)
                .map_err(StructureError::from)?
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn non_throwing(&self, node: &SemanticNode) -> bool {
        match node {
            SemanticNode::Empty => true,
            SemanticNode::BasicBlock(block) => self.cfg.block(block.id).is_some_and(|source| {
                source
                    .insns
                    .iter()
                    .all(|instruction| !instruction.can_throw())
                    && self
                        .cfg
                        .successors_with_kind(block.id)
                        .iter()
                        .all(|(_, kind)| !kind.is_exception())
            }),
            SemanticNode::Sequence(nodes) => nodes.iter().all(|node| self.non_throwing(node)),
            _ => false,
        }
    }
}

impl SemanticFolder for ExternalMonitorHandlerPlacement<'_, '_> {
    type Error = StructureError;

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
        if method {
            return Ok(SemanticNode::Synchronized {
                region,
                lock,
                method,
                body,
            });
        }
        let Some(plan) = self.plan(region, &body)? else {
            return Ok(SemanticNode::Synchronized {
                region,
                lock,
                method,
                body,
            });
        };

        let (try_region, synchronized_body, catches, finally) = match (plan, *body) {
            (
                ExternalEnvelopePlan::Direct,
                SemanticNode::Try {
                    region: try_region,
                    body: try_body,
                    catches,
                    finally,
                },
            ) => (try_region, *try_body, catches, finally),
            (ExternalEnvelopePlan::Sequence(index), SemanticNode::Sequence(mut nodes)) => {
                let SemanticNode::Try {
                    region: try_region,
                    body: try_body,
                    catches,
                    finally,
                } = nodes.remove(index)
                else {
                    unreachable!("external envelope plan must select a try node");
                };
                nodes.insert(index, *try_body);
                (try_region, SemanticNode::sequence(nodes), catches, finally)
            }
            _ => unreachable!("external envelope plan must match synchronized body"),
        };

        self.changed = true;
        Ok(SemanticNode::Try {
            region: try_region,
            body: Box::new(SemanticNode::Synchronized {
                region,
                lock,
                method,
                body: Box::new(synchronized_body),
            }),
            catches,
            finally,
        })
    }
}

/// A cleanup clause repeated around typed catch bodies is an outer lexical
/// protection scope, not a sibling catch. Region reduction keeps the complete
/// handler bodies here; nesting after envelope canonicalization prevents a
/// shared coroutine handler tail from being moved outside the cleanup.
struct HandlerCleanupEnvelopePlacement<'a> {
    regions: &'a RegionGraph,
}

impl<'a> HandlerCleanupEnvelopePlacement<'a> {
    fn apply(regions: &'a RegionGraph, root: SemanticNode) -> Result<SemanticNode, StructureError> {
        Self { regions }.fold_node(root)
    }

    fn protects(&self, cleanup: RegionId, handler: RegionId) -> Result<bool, StructureError> {
        for owner in self.regions.handler_owners(cleanup) {
            if owner == handler
                || self
                    .regions
                    .tree()
                    .is_ancestor(handler, owner)
                    .map_err(StructureError::from)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn nest(
        region: RegionId,
        body: Box<SemanticNode>,
        mut catches: Vec<SemanticCatch>,
        finally: Option<SemanticFinally>,
    ) -> Result<SemanticNode, StructureError> {
        let cleanup = catches
            .pop()
            .expect("outer cleanup nesting requires one cleanup clause");
        let cleanup_key = EnvelopeKey {
            catches: vec![cleanup.region],
            finally: None,
        };
        Self::strip_redundant_cleanup(&mut catches, &cleanup_key)?;
        let inner = SemanticNode::Try {
            region,
            body,
            catches,
            finally: None,
        };
        Ok(SemanticNode::Try {
            region,
            body: Box::new(inner),
            catches: vec![cleanup],
            finally,
        })
    }

    fn strip_redundant_cleanup(
        catches: &mut [SemanticCatch],
        cleanup_key: &EnvelopeKey,
    ) -> Result<(), StructureError> {
        for catch in catches {
            catch.body = StripEnvelopeFamily { key: cleanup_key }
                .fold_node(std::mem::replace(&mut catch.body, SemanticNode::Empty))?;
        }
        Ok(())
    }
}

impl SemanticFolder for HandlerCleanupEnvelopePlacement<'_> {
    type Error = StructureError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::Try {
            region,
            mut body,
            catches,
            finally,
        } = node
        else {
            return Ok(node);
        };
        let Some(cleanup) = catches.last().map(|catch| catch.region) else {
            return Ok(SemanticNode::Try {
                region,
                body,
                catches,
                finally,
            });
        };
        let cleanup_kind = self
            .regions
            .tree()
            .region(cleanup)
            .ok_or(StructureError::UnknownRegion(cleanup))?;
        if finally.is_none()
            && catches.len() == 1
            && matches!(&cleanup_kind.kind, crate::ir::RegionKind::Cleanup(_))
        {
            if let SemanticNode::Try {
                catches: inner_catches,
                ..
            } = body.as_mut()
            {
                let cleanup_key = EnvelopeKey {
                    catches: vec![cleanup],
                    finally: None,
                };
                Self::strip_redundant_cleanup(inner_catches, &cleanup_key)?;
            }
            return Ok(SemanticNode::Try {
                region,
                body,
                catches,
                finally,
            });
        }
        if finally.is_some()
            || !matches!(&cleanup_kind.kind, crate::ir::RegionKind::Cleanup(_))
            || catches.len() < 2
        {
            return Ok(SemanticNode::Try {
                region,
                body,
                catches,
                finally,
            });
        }
        for catch in &catches[..catches.len() - 1] {
            let kind = self
                .regions
                .tree()
                .region(catch.region)
                .ok_or(StructureError::UnknownRegion(catch.region))?;
            if !matches!(&kind.kind, crate::ir::RegionKind::Catch(_))
                || !self.protects(cleanup, catch.region)?
            {
                return Ok(SemanticNode::Try {
                    region,
                    body,
                    catches,
                    finally,
                });
            }
        }
        Self::nest(region, body, catches, finally)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        ArgType, Block, CatchRegion, InsnArg, InsnNode, RegionKind, RegisterArg, SemanticBlock,
        SemanticExpression, SemanticLeave, SemanticLoopKind, SemanticLoopTest, SemanticOperand,
        SemanticPredicate, SynchronizedRegion,
    };

    fn control_leave(region: RegionId, kind: SemanticLeaveKind) -> SemanticNode {
        SemanticNode::Leave(SemanticLeave {
            site: None,
            condition: None,
            kind,
            edge: None,
            origin: None,
            source: region,
            destination: region,
            target: region,
            cleanup: Vec::new(),
        })
    }

    fn loop_node(region: RegionId, body: SemanticNode) -> SemanticNode {
        SemanticNode::Loop {
            control: SemanticLoopControl::Region(region),
            header: None,
            kind: SemanticLoopKind::Endless,
            test: SemanticLoopTest::pure(SemanticPredicate::True),
            body: Box::new(body),
        }
    }

    fn envelope(handler: RegionId, body: SemanticNode) -> ExceptionEnvelope {
        ExceptionEnvelope {
            catches: vec![SemanticCatch {
                region: handler,
                exception_types: Vec::new(),
                exception_value: None,
                body,
            }],
            finally: None,
        }
    }

    #[test]
    fn envelope_does_not_cross_handler_control_dependency() {
        let loop_region = RegionId::new(1);
        let handler_region = RegionId::new(2);
        let envelope = envelope(
            handler_region,
            control_leave(loop_region, SemanticLeaveKind::Break),
        );

        assert!(!envelope.can_wrap(&loop_node(loop_region, SemanticNode::Empty)));
        assert!(envelope.can_wrap(&loop_node(RegionId::new(3), SemanticNode::Empty,)));
    }

    #[test]
    fn envelope_shape_includes_handler_control_dependencies() {
        let loop_region = RegionId::new(1);
        let handler_region = RegionId::new(2);
        let label = SemanticLabel::block(RegionId::new(4), crate::ir::BlockId::new(88));
        let with_break = envelope(
            handler_region,
            control_leave(loop_region, SemanticLeaveKind::Break),
        );
        let with_break_label = envelope(
            handler_region,
            SemanticNode::Leave(SemanticLeave {
                site: None,
                condition: None,
                kind: SemanticLeaveKind::BreakLabel(label),
                edge: None,
                origin: None,
                source: handler_region,
                destination: RegionId::new(4),
                target: RegionId::new(4),
                cleanup: Vec::new(),
            }),
        );

        assert!(!with_break.same_shape(&with_break_label));
        assert!(escapes_structured_control(
            &with_break
                .clone()
                .attach(RegionId::new(5), SemanticNode::Empty,)
        ));
        assert!(!escapes_structured_control(&loop_node(
            loop_region,
            with_break.attach(RegionId::new(5), SemanticNode::Empty),
        )));
    }

    #[test]
    fn locally_bound_handler_control_is_not_a_free_dependency() {
        let loop_region = RegionId::new(1);
        let handler_region = RegionId::new(2);
        let envelope = envelope(
            handler_region,
            loop_node(
                loop_region,
                control_leave(loop_region, SemanticLeaveKind::Continue),
            ),
        );

        assert!(envelope.can_wrap(&loop_node(loop_region, SemanticNode::Empty)));
    }

    #[test]
    fn repeated_handler_cleanup_wraps_typed_catches() {
        let region = RegionId::new(1);
        let typed = RegionId::new(2);
        let cleanup = RegionId::new(3);
        let catches = vec![
            SemanticCatch {
                region: typed,
                exception_types: vec![ArgType::object("java/lang/Exception")],
                exception_value: None,
                body: envelope(cleanup, SemanticNode::Empty)
                    .attach(RegionId::new(4), SemanticNode::Empty),
            },
            SemanticCatch {
                region: cleanup,
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                body: SemanticNode::Empty,
            },
        ];

        let nested = HandlerCleanupEnvelopePlacement::nest(
            region,
            Box::new(SemanticNode::Empty),
            catches,
            None,
        )
        .unwrap();

        let SemanticNode::Try {
            body,
            catches: outer,
            ..
        } = nested
        else {
            panic!("cleanup must form an outer try");
        };
        assert_eq!(outer[0].region, cleanup);
        let SemanticNode::Try { catches: inner, .. } = *body else {
            panic!("typed catches must remain on the inner try");
        };
        assert_eq!(inner[0].region, typed);
        assert!(matches!(inner[0].body, SemanticNode::Empty));
    }

    fn synchronized_try_with_catch(
        catch_inside_monitor: bool,
    ) -> (CFG, crate::ir::RegionTree, SemanticNode) {
        let mut tree = crate::ir::RegionTree::new(Some(crate::ir::BlockId::new(0)));
        let root = tree.root();
        let lock = RegisterArg::new_ssa(0, 0, ArgType::object("java/lang/Object"));
        let prefix_value = RegisterArg::new_ssa(1, 0, ArgType::INT);
        let prefix = crate::ir::BlockId::new(4);
        let mut prefix_block = Block::new(prefix.raw());
        prefix_block.push(InsnNode::const_val(prefix_value, 0, ArgType::INT));
        let mut cfg = CFG::new("external_monitor_handler_placement");
        cfg.entry = prefix;
        cfg.add_block(prefix_block);
        let synchronized = tree
            .add_child(
                root,
                RegionKind::Synchronized(SynchronizedRegion {
                    lock: InsnArg::Reg(lock.clone()),
                    method: false,
                    release_handlers: BTreeSet::new(),
                }),
                Some(crate::ir::BlockId::new(1)),
            )
            .unwrap();
        let protected = tree
            .add_child(
                synchronized,
                RegionKind::Try,
                Some(crate::ir::BlockId::new(2)),
            )
            .unwrap();
        let catch_parent = if catch_inside_monitor {
            synchronized
        } else {
            root
        };
        let catch = tree
            .add_child(
                catch_parent,
                RegionKind::Catch(CatchRegion {
                    exception_types: vec![ArgType::object("java/lang/Exception")],
                    exception_value: None,
                    continuation: None,
                }),
                Some(crate::ir::BlockId::new(3)),
            )
            .unwrap();
        let node = SemanticNode::Synchronized {
            region: synchronized,
            lock: SemanticOperand::new(SemanticExpression::Register(lock)),
            method: false,
            body: Box::new(SemanticNode::Sequence(vec![
                SemanticNode::BasicBlock(SemanticBlock {
                    id: prefix,
                    statements: Vec::new(),
                }),
                SemanticNode::Try {
                    region: protected,
                    body: Box::new(SemanticNode::Empty),
                    catches: vec![SemanticCatch {
                        region: catch,
                        exception_types: vec![ArgType::object("java/lang/Exception")],
                        exception_value: None,
                        body: SemanticNode::Empty,
                    }],
                    finally: None,
                },
            ])),
        };
        (cfg, tree, node)
    }

    #[test]
    fn external_catch_is_hoisted_outside_explicit_synchronization() {
        let (cfg, tree, node) = synchronized_try_with_catch(false);

        let result = ExternalMonitorHandlerPlacement::apply(&cfg, &tree, node).unwrap();
        let SemanticNode::Try { body, catches, .. } = result else {
            panic!("external catch must wrap the monitor scope");
        };
        assert_eq!(catches.len(), 1);
        assert!(matches!(*body, SemanticNode::Synchronized { .. }));
    }

    #[test]
    fn catch_inside_synchronization_stays_inside_monitor_scope() {
        let (cfg, tree, node) = synchronized_try_with_catch(true);

        let result = ExternalMonitorHandlerPlacement::apply(&cfg, &tree, node).unwrap();
        let SemanticNode::Synchronized { body, .. } = result else {
            panic!("internal catch must stay inside the monitor scope");
        };
        assert!(matches!(*body, SemanticNode::Sequence(_)));
    }
}
