use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::{InstructionEffects, LexicalBoundaryAnalysis};
use crate::ir::{BlockId, InsnArg, CFG};

use super::{
    LaminarPlacement, RegionId, RegionInvariantError, RegionKind, RegionPlacement, RegionTree,
    StructuredRegion, SynchronizedRegion,
};

impl RegionTree {
    pub fn new(method_entry: Option<BlockId>) -> Self {
        let root = RegionId::new(0);
        let mut method = StructuredRegion::new(root, RegionKind::Method, None);
        method.entry = method_entry;

        let mut regions = BTreeMap::new();
        regions.insert(root, method);

        Self {
            root,
            next_id: 1,
            regions,
        }
    }

    pub fn root(&self) -> RegionId {
        self.root
    }

    pub fn region(&self, id: RegionId) -> Option<&StructuredRegion> {
        self.regions.get(&id)
    }

    pub fn region_mut(&mut self, id: RegionId) -> Option<&mut StructuredRegion> {
        self.regions.get_mut(&id)
    }

    pub fn regions(&self) -> impl Iterator<Item = &StructuredRegion> {
        self.regions.values()
    }

    pub(super) fn cover_method(&mut self, cfg: &CFG) -> Result<(), RegionInvariantError> {
        let root = self.root;
        self.region_mut(root)
            .ok_or(RegionInvariantError::UnknownRegion(root))?
            .blocks
            .extend(cfg.block_ids());
        Ok(())
    }

    pub(super) fn synchronize(
        &mut self,
        cfg: &CFG,
        region_handlers: &BTreeMap<RegionId, Vec<RegionId>>,
        owner: RegionId,
        handlers: &[RegionId],
        lock: InsnArg,
        enter: BlockId,
        entry: BlockId,
        blocks: &BTreeSet<BlockId>,
        release_entries: &BTreeSet<BlockId>,
        release_segments: &BTreeSet<RegionId>,
        method: bool,
    ) -> Result<SynchronizationRewrite, RegionInvariantError> {
        if release_entries.is_empty() {
            return self.insert_standalone_synchronization(cfg, lock, enter, entry, blocks, method);
        }
        SynchronizationPlacement::analyze(
            self,
            cfg,
            owner,
            handlers,
            lock,
            enter,
            entry,
            blocks,
            release_entries,
            release_segments,
            method,
        )?
        .apply(self, cfg, region_handlers)
    }

    fn insert_standalone_synchronization(
        &mut self,
        cfg: &CFG,
        lock: InsnArg,
        enter: BlockId,
        entry: BlockId,
        blocks: &BTreeSet<BlockId>,
        method: bool,
    ) -> Result<SynchronizationRewrite, RegionInvariantError> {
        self.close_lexical_scope(enter, entry, blocks)?;
        // A handler can cross the runtime monitor-exit boundary only through
        // one proven continuation, such as a return lowered after monitor-exit.
        SynchronizationPlacement::partition_handler_regions_for(self, cfg, None, blocks)?;
        let kind = RegionKind::Synchronized(SynchronizedRegion {
            lock,
            method,
            release_handlers: BTreeSet::new(),
        });
        let region = match self.insert_laminar_region(kind, entry, blocks.clone())? {
            RegionPlacement::Inserted(region) => region,
            RegionPlacement::Residual => {
                let regions = self
                    .regions()
                    .filter(|region| {
                        !region.blocks.is_disjoint(blocks)
                            && !region.blocks.is_subset(blocks)
                            && !blocks.is_subset(&region.blocks)
                    })
                    .map(|region| {
                        (
                            region.id,
                            region.kind.clone(),
                            region.entry,
                            region.blocks.clone(),
                        )
                    })
                    .collect();
                return Err(RegionInvariantError::SynchronizationRegionOverlap {
                    entry,
                    blocks: blocks.clone(),
                    regions,
                });
            }
        };
        self.enclose_region(region)?;
        Ok(SynchronizationRewrite {
            removed: BTreeSet::new(),
            splits: Vec::new(),
            handler_splits: Vec::new(),
        })
    }

    fn close_lexical_scope(
        &mut self,
        enter: BlockId,
        entry: BlockId,
        blocks: &BTreeSet<BlockId>,
    ) -> Result<(), RegionInvariantError> {
        let owner = self.common_ancestor(self.owner(enter)?, self.owner(entry)?)?;
        for ancestor in self.parent_chain(owner)? {
            self.region_mut(ancestor)
                .ok_or(RegionInvariantError::UnknownRegion(ancestor))?
                .blocks
                .extend(blocks.iter().copied());
        }
        Ok(())
    }

    pub(super) fn insert_laminar_region(
        &mut self,
        kind: RegionKind,
        entry: BlockId,
        blocks: BTreeSet<BlockId>,
    ) -> Result<RegionPlacement, RegionInvariantError> {
        let placement = self.laminar_placement(&kind, entry, &blocks)?;
        let Some(placement) = placement else {
            return Ok(RegionPlacement::Residual);
        };
        let id = self.add_child(placement.parent, kind, Some(entry))?;
        self.region_mut(id)
            .ok_or(RegionInvariantError::UnknownRegion(id))?
            .blocks = blocks;
        self.region_mut(placement.parent)
            .ok_or(RegionInvariantError::UnknownRegion(placement.parent))?
            .children
            .retain(|child| !placement.reparent.contains(child));
        for child in placement.reparent {
            self.region_mut(child)
                .ok_or(RegionInvariantError::UnknownRegion(child))?
                .parent = Some(id);
            self.region_mut(id)
                .ok_or(RegionInvariantError::UnknownRegion(id))?
                .children
                .push(child);
        }
        Ok(RegionPlacement::Inserted(id))
    }

    pub(super) fn laminar_closure(&self, seed: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut blocks = seed.clone();
        loop {
            let additions = self
                .regions()
                .filter(|region| region.id != self.root())
                .filter(|region| {
                    !region.blocks.is_disjoint(&blocks)
                        && !region.blocks.is_subset(&blocks)
                        && !blocks.is_subset(&region.blocks)
                })
                .flat_map(|region| region.blocks.iter().copied())
                .filter(|block| !blocks.contains(block))
                .collect::<BTreeSet<_>>();
            if additions.is_empty() {
                return blocks;
            }
            blocks.extend(additions);
        }
    }

    /// Loops and switches are indivisible lexical control domains. Semantic
    /// regions recovered from dataflow may omit non-throwing blocks inside
    /// them, but a source-level construct that crosses such a domain must own
    /// the complete domain to keep the region tree laminar.
    pub(super) fn control_domain_closure(
        &self,
        seed: &BTreeSet<BlockId>,
        lexical_anchor: BlockId,
    ) -> BTreeSet<BlockId> {
        let mut blocks = seed.clone();
        loop {
            let additions = self
                .regions()
                .filter(|region| {
                    matches!(&region.kind, RegionKind::Loop(_) | RegionKind::Switch(_))
                })
                .filter(|region| !region.blocks.contains(&lexical_anchor))
                .filter(|region| {
                    !region.blocks.is_disjoint(&blocks)
                        && !region.blocks.is_subset(&blocks)
                        && !blocks.is_subset(&region.blocks)
                })
                .flat_map(|region| region.blocks.iter().copied())
                .filter(|block| !blocks.contains(block))
                .collect::<BTreeSet<_>>();
            if additions.is_empty() {
                return blocks;
            }
            blocks.extend(additions);
        }
    }

    /// A lexical region that owns a structural entry owns the corresponding
    /// control construct. Keeping only the header would move dispatch or loop
    /// control into a child region and leave the parent impossible to reduce.
    pub(super) fn control_entry_closure(&self, seed: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut blocks = seed.clone();
        loop {
            let additions = self
                .regions()
                .filter(|region| {
                    matches!(&region.kind, RegionKind::Loop(_) | RegionKind::Switch(_))
                })
                .filter(|region| region.entry.is_some_and(|entry| blocks.contains(&entry)))
                .flat_map(|region| region.blocks.iter().copied())
                .filter(|block| !blocks.contains(block))
                .collect::<BTreeSet<_>>();
            if additions.is_empty() {
                return blocks;
            }
            blocks.extend(additions);
        }
    }

    fn laminar_placement(
        &self,
        kind: &RegionKind,
        entry: BlockId,
        blocks: &BTreeSet<BlockId>,
    ) -> Result<Option<LaminarPlacement>, RegionInvariantError> {
        let candidates = self
            .regions
            .values()
            .filter(|region| blocks.is_subset(&region.blocks))
            .filter(|region| {
                let established_handler_domain = matches!(kind, RegionKind::Try)
                    && matches!(
                        &region.kind,
                        RegionKind::Catch(_) | RegionKind::Finally | RegionKind::Cleanup(_)
                    );
                region.blocks != *blocks
                    || region.entry != Some(entry)
                    || established_handler_domain
                    || !kind.encloses_coincident(&region.kind)
            })
            .map(|region| {
                self.parent_chain(region.id).map(|chain| {
                    (
                        region.blocks.len(),
                        std::cmp::Reverse(chain.len()),
                        region.id,
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let parent = candidates
            .into_iter()
            .min()
            .map(|(_, _, region)| region)
            .ok_or_else(|| RegionInvariantError::UncontainedRegion {
                entry,
                blocks: blocks.clone(),
            })?;
        for region in self.regions.values() {
            let intersects = !blocks.is_disjoint(&region.blocks);
            let nested = blocks.is_subset(&region.blocks) || region.blocks.is_subset(&blocks);
            if intersects && !nested {
                return Ok(None);
            }
        }
        let parent_region = self
            .region(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?;
        for child in &parent_region.children {
            let child_region = self
                .region(*child)
                .ok_or(RegionInvariantError::UnknownRegion(*child))?;
            if child_region.blocks.is_subset(blocks) {
                continue;
            }
            if self.descendants_intersect(*child, blocks)? {
                return Ok(None);
            }
        }
        let reparent = self
            .region(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?
            .children
            .iter()
            .copied()
            .filter(|child| {
                self.region(*child)
                    .is_some_and(|region| region.blocks.is_subset(blocks))
            })
            .collect();
        Ok(Some(LaminarPlacement { parent, reparent }))
    }

    pub(super) fn canonicalize_nesting(&mut self) -> Result<(), RegionInvariantError> {
        loop {
            if let Some((outer, inner, parent)) = self.parent_child_inversion() {
                self.rotate_parent_child(outer, inner, parent)?;
                continue;
            }
            if let Some((outer, inner)) = self.overlapping_siblings()? {
                self.reparent(inner, outer)?;
                continue;
            }
            return Ok(());
        }
    }

    pub(super) fn remove_control_regions(&mut self) -> Result<(), RegionInvariantError> {
        let mut controls = self
            .regions
            .values()
            .filter(|region| matches!(&region.kind, RegionKind::Loop(_) | RegionKind::Switch(_)))
            .map(|region| {
                self.parent_chain(region.id)
                    .map(|parents| (parents.len(), region.id))
            })
            .collect::<Result<Vec<_>, _>>()?;
        controls.sort_by_key(|(depth, region)| (std::cmp::Reverse(*depth), *region));
        for (_, control) in controls {
            let Some(region) = self.region(control).cloned() else {
                continue;
            };
            let parent = region
                .parent
                .ok_or(RegionInvariantError::MissingRegionParent {
                    region: control,
                    parent: self.root,
                })?;
            for child in region.children {
                self.reparent(child, parent)?;
            }
            self.unlink_child(parent, control)?;
            self.regions.remove(&control);
        }
        Ok(())
    }

    fn parent_child_inversion(&self) -> Option<(RegionId, RegionId, RegionId)> {
        self.regions.values().find_map(|outer| {
            outer.children.iter().find_map(|child| {
                let inner = self.region(*child)?;
                // A protected range nested in a handler domain is a lexical
                // child even when both reduce to the same CFG blocks. Kind
                // precedence is only a tie-breaker when no handler-domain
                // ownership has already established that relation.
                if matches!(
                    (&outer.kind, &inner.kind),
                    (
                        RegionKind::Catch(_) | RegionKind::Finally | RegionKind::Cleanup(_),
                        RegionKind::Try
                    )
                ) {
                    return None;
                }
                (inner.blocks == outer.blocks
                    && inner.entry == outer.entry
                    && inner.kind.encloses_coincident(&outer.kind))
                .then_some((outer.id, inner.id, outer.parent?))
            })
        })
    }

    fn overlapping_siblings(&self) -> Result<Option<(RegionId, RegionId)>, RegionInvariantError> {
        for parent in self.regions.values() {
            for (index, left_id) in parent.children.iter().copied().enumerate() {
                let left = self
                    .region(left_id)
                    .ok_or(RegionInvariantError::UnknownRegion(left_id))?;
                for right_id in parent.children.iter().copied().skip(index + 1) {
                    let right = self
                        .region(right_id)
                        .ok_or(RegionInvariantError::UnknownRegion(right_id))?;
                    if left.blocks.is_disjoint(&right.blocks) {
                        let left_reaches_right =
                            self.descendants_intersect(left_id, &right.blocks)?;
                        let right_reaches_left =
                            self.descendants_intersect(right_id, &left.blocks)?;
                        match (left_reaches_right, right_reaches_left) {
                            (true, false) => return Ok(Some((left_id, right_id))),
                            (false, true) => return Ok(Some((right_id, left_id))),
                            _ => {}
                        }
                        continue;
                    }
                    if right.blocks != left.blocks && right.blocks.is_subset(&left.blocks) {
                        return Ok(Some((left_id, right_id)));
                    }
                    if left.blocks != right.blocks && left.blocks.is_subset(&right.blocks) {
                        return Ok(Some((right_id, left_id)));
                    }
                    if left.blocks == right.blocks && left.entry == right.entry {
                        if left.kind.encloses_coincident(&right.kind) {
                            return Ok(Some((left_id, right_id)));
                        }
                        if right.kind.encloses_coincident(&left.kind) {
                            return Ok(Some((right_id, left_id)));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    fn rotate_parent_child(
        &mut self,
        outer: RegionId,
        inner: RegionId,
        parent: RegionId,
    ) -> Result<(), RegionInvariantError> {
        self.unlink_child(parent, outer)?;
        self.unlink_child(outer, inner)?;
        self.link_child(parent, inner)?;
        self.link_child(inner, outer)
    }

    pub(super) fn reparent(
        &mut self,
        region: RegionId,
        parent: RegionId,
    ) -> Result<(), RegionInvariantError> {
        let current = self.region(region).and_then(|region| region.parent).ok_or(
            RegionInvariantError::MissingRegionParent {
                region,
                parent: self.root,
            },
        )?;
        self.unlink_child(current, region)?;
        self.link_child(parent, region)
    }

    fn unlink_child(
        &mut self,
        parent: RegionId,
        child: RegionId,
    ) -> Result<(), RegionInvariantError> {
        let parent = self
            .region_mut(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?;
        let Some(position) = parent
            .children
            .iter()
            .position(|candidate| *candidate == child)
        else {
            return Err(RegionInvariantError::MissingChildLink {
                parent: parent.id,
                child,
            });
        };
        parent.children.remove(position);
        Ok(())
    }

    fn link_child(
        &mut self,
        parent: RegionId,
        child: RegionId,
    ) -> Result<(), RegionInvariantError> {
        self.region_mut(child)
            .ok_or(RegionInvariantError::UnknownRegion(child))?
            .parent = Some(parent);
        let children = &mut self
            .region_mut(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?
            .children;
        children.push(child);
        children.sort_unstable();
        children.dedup();
        Ok(())
    }

    fn descendants_intersect(
        &self,
        region: RegionId,
        blocks: &BTreeSet<BlockId>,
    ) -> Result<bool, RegionInvariantError> {
        let mut pending = self
            .region(region)
            .ok_or(RegionInvariantError::UnknownRegion(region))?
            .children
            .clone();
        while let Some(child) = pending.pop() {
            let child = self
                .region(child)
                .ok_or(RegionInvariantError::UnknownRegion(child))?;
            if !child.blocks.is_disjoint(blocks) {
                return Ok(true);
            }
            pending.extend(child.children.iter().copied());
        }
        Ok(false)
    }

    pub(super) fn block_owners(
        &self,
        cfg: &CFG,
    ) -> Result<BTreeMap<BlockId, RegionId>, RegionInvariantError> {
        cfg.block_ids()
            .into_iter()
            .map(|block| self.owner(block).map(|owner| (block, owner)))
            .collect()
    }

    pub fn add_child(
        &mut self,
        parent: RegionId,
        kind: RegionKind,
        entry: Option<BlockId>,
    ) -> Result<RegionId, RegionInvariantError> {
        if !self.regions.contains_key(&parent) {
            return Err(RegionInvariantError::UnknownRegion(parent));
        }

        let id = RegionId::new(self.next_id);
        self.next_id += 1;

        let mut region = StructuredRegion::new(id, kind, Some(parent));
        region.entry = entry;
        self.regions.insert(id, region);
        self.regions
            .get_mut(&parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?
            .children
            .push(id);
        Ok(id)
    }

    pub fn add_block(
        &mut self,
        region: RegionId,
        block: BlockId,
    ) -> Result<(), RegionInvariantError> {
        self.regions
            .get_mut(&region)
            .ok_or(RegionInvariantError::UnknownRegion(region))?
            .blocks
            .insert(block);
        Ok(())
    }

    /// Closes lexical ownership after all region rewrites have settled.
    ///
    /// Intermediate exception/control trees may temporarily rotate parent
    /// links, so eager propagation in `add_block` is invalid. At the stable
    /// RegionGraph boundary every child domain must be contained by each
    /// ancestor, and this closure establishes that invariant in depth order.
    pub(super) fn close_ancestor_ownership(&mut self) -> Result<(), RegionInvariantError> {
        let mut regions = self
            .regions()
            .map(|region| {
                self.parent_chain(region.id)
                    .map(|chain| (chain.len(), region.id))
            })
            .collect::<Result<Vec<_>, _>>()?;
        regions.sort_by_key(|(depth, _)| std::cmp::Reverse(*depth));
        for (_, region) in regions {
            let current = self
                .region(region)
                .ok_or(RegionInvariantError::UnknownRegion(region))?
                .clone();
            let Some(parent) = current.parent else {
                continue;
            };
            self.region_mut(parent)
                .ok_or(RegionInvariantError::UnknownRegion(parent))?
                .blocks
                .extend(current.blocks);
        }
        Ok(())
    }

    pub(super) fn remove_region_promoting_children(
        &mut self,
        region: RegionId,
    ) -> Result<(), RegionInvariantError> {
        if region == self.root {
            return Err(RegionInvariantError::UnknownRegion(region));
        }
        let current = self
            .region(region)
            .ok_or(RegionInvariantError::UnknownRegion(region))?;
        let parent = current
            .parent
            .ok_or(RegionInvariantError::MissingRegionParent {
                region,
                parent: self.root,
            })?;
        let children = current.children.clone();
        let blocks = current.blocks.clone();
        self.region_mut(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?
            .children
            .retain(|child| *child != region);
        for child in &children {
            self.region_mut(*child)
                .ok_or(RegionInvariantError::UnknownRegion(*child))?
                .parent = Some(parent);
        }
        let parent = self
            .region_mut(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?;
        parent.blocks.extend(blocks);
        parent.children.extend(children);
        parent.children.sort_unstable();
        parent.children.dedup();
        self.regions.remove(&region);
        Ok(())
    }

    fn enclose_region(&mut self, region: RegionId) -> Result<(), RegionInvariantError> {
        let blocks = self
            .region(region)
            .ok_or(RegionInvariantError::UnknownRegion(region))?
            .blocks
            .clone();
        for ancestor in self.parent_chain(region)?.into_iter().skip(1) {
            let boundary = self.region(ancestor).is_some_and(|region| {
                matches!(
                    &region.kind,
                    RegionKind::Catch(_) | RegionKind::Finally | RegionKind::Cleanup(_)
                )
            });
            self.region_mut(ancestor)
                .ok_or(RegionInvariantError::UnknownRegion(ancestor))?
                .blocks
                .extend(blocks.iter().copied());
            if boundary {
                break;
            }
        }
        Ok(())
    }

    pub fn parent_chain(
        &self,
        mut region: RegionId,
    ) -> Result<Vec<RegionId>, RegionInvariantError> {
        let mut chain = Vec::new();
        let mut visited = BTreeSet::new();
        loop {
            if !visited.insert(region) {
                chain.push(region);
                return Err(RegionInvariantError::RegionParentCycle(chain));
            }
            let current = self
                .region(region)
                .ok_or(RegionInvariantError::UnknownRegion(region))?;
            chain.push(region);
            match current.parent {
                Some(parent) => region = parent,
                None => break,
            }
        }
        Ok(chain)
    }

    pub fn is_ancestor(
        &self,
        ancestor: RegionId,
        region: RegionId,
    ) -> Result<bool, RegionInvariantError> {
        Ok(self.parent_chain(region)?.contains(&ancestor))
    }

    pub fn common_ancestor(
        &self,
        left: RegionId,
        right: RegionId,
    ) -> Result<RegionId, RegionInvariantError> {
        let right_ancestors = self
            .parent_chain(right)?
            .into_iter()
            .collect::<BTreeSet<_>>();
        self.parent_chain(left)?
            .into_iter()
            .find(|candidate| right_ancestors.contains(candidate))
            .ok_or(RegionInvariantError::NoCommonAncestor { left, right })
    }

    pub fn owner(&self, block: BlockId) -> Result<RegionId, RegionInvariantError> {
        let mut candidates = self
            .regions
            .values()
            .filter(|region| region.owns_block(block))
            .map(|region| {
                self.parent_chain(region.id)
                    .map(|chain| (chain.len(), region.id))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let depth = candidates
            .iter()
            .map(|(depth, _)| *depth)
            .max()
            .ok_or(RegionInvariantError::MissingOwner(block))?;
        candidates.retain(|(candidate_depth, _)| *candidate_depth == depth);
        if candidates.len() != 1 {
            return Err(RegionInvariantError::AmbiguousOwner {
                block,
                regions: candidates.into_iter().map(|(_, region)| region).collect(),
            });
        }
        candidates
            .first()
            .map(|(_, owner)| *owner)
            .ok_or(RegionInvariantError::MissingOwner(block))
    }

    pub(super) fn verify(&self, cfg: &CFG) -> Result<(), RegionInvariantError> {
        let root = self
            .region(self.root)
            .ok_or(RegionInvariantError::UnknownRegion(self.root))?;
        if root.parent.is_some() {
            return Err(RegionInvariantError::ChildParentMismatch {
                parent: self.root,
                child: self.root,
                actual: root.parent,
            });
        }

        for region in self.regions.values() {
            if region.id != self.root {
                let parent = region
                    .parent
                    .ok_or(RegionInvariantError::MissingRegionParent {
                        region: region.id,
                        parent: self.root,
                    })?;
                let owner =
                    self.region(parent)
                        .ok_or(RegionInvariantError::MissingRegionParent {
                            region: region.id,
                            parent,
                        })?;
                if owner
                    .children
                    .iter()
                    .filter(|child| **child == region.id)
                    .count()
                    != 1
                {
                    return Err(RegionInvariantError::MissingChildLink {
                        parent,
                        child: region.id,
                    });
                }
            }
            let mut children = BTreeSet::new();
            for child in &region.children {
                if !children.insert(*child) {
                    return Err(RegionInvariantError::MissingChildLink {
                        parent: region.id,
                        child: *child,
                    });
                }
                let actual = self
                    .region(*child)
                    .ok_or(RegionInvariantError::UnknownRegion(*child))?
                    .parent;
                if actual != Some(region.id) {
                    return Err(RegionInvariantError::ChildParentMismatch {
                        parent: region.id,
                        child: *child,
                        actual,
                    });
                }
            }
            if let RegionKind::Synchronized(synchronized) = &region.kind {
                for handler in &synchronized.release_handlers {
                    let valid = self
                        .region(*handler)
                        .is_some_and(|handler| handler.kind.is_release_handler());
                    if !valid {
                        return Err(RegionInvariantError::InvalidSynchronizationRelease {
                            region: region.id,
                            handler: *handler,
                        });
                    }
                }
            }
            self.parent_chain(region.id)?;
            if let Some(entry) = region.entry {
                if !region.blocks.contains(&entry) {
                    return Err(RegionInvariantError::RegionEntryOutsideBody {
                        region: region.id,
                        entry,
                    });
                }
            }
        }

        let regions = self.regions.values().collect::<Vec<_>>();
        for (index, left) in regions.iter().enumerate() {
            for right in regions.iter().skip(index + 1) {
                let intersects = !left.blocks.is_disjoint(&right.blocks);
                let laminar =
                    left.blocks.is_subset(&right.blocks) || right.blocks.is_subset(&left.blocks);
                if intersects && !laminar {
                    return Err(RegionInvariantError::RegionOverlap {
                        left: left.id,
                        right: right.id,
                        intersection: left.blocks.intersection(&right.blocks).copied().collect(),
                        left_only: left.blocks.difference(&right.blocks).copied().collect(),
                        right_only: right.blocks.difference(&left.blocks).copied().collect(),
                    });
                }
                if intersects
                    && !self.is_ancestor(left.id, right.id)?
                    && !self.is_ancestor(right.id, left.id)?
                {
                    return Err(RegionInvariantError::UnnestedOverlap {
                        left: left.id,
                        right: right.id,
                        left_parent: left.parent,
                        right_parent: right.parent,
                        left_kind: left.kind.clone(),
                        right_kind: right.kind.clone(),
                        left_entry: left.entry,
                        right_entry: right.entry,
                        left_blocks: left.blocks.clone(),
                        right_blocks: right.blocks.clone(),
                    });
                }
            }
        }

        for block in cfg.block_ids() {
            self.owner(block)?;
        }
        Ok(())
    }
}

struct SynchronizationPlacement {
    owner: RegionId,
    enter: BlockId,
    lock: InsnArg,
    entry: BlockId,
    blocks: BTreeSet<BlockId>,
    release_handlers: BTreeSet<RegionId>,
    user_handlers: BTreeSet<RegionId>,
    release_segments: BTreeSet<RegionId>,
    duplicate_handlers: Vec<RegionId>,
    method: bool,
}

struct ProtectedDomain {
    region: RegionId,
    handlers: BTreeSet<RegionId>,
}

pub(super) struct SynchronizationRewrite {
    pub(super) removed: BTreeSet<RegionId>,
    pub(super) splits: Vec<(RegionId, RegionId)>,
    pub(super) handler_splits: Vec<(RegionId, Vec<RegionId>)>,
}

impl SynchronizationPlacement {
    fn analyze(
        tree: &RegionTree,
        cfg: &CFG,
        owner: RegionId,
        handlers: &[RegionId],
        lock: InsnArg,
        enter: BlockId,
        entry: BlockId,
        blocks: &BTreeSet<BlockId>,
        release_entries: &BTreeSet<BlockId>,
        release_segments: &BTreeSet<RegionId>,
        method: bool,
    ) -> Result<Self, RegionInvariantError> {
        tree.region(owner)
            .ok_or(RegionInvariantError::UnknownRegion(owner))?;
        let release_handlers = handlers
            .iter()
            .copied()
            .filter(|handler| Self::is_release_entry(cfg, tree, *handler, release_entries))
            .collect::<BTreeSet<_>>();
        if release_handlers.is_empty() {
            return Err(RegionInvariantError::MissingSynchronizationHandler {
                region: owner,
                entry: release_entries.iter().copied().next().unwrap_or(entry),
            });
        }
        let nested_release_handlers = tree
            .regions
            .values()
            .filter(|region| region.id != owner)
            .filter_map(|region| match &region.kind {
                RegionKind::Synchronized(synchronized) => Some(&synchronized.release_handlers),
                _ => None,
            })
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();
        // Only this synchronization's synthetic release lies outside its
        // source body. Nested release handlers remain lexically enclosed by
        // every outer synchronization, even though their inner owner elides
        // them during semantic lowering.
        let own_release_blocks = Self::region_subtree_blocks(tree, &release_handlers)?;
        let user_handlers = handlers
            .iter()
            .copied()
            .filter(|handler| {
                !release_handlers.contains(handler) && !nested_release_handlers.contains(handler)
            })
            .collect::<BTreeSet<_>>();
        // A declared-synchronized method is one source-level lexical scope.
        // Runtime monitor analysis stops at each synthetic monitor-exit, so it
        // omits return/throw tails split after the exit. Those tails still
        // belong to the method body and can otherwise cross a user handler at
        // the same region depth. Keep only the synthetic enter and this
        // monitor's release handler outside the recovered source scope.
        let mut blocks = if method {
            cfg.block_ids()
                .into_iter()
                .filter(|block| *block != enter && !own_release_blocks.contains(block))
                .collect::<BTreeSet<_>>()
        } else {
            blocks
                .difference(&own_release_blocks)
                .copied()
                .collect::<BTreeSet<_>>()
        };
        blocks.extend(user_handlers.iter().flat_map(|handler| {
            tree.region(*handler)
                .into_iter()
                .flat_map(|region| region.blocks.iter().copied())
        }));
        blocks = tree.control_domain_closure(&blocks, enter);
        let duplicate_handlers = tree
            .regions
            .values()
            .filter(|region| !release_handlers.contains(&region.id))
            .filter(|region| !nested_release_handlers.contains(&region.id))
            .filter(|region| Self::is_release_entry(cfg, tree, region.id, release_entries))
            .filter(|region| {
                region
                    .parent
                    .and_then(|parent| tree.region(parent))
                    .and_then(|parent| parent.entry)
                    .is_some_and(|entry| blocks.contains(&entry))
            })
            .map(|region| region.id)
            .collect();
        Ok(Self {
            owner,
            enter,
            lock,
            entry,
            blocks,
            release_handlers,
            user_handlers,
            release_segments: release_segments.clone(),
            duplicate_handlers,
            method,
        })
    }

    fn apply(
        mut self,
        tree: &mut RegionTree,
        cfg: &CFG,
        region_handlers: &BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Result<SynchronizationRewrite, RegionInvariantError> {
        let mut removed = self.remove_release_segments(tree)?;
        let (wrappers, duplicate_handlers) = self.remove_duplicate_handlers(tree)?;
        removed.extend(duplicate_handlers);
        removed.extend(self.remove_empty_wrappers(tree, wrappers)?);
        let handler_splits = self.preserve_user_handlers(tree, cfg, region_handlers)?;
        self.partition_handler_regions(tree, cfg)?;
        let splits = self.partition_try_regions(tree, cfg)?;
        // Closing over a loop or switch can temporarily pull a synthetic
        // release subtree back into the recovered source body. Once handler
        // boundaries have been partitioned, exclude the final release tree so
        // monitor-exit retries remain represented by `synchronized` itself.
        let release_blocks = Self::region_subtree_blocks(tree, &self.release_handlers)?;
        self.blocks.retain(|block| !release_blocks.contains(block));
        self.place_owner(tree)?;
        self.reparent_contained_regions(tree)?;
        self.mark_release_handlers(tree)?;
        let owner = tree
            .region_mut(self.owner)
            .ok_or(RegionInvariantError::UnknownRegion(self.owner))?;
        owner.blocks = self.blocks;
        owner.entry = Some(self.entry);
        owner.kind = RegionKind::Synchronized(SynchronizedRegion {
            lock: self.lock,
            method: self.method,
            release_handlers: self.release_handlers,
        });
        owner.children.sort_unstable();
        owner.children.dedup();
        tree.enclose_region(self.owner)?;
        Ok(SynchronizationRewrite {
            removed,
            splits,
            handler_splits,
        })
    }

    fn region_subtree_blocks(
        tree: &RegionTree,
        roots: &BTreeSet<RegionId>,
    ) -> Result<BTreeSet<BlockId>, RegionInvariantError> {
        let mut blocks = BTreeSet::new();
        let mut pending = roots.iter().copied().collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(region_id) = pending.pop() {
            if !visited.insert(region_id) {
                continue;
            }
            let region = tree
                .region(region_id)
                .ok_or(RegionInvariantError::UnknownRegion(region_id))?;
            blocks.extend(region.blocks.iter().copied());
            pending.extend(region.children.iter().copied());
        }
        Ok(blocks)
    }

    fn preserve_user_handlers(
        &self,
        tree: &mut RegionTree,
        cfg: &CFG,
        region_handlers: &BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Result<Vec<(RegionId, Vec<RegionId>)>, RegionInvariantError> {
        let protected_owner = self.preserve_owner_try(tree, region_handlers)?;
        let mut protected = BTreeMap::<BTreeSet<RegionId>, BTreeSet<BlockId>>::new();
        for source in &self.blocks {
            let exceptional_targets = cfg
                .successors_with_kind(*source)
                .iter()
                .filter_map(|(target, kind)| kind.is_exception().then_some(*target))
                .collect::<BTreeSet<_>>();
            let handlers = self
                .user_handlers
                .iter()
                .copied()
                .filter(|handler| {
                    tree.region(*handler).is_some_and(|region| {
                        region
                            .entry
                            .is_some_and(|entry| exceptional_targets.contains(&entry))
                            || !region.blocks.is_disjoint(&exceptional_targets)
                    })
                })
                .collect::<BTreeSet<_>>();
            if !handlers.is_empty() {
                if protected_owner.as_ref().is_some_and(|domain| {
                    domain.handlers == handlers
                        && tree
                            .region(domain.region)
                            .is_some_and(|region| region.blocks.contains(source))
                }) {
                    continue;
                }
                if self.existing_try_preserves(tree, region_handlers, *source, &handlers) {
                    continue;
                }
                protected.entry(handlers).or_default().insert(*source);
            }
        }

        let mut splits = protected_owner
            .into_iter()
            .map(|domain| (domain.region, domain.handlers.into_iter().collect()))
            .collect::<Vec<_>>();
        for (handlers, sources) in protected {
            let entry = sources
                .iter()
                .copied()
                .next()
                .ok_or(RegionInvariantError::EmptyExceptionRegion(self.owner.raw()))?;
            let mut blocks = sources;
            let closed = tree.laminar_closure(&blocks);
            for block in closed.difference(&blocks).copied() {
                let exceptional_targets = cfg
                    .successors_with_kind(block)
                    .iter()
                    .filter_map(|(target, kind)| kind.is_exception().then_some(*target))
                    .collect::<BTreeSet<_>>();
                if exceptional_targets.is_empty() {
                    continue;
                }
                let block_handlers = self
                    .user_handlers
                    .iter()
                    .copied()
                    .filter(|handler| {
                        tree.region(*handler).is_some_and(|region| {
                            region
                                .entry
                                .is_some_and(|entry| exceptional_targets.contains(&entry))
                                || !region.blocks.is_disjoint(&exceptional_targets)
                        })
                    })
                    .collect::<BTreeSet<_>>();
                if block_handlers != handlers {
                    return Err(RegionInvariantError::SynchronizationHandlerDomainMismatch {
                        entry,
                        block,
                        expected: handlers.clone(),
                        actual: block_handlers,
                        closure: closed,
                    });
                }
            }
            blocks = closed;
            let split = match tree.insert_laminar_region(RegionKind::Try, entry, blocks.clone())? {
                RegionPlacement::Inserted(region) => region,
                RegionPlacement::Residual => {
                    return Err(RegionInvariantError::SynchronizationHandlerDomainOverlap {
                        entry,
                        blocks,
                    });
                }
            };
            splits.push((split, handlers.into_iter().collect()));
        }
        Ok(splits)
    }

    fn preserve_owner_try(
        &self,
        tree: &mut RegionTree,
        region_handlers: &BTreeMap<RegionId, Vec<RegionId>>,
    ) -> Result<Option<ProtectedDomain>, RegionInvariantError> {
        let owner = tree
            .region(self.owner)
            .cloned()
            .ok_or(RegionInvariantError::UnknownRegion(self.owner))?;
        if !matches!(owner.kind, RegionKind::Try) || !owner.blocks.is_subset(&self.blocks) {
            return Ok(None);
        }
        let handlers = region_handlers
            .get(&self.owner)
            .into_iter()
            .flatten()
            .copied()
            .filter(|handler| self.user_handlers.contains(handler))
            .collect::<BTreeSet<_>>();
        if handlers.is_empty() {
            return Ok(None);
        }

        let protected = tree.add_child(self.owner, RegionKind::Try, owner.entry)?;
        tree.region_mut(protected)
            .ok_or(RegionInvariantError::UnknownRegion(protected))?
            .blocks = owner.blocks.clone();
        for child in owner.children {
            let child_blocks = tree
                .region(child)
                .ok_or(RegionInvariantError::UnknownRegion(child))?
                .blocks
                .clone();
            if !child_blocks.is_subset(&owner.blocks) {
                continue;
            }
            Self::unlink(tree, self.owner, child)?;
            Self::link(tree, protected, child)?;
        }
        Ok(Some(ProtectedDomain {
            region: protected,
            handlers,
        }))
    }

    fn existing_try_preserves(
        &self,
        tree: &RegionTree,
        region_handlers: &BTreeMap<RegionId, Vec<RegionId>>,
        source: BlockId,
        expected: &BTreeSet<RegionId>,
    ) -> bool {
        tree.regions().any(|region| {
            region.id != self.owner
                && matches!(&region.kind, RegionKind::Try)
                && region.blocks.contains(&source)
                && region_handlers
                    .get(&region.id)
                    .into_iter()
                    .flatten()
                    .copied()
                    .filter(|handler| self.user_handlers.contains(handler))
                    .collect::<BTreeSet<_>>()
                    == *expected
        })
    }

    fn partition_try_regions(
        &self,
        tree: &mut RegionTree,
        cfg: &CFG,
    ) -> Result<Vec<(RegionId, RegionId)>, RegionInvariantError> {
        // Catch/cleanup continuations may sit after monitor-exit. Private
        // non-throwing closure can still pull those tails into an enclosing
        // try, which then only partially overlaps the recovered synchronized
        // body. Drop them before looking for a lexical cut.
        Self::strip_external_handler_continuations(tree, &self.blocks)?;
        let mut candidates = tree
            .regions
            .values()
            .filter(|region| region.id != tree.root && region.id != self.owner)
            .filter(|region| matches!(region.kind, RegionKind::Try))
            .filter(|region| {
                !region.blocks.is_disjoint(&self.blocks)
                    && !region.blocks.is_subset(&self.blocks)
                    && !self.blocks.is_subset(&region.blocks)
            })
            .map(|region| {
                tree.parent_chain(region.id)
                    .map(|chain| (chain.len(), region.id))
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Every lexical cut must preserve laminar ownership. Partition the
        // deepest protected domains first so an ancestor never encounters an
        // unpartitioned child crossing its new boundary.
        candidates.sort_by_key(|(depth, region)| (std::cmp::Reverse(*depth), *region));
        let boundaries = LexicalBoundaryAnalysis::new(cfg);
        let mut splits = Vec::new();

        for (_, candidate) in candidates {
            let region = tree
                .region(candidate)
                .cloned()
                .ok_or(RegionInvariantError::UnknownRegion(candidate))?;
            if region.blocks.contains(&self.enter)
                || region.blocks.contains(&self.entry)
                || tree.is_ancestor(candidate, self.owner)?
            {
                // An enclosing try of the synchronization owner may omit the
                // post-monitor-enter split block (especially for declared-
                // synchronized methods whose enter stays on the method entry).
                // Close that try over the recovered synchronized scope instead
                // of demanding an impossible lexical cut.
                //
                // Also realign the try entry onto the synchronized body entry.
                // After monitor-enter splitting the try often still points at a
                // later body block (e.g. B1 while sync enters at B724). Leaving
                // that stale entry creates a second synchronized port and emits
                // an empty `synchronized` prefix before the real monitor body.
                let closed = tree
                    .region_mut(candidate)
                    .ok_or(RegionInvariantError::UnknownRegion(candidate))?;
                closed.blocks.extend(self.blocks.iter().copied());
                if closed
                    .entry
                    .is_some_and(|entry| entry != self.entry && self.blocks.contains(&entry))
                {
                    closed.entry = Some(self.entry);
                }
                continue;
            }
            let entry = region
                .entry
                .ok_or(RegionInvariantError::UnknownRegion(candidate))?;
            let outside = region
                .blocks
                .difference(&self.blocks)
                .copied()
                .collect::<BTreeSet<_>>();
            let boundary = boundaries
                .partition(entry, &region.blocks, &self.blocks)
                .or_else(|| boundaries.partition(entry, &region.blocks, &outside))
                .ok_or_else(|| RegionInvariantError::RegionOverlap {
                    left: candidate,
                    right: self.owner,
                    intersection: region.blocks.intersection(&self.blocks).copied().collect(),
                    left_only: region.blocks.difference(&self.blocks).copied().collect(),
                    right_only: self.blocks.difference(&region.blocks).copied().collect(),
                })?;
            let remainder = region
                .blocks
                .difference(&boundary.blocks)
                .copied()
                .collect::<BTreeSet<_>>();
            let parent = region
                .parent
                .ok_or(RegionInvariantError::MissingRegionParent {
                    region: candidate,
                    parent: tree.root,
                })?;
            let split = tree.add_child(parent, region.kind.clone(), Some(boundary.continuation))?;
            tree.region_mut(split)
                .ok_or(RegionInvariantError::UnknownRegion(split))?
                .blocks = remainder.clone();
            tree.region_mut(candidate)
                .ok_or(RegionInvariantError::UnknownRegion(candidate))?
                .blocks = boundary.blocks.clone();

            for child in region.children {
                if child == self.owner {
                    continue;
                }
                let child_blocks = tree
                    .region(child)
                    .ok_or(RegionInvariantError::UnknownRegion(child))?
                    .blocks
                    .clone();
                if child_blocks.is_disjoint(&region.blocks)
                    || child_blocks.is_subset(&boundary.blocks)
                {
                    continue;
                }
                if child_blocks.is_subset(&remainder) {
                    Self::unlink(tree, candidate, child)?;
                    Self::link(tree, split, child)?;
                    continue;
                }
                return Err(RegionInvariantError::RegionOverlap {
                    left: candidate,
                    right: child,
                    intersection: boundary
                        .blocks
                        .intersection(&child_blocks)
                        .copied()
                        .collect(),
                    left_only: boundary.blocks.difference(&child_blocks).copied().collect(),
                    right_only: child_blocks.difference(&boundary.blocks).copied().collect(),
                });
            }
            splits.push((candidate, split));
        }
        Ok(splits)
    }

    fn strip_external_handler_continuations(
        tree: &mut RegionTree,
        sync_blocks: &BTreeSet<BlockId>,
    ) -> Result<(), RegionInvariantError> {
        let tries = tree
            .regions
            .values()
            .filter(|region| matches!(region.kind, RegionKind::Try))
            .map(|region| region.id)
            .collect::<Vec<_>>();
        for try_region in tries {
            let children = tree
                .region(try_region)
                .ok_or(RegionInvariantError::UnknownRegion(try_region))?
                .children
                .clone();
            let mut pending = children;
            let mut visited = BTreeSet::new();
            let mut external = BTreeSet::new();
            while let Some(child) = pending.pop() {
                if !visited.insert(child) {
                    continue;
                }
                let Some(region) = tree.region(child) else {
                    continue;
                };
                pending.extend(region.children.iter().copied());
                let continuation = match &region.kind {
                    RegionKind::Catch(catch) | RegionKind::Cleanup(catch) => catch.continuation,
                    _ => None,
                };
                if let Some(block) = continuation {
                    if !sync_blocks.contains(&block) {
                        external.insert(block);
                    }
                }
            }
            if external.is_empty() {
                continue;
            }
            tree.region_mut(try_region)
                .ok_or(RegionInvariantError::UnknownRegion(try_region))?
                .blocks
                .retain(|block| !external.contains(block));
        }
        Ok(())
    }

    fn remove_release_segments(
        &self,
        tree: &mut RegionTree,
    ) -> Result<BTreeSet<RegionId>, RegionInvariantError> {
        let mut segments = self
            .release_segments
            .iter()
            .copied()
            .map(|region| tree.parent_chain(region).map(|chain| (chain.len(), region)))
            .collect::<Result<Vec<_>, _>>()?;
        segments.sort_by_key(|(depth, _)| std::cmp::Reverse(*depth));
        let mut removed = BTreeSet::new();
        for (_, segment) in segments {
            if tree.region(segment).is_none() {
                continue;
            }
            Self::promote_children(tree, segment)?;
            removed.insert(segment);
        }
        Ok(removed)
    }

    fn partition_handler_regions(
        &self,
        tree: &mut RegionTree,
        cfg: &CFG,
    ) -> Result<(), RegionInvariantError> {
        Self::partition_handler_regions_for(tree, cfg, Some(self.owner), &self.blocks)
    }

    fn partition_handler_regions_for(
        tree: &mut RegionTree,
        cfg: &CFG,
        owner: Option<RegionId>,
        blocks: &BTreeSet<BlockId>,
    ) -> Result<(), RegionInvariantError> {
        let mut candidates = tree
            .regions
            .values()
            .filter(|region| region.id != tree.root && Some(region.id) != owner)
            .filter(|region| matches!(region.kind, RegionKind::Catch(_) | RegionKind::Cleanup(_)))
            .filter(|region| {
                !region.blocks.is_disjoint(blocks)
                    && !region.blocks.is_subset(blocks)
                    && !blocks.is_subset(&region.blocks)
            })
            .map(|region| {
                tree.parent_chain(region.id)
                    .map(|chain| (chain.len(), region.id))
            })
            .collect::<Result<Vec<_>, _>>()?;
        // A lexical boundary propagates from nested domains to their
        // ancestors. Cutting a parent first would temporarily leave an
        // uncut child crossing the new parent boundary.
        candidates.sort_by_key(|(depth, region)| (std::cmp::Reverse(*depth), *region));

        for (_, candidate) in candidates {
            let region = tree
                .region(candidate)
                .ok_or(RegionInvariantError::UnknownRegion(candidate))?;
            let Some(entry) = region.entry else {
                continue;
            };
            let parent = region
                .parent
                .ok_or(RegionInvariantError::MissingRegionParent {
                    region: candidate,
                    parent: tree.root,
                })?;
            let children = region.children.clone();
            let region_blocks = region.blocks.clone();
            let boundary =
                LexicalBoundaryAnalysis::new(cfg).partition(entry, &region_blocks, blocks);
            let Some(boundary) = boundary else {
                continue;
            };
            let mut promote = Vec::new();
            let mut crossing = None;
            for child in children {
                if Some(child) == owner {
                    continue;
                }
                let child_blocks = &tree
                    .region(child)
                    .ok_or(RegionInvariantError::UnknownRegion(child))?
                    .blocks;
                if child_blocks.is_disjoint(&boundary.blocks) {
                    promote.push(child);
                } else if !child_blocks.is_subset(&boundary.blocks) {
                    crossing = Some((child, child_blocks.clone()));
                    break;
                }
            }
            if let Some((child, child_blocks)) = crossing {
                return Err(RegionInvariantError::RegionOverlap {
                    left: candidate,
                    right: child,
                    intersection: boundary
                        .blocks
                        .intersection(&child_blocks)
                        .copied()
                        .collect(),
                    left_only: boundary.blocks.difference(&child_blocks).copied().collect(),
                    right_only: child_blocks.difference(&boundary.blocks).copied().collect(),
                });
            }

            let removed = region_blocks
                .difference(&boundary.blocks)
                .copied()
                .collect::<BTreeSet<_>>();
            let kind = &mut tree
                .region_mut(candidate)
                .ok_or(RegionInvariantError::UnknownRegion(candidate))?
                .kind;
            let continuation = match kind {
                RegionKind::Catch(catch) | RegionKind::Cleanup(catch) => &mut catch.continuation,
                _ => continue,
            };
            if continuation.is_some_and(|target| target != boundary.continuation) {
                continue;
            }
            *continuation = Some(boundary.continuation);
            tree.region_mut(candidate)
                .ok_or(RegionInvariantError::UnknownRegion(candidate))?
                .blocks = boundary.blocks;

            // Keep enclosing tries laminar with the monitor: they must not
            // retain the continuation that now sits outside the synchronized
            // body.
            let mut ancestor = Some(parent);
            while let Some(region_id) = ancestor {
                if Some(region_id) == owner || region_id == tree.root {
                    break;
                }
                let current = tree
                    .region_mut(region_id)
                    .ok_or(RegionInvariantError::UnknownRegion(region_id))?;
                ancestor = current.parent;
                current.blocks.retain(|block| !removed.contains(block));
            }

            for child in promote {
                Self::unlink(tree, candidate, child)?;
                Self::link(tree, parent, child)?;
            }
        }
        Ok(())
    }

    fn place_owner(&self, tree: &mut RegionTree) -> Result<(), RegionInvariantError> {
        let enter_owner = tree.owner(self.enter)?;
        let lexical_parent = tree
            .parent_chain(self.owner)?
            .into_iter()
            .find(|region| {
                tree.region(*region)
                    .is_some_and(|region| region.blocks.contains(&self.enter))
            })
            .unwrap_or(tree.common_ancestor(self.owner, enter_owner)?);
        let parent = tree
            .region(self.owner)
            .and_then(|region| region.parent)
            .ok_or(RegionInvariantError::MissingRegionParent {
                region: self.owner,
                parent: tree.root,
            })?;
        if tree
            .region(parent)
            .is_some_and(|region| self.blocks.is_subset(&region.blocks))
        {
            return Ok(());
        }
        if self.owner == lexical_parent || parent == lexical_parent {
            return Ok(());
        }

        let chain = tree.parent_chain(self.owner)?;
        let Some(boundary) = chain.iter().position(|region| *region == lexical_parent) else {
            return Err(RegionInvariantError::UncontainedRegion {
                entry: self.entry,
                blocks: self.blocks.clone(),
            });
        };
        let enclosed =
            chain
                .get(1..boundary)
                .ok_or_else(|| RegionInvariantError::UncontainedRegion {
                    entry: self.entry,
                    blocks: self.blocks.clone(),
                })?;
        if enclosed.is_empty() {
            return Ok(());
        }
        let disjoint_ancestors = enclosed
            .iter()
            .copied()
            .filter(|region| {
                tree.region(*region)
                    .is_some_and(|region| region.blocks.is_disjoint(&self.blocks))
            })
            .collect::<Vec<_>>();
        if disjoint_ancestors.len() == enclosed.len() {
            // DEX exception ranges omit non-throwing instructions. When the
            // synchronization region is already nested under the right
            // control domains, an enter/body component can consequently be
            // disjoint from every intervening ancestor. Preserve that nesting
            // and close the ancestors over the recovered lexical scope.
            for region in disjoint_ancestors {
                let body = &mut tree
                    .region_mut(region)
                    .ok_or(RegionInvariantError::UnknownRegion(region))?
                    .blocks;
                body.insert(self.enter);
                body.extend(self.blocks.iter().copied());
            }
            return Ok(());
        }
        for region in enclosed {
            let body = &tree
                .region(*region)
                .ok_or(RegionInvariantError::UnknownRegion(*region))?
                .blocks;
            if !body.is_subset(&self.blocks) {
                return Err(RegionInvariantError::RegionOverlap {
                    left: self.owner,
                    right: *region,
                    intersection: self.blocks.intersection(body).copied().collect(),
                    left_only: self.blocks.difference(body).copied().collect(),
                    right_only: body.difference(&self.blocks).copied().collect(),
                });
            }
        }

        let outer = *enclosed
            .last()
            .ok_or(RegionInvariantError::UnknownRegion(self.owner))?;
        let children = tree
            .region(self.owner)
            .ok_or(RegionInvariantError::UnknownRegion(self.owner))?
            .children
            .clone();

        Self::unlink(tree, parent, self.owner)?;
        Self::unlink(tree, lexical_parent, outer)?;
        Self::link(tree, lexical_parent, self.owner)?;
        Self::link(tree, self.owner, outer)?;

        for child in children {
            if self.release_handlers.contains(&child) || tree.region(child).is_none() {
                continue;
            }
            let child_blocks = tree
                .region(child)
                .ok_or(RegionInvariantError::UnknownRegion(child))?
                .blocks
                .clone();
            let target = enclosed.iter().copied().find(|region| {
                tree.region(*region)
                    .is_some_and(|region| child_blocks.is_subset(&region.blocks))
            });
            let Some(target) = target else {
                continue;
            };
            Self::unlink(tree, self.owner, child)?;
            Self::link(tree, target, child)?;
        }
        Ok(())
    }

    fn is_release_entry(
        cfg: &CFG,
        tree: &RegionTree,
        region: RegionId,
        entries: &BTreeSet<BlockId>,
    ) -> bool {
        tree.region(region).is_some_and(|region| {
            let semantic_entry = region.entry.or_else(|| match &region.kind {
                RegionKind::Catch(catch) | RegionKind::Cleanup(catch) => catch.continuation,
                _ => None,
            });
            matches!(
                &region.kind,
                RegionKind::Catch(_) | RegionKind::Finally | RegionKind::Cleanup(_)
            ) && semantic_entry.is_some_and(|target| {
                entries.iter().copied().any(|entry| {
                    entry == target || Self::transparent_release_adapter(cfg, entry, target)
                })
            })
        })
    }

    /// Exception analysis can retain a `move-exception` adapter as the
    /// release entry while the lexical handler starts at its successor.
    /// Relate those representations only across a deterministic path of SSA
    /// bookkeeping with no exceptional side exit.
    fn transparent_release_adapter(cfg: &CFG, entry: BlockId, target: BlockId) -> bool {
        let mut current = entry;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            if current == target {
                return true;
            }
            let Some(block) = cfg.block(current) else {
                return false;
            };
            if block
                .insns
                .iter()
                .any(|instruction| !InstructionEffects::is_ssa_bookkeeping(instruction))
                || cfg
                    .successors_with_kind(current)
                    .iter()
                    .any(|(_, kind)| kind.is_exception())
            {
                return false;
            }
            let successors = cfg.normal_successors(current).collect::<Vec<_>>();
            let [next] = successors.as_slice() else {
                return false;
            };
            current = *next;
        }
        false
    }

    fn mark_release_handlers(&self, tree: &mut RegionTree) -> Result<(), RegionInvariantError> {
        for handler in &self.release_handlers {
            let kind = &mut tree
                .region_mut(*handler)
                .ok_or(RegionInvariantError::UnknownRegion(*handler))?
                .kind;
            if let RegionKind::Catch(catch) = kind.clone() {
                *kind = RegionKind::Cleanup(catch);
            }
        }
        Ok(())
    }

    fn remove_duplicate_handlers(
        &self,
        tree: &mut RegionTree,
    ) -> Result<(BTreeSet<RegionId>, BTreeSet<RegionId>), RegionInvariantError> {
        let mut wrappers = BTreeSet::new();
        let mut removed = BTreeSet::new();
        for duplicate in &self.duplicate_handlers {
            let parent = tree
                .region(*duplicate)
                .and_then(|region| region.parent)
                .ok_or(RegionInvariantError::MissingRegionParent {
                    region: *duplicate,
                    parent: self.owner,
                })?;
            Self::unlink(tree, parent, *duplicate)?;
            tree.regions.remove(duplicate);
            wrappers.insert(parent);
            removed.insert(*duplicate);
        }
        Ok((wrappers, removed))
    }

    fn remove_empty_wrappers(
        &self,
        tree: &mut RegionTree,
        wrappers: BTreeSet<RegionId>,
    ) -> Result<BTreeSet<RegionId>, RegionInvariantError> {
        let mut wrappers = wrappers
            .into_iter()
            .filter(|region| *region != self.owner)
            .map(|region| tree.parent_chain(region).map(|chain| (chain.len(), region)))
            .collect::<Result<Vec<_>, _>>()?;
        wrappers.sort_by_key(|(depth, _)| std::cmp::Reverse(*depth));
        let mut removed = BTreeSet::new();
        for (_, wrapper) in wrappers {
            if !Self::is_empty_try_wrapper(tree, wrapper) {
                continue;
            }
            Self::promote_children(tree, wrapper)?;
            removed.insert(wrapper);
        }
        Ok(removed)
    }

    fn reparent_contained_regions(
        &self,
        tree: &mut RegionTree,
    ) -> Result<(), RegionInvariantError> {
        let owner_ancestors = tree
            .parent_chain(self.owner)?
            .into_iter()
            .skip(1)
            .collect::<BTreeSet<_>>();
        let contained = tree
            .regions
            .values()
            .filter(|region| region.id != tree.root && region.id != self.owner)
            // An enclosing try can cover exactly the synchronized body while
            // providing source catches outside the monitor. It contains the
            // same blocks, but moving it below its own synchronized child
            // creates a parent cycle and inverts the release-before-catch
            // semantics.
            .filter(|region| !owner_ancestors.contains(&region.id))
            .filter(|region| !region.blocks.is_empty() && region.blocks.is_subset(&self.blocks))
            .map(|region| region.id)
            .collect::<BTreeSet<_>>();
        let roots = contained
            .iter()
            .copied()
            .filter(|region| {
                let parent = tree.region(*region).and_then(|region| region.parent);
                parent != Some(self.owner)
                    && parent.is_some_and(|parent| !contained.contains(&parent))
            })
            .collect::<Vec<_>>();
        for region in roots {
            let parent = tree.region(region).and_then(|region| region.parent).ok_or(
                RegionInvariantError::MissingRegionParent {
                    region,
                    parent: tree.root,
                },
            )?;
            Self::unlink(tree, parent, region)?;
            tree.region_mut(region)
                .ok_or(RegionInvariantError::UnknownRegion(region))?
                .parent = Some(self.owner);
            tree.region_mut(self.owner)
                .ok_or(RegionInvariantError::UnknownRegion(self.owner))?
                .children
                .push(region);
        }
        Ok(())
    }

    fn is_empty_try_wrapper(tree: &RegionTree, wrapper: RegionId) -> bool {
        tree.region(wrapper).is_some_and(|region| {
            matches!(&region.kind, RegionKind::Try)
                && !region.children.iter().any(|child| {
                    tree.region(*child).is_some_and(|child| {
                        matches!(
                            &child.kind,
                            RegionKind::Catch(_) | RegionKind::Finally | RegionKind::Cleanup(_)
                        )
                    })
                })
        })
    }

    fn promote_children(
        tree: &mut RegionTree,
        wrapper: RegionId,
    ) -> Result<(), RegionInvariantError> {
        tree.remove_region_promoting_children(wrapper)
    }

    fn unlink(
        tree: &mut RegionTree,
        parent: RegionId,
        child: RegionId,
    ) -> Result<(), RegionInvariantError> {
        tree.region_mut(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?
            .children
            .retain(|candidate| *candidate != child);
        Ok(())
    }

    fn link(
        tree: &mut RegionTree,
        parent: RegionId,
        child: RegionId,
    ) -> Result<(), RegionInvariantError> {
        tree.region_mut(child)
            .ok_or(RegionInvariantError::UnknownRegion(child))?
            .parent = Some(parent);
        let children = &mut tree
            .region_mut(parent)
            .ok_or(RegionInvariantError::UnknownRegion(parent))?
            .children;
        children.push(child);
        children.sort_unstable();
        children.dedup();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::{CatchRegion, LoopRegion};
    use super::*;
    use crate::ir::{ArgType, Block, EdgeKind, InsnNode, RegisterArg};

    fn blocks(ids: impl IntoIterator<Item = u32>) -> BTreeSet<BlockId> {
        ids.into_iter().map(BlockId::new).collect()
    }

    fn add_region(
        tree: &mut RegionTree,
        parent: RegionId,
        kind: RegionKind,
        entry: u32,
        body: impl IntoIterator<Item = u32>,
    ) -> RegionId {
        let id = tree
            .add_child(parent, kind, Some(BlockId::new(entry)))
            .unwrap();
        tree.region_mut(id).unwrap().blocks = blocks(body);
        id
    }

    #[test]
    fn synchronization_reparenting_preserves_coincident_try_ancestor() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let outer_try = add_region(&mut tree, root, RegionKind::Try, 1, [1, 2]);
        let owner = add_region(&mut tree, outer_try, RegionKind::Try, 1, [1, 2]);
        let contained = add_region(
            &mut tree,
            outer_try,
            RegionKind::Loop(LoopRegion {
                follow: None,
                latches: blocks([2]),
            }),
            2,
            [2],
        );
        let placement = SynchronizationPlacement {
            owner,
            enter: BlockId::new(0),
            lock: InsnArg::Reg(RegisterArg::new(
                0,
                ArgType::object("java/lang/Object"),
            )),
            entry: BlockId::new(1),
            blocks: blocks([1, 2]),
            release_handlers: BTreeSet::new(),
            user_handlers: BTreeSet::new(),
            release_segments: BTreeSet::new(),
            duplicate_handlers: Vec::new(),
            method: false,
        };

        placement.reparent_contained_regions(&mut tree).unwrap();

        assert_eq!(tree.region(outer_try).unwrap().parent, Some(root));
        assert_eq!(tree.region(owner).unwrap().parent, Some(outer_try));
        assert_eq!(tree.region(contained).unwrap().parent, Some(owner));
        assert_eq!(tree.parent_chain(owner).unwrap(), vec![owner, outer_try, root]);
    }

    #[test]
    fn strict_subsets_follow_lexical_nesting() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let loop_region = add_region(
            &mut tree,
            root,
            RegionKind::Loop(LoopRegion {
                follow: None,
                latches: blocks([2]),
            }),
            1,
            [1, 2],
        );
        let try_region = add_region(&mut tree, root, RegionKind::Try, 2, [2]);

        tree.canonicalize_nesting().unwrap();

        assert_eq!(tree.region(try_region).unwrap().parent, Some(loop_region));
    }

    #[test]
    fn handler_encloses_coincident_control_region() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let try_region = add_region(&mut tree, root, RegionKind::Try, 1, [1, 2]);
        let loop_region = add_region(
            &mut tree,
            try_region,
            RegionKind::Loop(LoopRegion {
                follow: None,
                latches: blocks([2]),
            }),
            1,
            [1, 2],
        );
        let cleanup = add_region(
            &mut tree,
            try_region,
            RegionKind::Cleanup(CatchRegion {
                exception_types: vec![crate::ir::ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            1,
            [1, 2],
        );

        tree.canonicalize_nesting().unwrap();

        assert_eq!(tree.region(cleanup).unwrap().parent, Some(try_region));
        assert_eq!(tree.region(loop_region).unwrap().parent, Some(cleanup));
    }

    #[test]
    fn semantic_envelope_is_rotated_outside_coincident_control() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let loop_region = add_region(
            &mut tree,
            root,
            RegionKind::Loop(LoopRegion {
                follow: None,
                latches: blocks([2]),
            }),
            1,
            [1, 2],
        );
        let try_region = add_region(&mut tree, loop_region, RegionKind::Try, 1, [1, 2]);

        tree.canonicalize_nesting().unwrap();

        assert_eq!(tree.region(try_region).unwrap().parent, Some(root));
        assert_eq!(tree.region(loop_region).unwrap().parent, Some(try_region));
    }

    #[test]
    fn protected_range_remains_inside_coincident_handler_domain() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let handler = add_region(&mut tree, root, RegionKind::Finally, 1, [1]);
        let protected = match tree
            .insert_laminar_region(RegionKind::Try, BlockId::new(1), blocks([1]))
            .unwrap()
        {
            RegionPlacement::Inserted(region) => region,
            RegionPlacement::Residual => panic!("coincident protected range was not inserted"),
        };

        tree.canonicalize_nesting().unwrap();

        assert_eq!(tree.region(protected).unwrap().parent, Some(handler));
    }

    #[test]
    fn synchronization_strips_nested_try_handler_continuations_outside_monitor() {
        let mut cfg = CFG::new("synchronized_try_external_continuation");
        for id in 0..=6 {
            cfg.add_block(Block::new(id));
        }
        for (source, target) in [(0, 1), (1, 2), (2, 3), (3, 4)] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), EdgeKind::Normal);
        }
        for source in 1..=3 {
            cfg.add_edge(BlockId::new(source), BlockId::new(5), EdgeKind::Exception);
        }
        cfg.add_edge(BlockId::new(5), BlockId::new(6), EdgeKind::Normal);

        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        let owner = add_region(&mut tree, root, RegionKind::Try, 1, [1, 2, 3]);
        let nested = add_region(&mut tree, owner, RegionKind::Try, 2, [2, 3, 4]);
        let catch = add_region(
            &mut tree,
            nested,
            RegionKind::Catch(CatchRegion {
                exception_types: vec![ArgType::object("java/lang/Exception")],
                exception_value: None,
                continuation: Some(BlockId::new(4)),
            }),
            3,
            [3],
        );
        let release = add_region(
            &mut tree,
            root,
            RegionKind::Cleanup(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            5,
            [5, 6],
        );
        let lock = InsnArg::Reg(RegisterArg::new(0, ArgType::object("java/lang/Object")));

        tree.synchronize(
            &cfg,
            &BTreeMap::from([(owner, vec![catch, release])]),
            owner,
            &[catch, release],
            lock,
            BlockId::new(0),
            BlockId::new(1),
            &blocks([1, 2, 3]),
            &blocks([5]),
            &BTreeSet::new(),
            false,
        )
        .unwrap();

        assert!(matches!(
            tree.region(owner).map(|region| &region.kind),
            Some(RegionKind::Synchronized(_))
        ));
        assert_eq!(tree.region(nested).unwrap().blocks, blocks([2, 3]));
        assert!(!tree.region(nested).unwrap().blocks.contains(&BlockId::new(4)));
    }

    #[test]
    fn standalone_synchronization_partitions_a_handler_return_continuation() {
        let mut cfg = CFG::new("synchronized_handler_return");
        for id in 0..=8 {
            cfg.add_block(Block::new(id));
        }
        for (source, target) in [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 7), (6, 8)] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), EdgeKind::Normal);
        }
        for source in 1..=4 {
            cfg.add_edge(BlockId::new(source), BlockId::new(6), EdgeKind::Exception);
        }

        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        let handler = add_region(
            &mut tree,
            root,
            RegionKind::Catch(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            6,
            [6, 8],
        );
        let scope = blocks([1, 2, 3, 4, 5, 6]);
        let lock = InsnArg::Reg(RegisterArg::new(0, ArgType::object("java/lang/Object")));

        tree.synchronize(
            &cfg,
            &BTreeMap::new(),
            root,
            &[],
            lock,
            BlockId::new(0),
            BlockId::new(1),
            &scope,
            &BTreeSet::new(),
            &BTreeSet::new(),
            true,
        )
        .unwrap();

        let handler_region = tree.region(handler).unwrap();
        assert_eq!(handler_region.blocks, blocks([6]));
        let RegionKind::Catch(catch) = &handler_region.kind else {
            panic!("handler changed kind");
        };
        assert_eq!(catch.continuation, Some(BlockId::new(8)));
        let synchronization = handler_region.parent.unwrap();
        assert!(matches!(
            tree.region(synchronization).map(|region| &region.kind),
            Some(RegionKind::Synchronized(_))
        ));
        assert_eq!(tree.region(synchronization).unwrap().blocks, scope);
    }

    #[test]
    fn synchronization_closes_ancestor_try_missing_split_entry() {
        let mut cfg = CFG::new("declared_synchronized_split_entry");
        for id in 0..=5 {
            cfg.add_block(Block::new(id));
        }
        for (source, target) in [(0, 1), (1, 2), (2, 3)] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), EdgeKind::Normal);
        }
        for source in 1..=2 {
            cfg.add_edge(BlockId::new(source), BlockId::new(4), EdgeKind::Exception);
        }
        cfg.add_edge(BlockId::new(4), BlockId::new(5), EdgeKind::Normal);

        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        // Outer try owns the original body but not the post-enter split block.
        let outer = add_region(&mut tree, root, RegionKind::Try, 2, [2, 3, 4]);
        let owner = add_region(&mut tree, outer, RegionKind::Try, 2, [2, 3]);
        let release = add_region(
            &mut tree,
            root,
            RegionKind::Cleanup(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            4,
            [4, 5],
        );
        let lock = InsnArg::Reg(RegisterArg::new(0, ArgType::object("java/lang/Object")));

        tree.synchronize(
            &cfg,
            &BTreeMap::from([(owner, vec![release])]),
            owner,
            &[release],
            lock,
            BlockId::new(0),
            BlockId::new(1),
            &blocks([1, 2, 3]),
            &blocks([4]),
            &BTreeSet::new(),
            false,
        )
        .unwrap();

        assert!(matches!(
            tree.region(owner).map(|region| &region.kind),
            Some(RegionKind::Synchronized(_))
        ));
        assert!(tree
            .region(outer)
            .unwrap()
            .blocks
            .is_superset(&blocks([1, 2, 3])));
        assert_eq!(
            tree.region(outer).and_then(|region| region.entry),
            Some(BlockId::new(1)),
            "enclosing try must enter at the synchronized body entry after split"
        );
    }

    #[test]
    fn declared_synchronization_owns_split_return_tails() {
        let mut cfg = CFG::new("declared_synchronized_return_tails");
        for id in 0..=7 {
            cfg.add_block(Block::new(id));
        }

        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        let release = add_region(
            &mut tree,
            root,
            RegionKind::Cleanup(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            4,
            [4, 5],
        );
        let user_handler = add_region(
            &mut tree,
            root,
            RegionKind::Catch(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            6,
            [6, 7],
        );
        let lock = InsnArg::Reg(RegisterArg::new(0, ArgType::object("java/lang/Object")));

        let placement = SynchronizationPlacement::analyze(
            &tree,
            &cfg,
            root,
            &[release, user_handler],
            lock,
            BlockId::new(0),
            BlockId::new(1),
            &blocks([1, 2, 4, 6]),
            &blocks([4]),
            &BTreeSet::new(),
            true,
        )
        .unwrap();

        assert_eq!(placement.blocks, blocks([1, 2, 3, 6, 7]));
    }

    #[test]
    fn synchronization_excludes_release_blocks_reintroduced_by_control_closure() {
        let mut cfg = CFG::new("synchronized_release_retry_loop");
        for id in 0..=4 {
            cfg.add_block(Block::new(id));
        }

        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        let owner = add_region(&mut tree, root, RegionKind::Try, 1, [1, 2, 3, 4]);
        let release = add_region(
            &mut tree,
            root,
            RegionKind::Cleanup(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            4,
            [4],
        );
        let retry_loop = add_region(
            &mut tree,
            root,
            RegionKind::Loop(LoopRegion {
                follow: None,
                latches: blocks([4]),
            }),
            3,
            [3, 4],
        );
        let lock = InsnArg::Reg(RegisterArg::new(0, ArgType::object("java/lang/Object")));

        tree.synchronize(
            &cfg,
            &BTreeMap::new(),
            owner,
            &[release],
            lock,
            BlockId::new(0),
            BlockId::new(1),
            &blocks([1, 2, 3, 4]),
            &blocks([4]),
            &BTreeSet::from([retry_loop]),
            false,
        )
        .unwrap();

        assert_eq!(tree.region(owner).unwrap().blocks, blocks([1, 2, 3]));
        assert_eq!(tree.region(release).unwrap().blocks, blocks([4]));
        tree.verify(&cfg).unwrap();
    }

    #[test]
    fn standalone_synchronization_rejects_ambiguous_handler_continuations() {
        let mut cfg = CFG::new("ambiguous_synchronized_handler");
        for id in 0..=9 {
            cfg.add_block(Block::new(id));
        }
        for (source, target) in [(0, 1), (1, 5), (5, 7), (6, 8), (6, 9)] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), EdgeKind::Normal);
        }
        cfg.add_edge(BlockId::new(1), BlockId::new(6), EdgeKind::Exception);

        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        tree.cover_method(&cfg).unwrap();
        let root = tree.root();
        add_region(
            &mut tree,
            root,
            RegionKind::Catch(CatchRegion {
                exception_types: vec![ArgType::throwable()],
                exception_value: None,
                continuation: None,
            }),
            6,
            [6, 8, 9],
        );
        let scope = blocks([1, 5, 6]);
        let lock = InsnArg::Reg(RegisterArg::new(0, ArgType::object("java/lang/Object")));

        let result = tree.synchronize(
            &cfg,
            &BTreeMap::new(),
            root,
            &[],
            lock,
            BlockId::new(0),
            BlockId::new(1),
            &scope,
            &BTreeSet::new(),
            &BTreeSet::new(),
            true,
        );

        assert!(matches!(
            result,
            Err(RegionInvariantError::SynchronizationRegionOverlap { .. })
        ));
    }

    #[test]
    fn release_handler_matches_a_transparent_move_exception_adapter() {
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let handler = add_region(&mut tree, root, RegionKind::Finally, 1, [0, 1, 2, 3, 4]);

        let mut adapter = Block::new(0);
        adapter.push(InsnNode::move_exception(RegisterArg::new(
            0,
            ArgType::throwable(),
        )));
        let target = Block::new(1);
        let exceptional_target = Block::new(2);
        let mut observable = Block::new(3);
        observable.push(InsnNode::monitor_exit(InsnArg::Reg(RegisterArg::new(
            1,
            ArgType::object("java/lang/Object"),
        ))));
        let mut branching_adapter = Block::new(4);
        branching_adapter.push(InsnNode::move_exception(RegisterArg::new(
            2,
            ArgType::throwable(),
        )));

        let mut cfg = CFG::new("release_handler_adapter");
        cfg.add_block(adapter);
        cfg.add_block(target);
        cfg.add_block(exceptional_target);
        cfg.add_block(observable);
        cfg.add_block(branching_adapter);
        cfg.add_edge(BlockId::new(0), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(3), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(4), BlockId::new(1), EdgeKind::Normal);
        cfg.add_edge(BlockId::new(4), BlockId::new(2), EdgeKind::Exception);

        assert!(SynchronizationPlacement::is_release_entry(
            &cfg,
            &tree,
            handler,
            &blocks([0]),
        ));
        assert!(!SynchronizationPlacement::is_release_entry(
            &cfg,
            &tree,
            handler,
            &blocks([3]),
        ));
        assert!(!SynchronizationPlacement::is_release_entry(
            &cfg,
            &tree,
            handler,
            &blocks([4]),
        ));
    }
}
