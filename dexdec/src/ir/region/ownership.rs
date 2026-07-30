//! Lexical ownership closure for non-throwing control-flow components.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{analysis::ControlFlowFacts, BlockId, CFG};

use super::{RegionId, RegionInvariantError, RegionKind, RegionTree};

/// Computes the region-convex closure of already owned lexical blocks.
///
/// Exception tables only cover instruction ranges that need handlers. A
/// non-throwing branch or edge split between protected blocks is nevertheless
/// part of the same lexical region. Leaving such components in an ancestor
/// creates artificial region entries and cross-region loops.
pub(super) struct LexicalOwnershipClosure;

impl LexicalOwnershipClosure {
    pub(super) fn apply(
        cfg: &CFG,
        facts: &ControlFlowFacts,
        handlers: &BTreeMap<RegionId, Vec<RegionId>>,
        tree: &mut RegionTree,
    ) -> Result<(), RegionInvariantError> {
        let predecessors = cfg.normal_predecessor_snapshot();
        loop {
            let mut candidates = BTreeMap::<RegionId, BTreeSet<BlockId>>::new();
            for block in cfg
                .block_ids()
                .into_iter()
                .filter(|block| Self::is_non_throwing(cfg, *block))
            {
                candidates
                    .entry(tree.owner(block)?)
                    .or_default()
                    .insert(block);
            }
            let mut changed = false;
            for (current_owner, blocks) in candidates {
                for component in Self::components(cfg, &predecessors, &blocks) {
                    let incoming = component.iter().flat_map(|block| {
                        predecessors
                            .get(block)
                            .into_iter()
                            .flatten()
                            .copied()
                            .filter(|predecessor| !component.contains(predecessor))
                    });
                    let outgoing = component.iter().flat_map(|block| {
                        cfg.normal_successors(*block)
                            .filter(|successor| !component.contains(successor))
                    });
                    let incoming = Self::owners(tree, incoming)?;
                    let outgoing = Self::owners(tree, outgoing)?;
                    if incoming.is_empty() || outgoing.is_empty() {
                        continue;
                    }
                    let boundaries = incoming.union(&outgoing).copied().collect::<BTreeSet<_>>();
                    let Some(owner) = Self::common_owner(tree, &boundaries)? else {
                        continue;
                    };
                    if owner == current_owner || !tree.is_ancestor(current_owner, owner)? {
                        continue;
                    }
                    if !Self::accepts(tree, facts, owner, &component)? {
                        continue;
                    }
                    for block in component {
                        tree.add_block(owner, block)?;
                    }
                    changed = true;
                }
            }
            if changed {
                continue;
            }
            if Self::place_region(cfg, facts, handlers, tree)? {
                tree.canonicalize_nesting()?;
                continue;
            }
            return Ok(());
        }
    }

    fn place_region(
        cfg: &CFG,
        facts: &ControlFlowFacts,
        handlers: &BTreeMap<RegionId, Vec<RegionId>>,
        tree: &mut RegionTree,
    ) -> Result<bool, RegionInvariantError> {
        let candidates = tree
            .regions()
            .filter(|region| matches!(&region.kind, RegionKind::Try))
            .map(|region| region.id)
            .collect::<Vec<_>>();
        let predecessors = cfg.normal_predecessor_snapshot();
        for candidate in candidates {
            let region = tree
                .region(candidate)
                .cloned()
                .ok_or(RegionInvariantError::UnknownRegion(candidate))?;
            let current = region
                .parent
                .ok_or(RegionInvariantError::MissingRegionParent {
                    region: candidate,
                    parent: tree.root(),
                })?;
            let associated = handlers
                .get(&candidate)
                .into_iter()
                .flatten()
                .copied()
                .collect::<BTreeSet<_>>();
            let incoming = region.blocks.iter().flat_map(|block| {
                predecessors
                    .get(block)
                    .into_iter()
                    .flatten()
                    .copied()
                    .filter(|predecessor| !region.blocks.contains(predecessor))
            });
            let outgoing = region
                .blocks
                .iter()
                .flat_map(|block| cfg.normal_successors(*block))
                .filter(|successor| !region.blocks.contains(successor))
                .map(|successor| Self::continuation(cfg, successor));
            let handler_outgoing = associated.iter().flat_map(|handler| {
                let blocks = tree
                    .region(*handler)
                    .map(|region| region.blocks.clone())
                    .unwrap_or_default();
                blocks
                    .iter()
                    .flat_map(|block| cfg.normal_successors(*block))
                    .filter(|successor| !blocks.contains(successor))
                    .map(|successor| Self::continuation(cfg, successor))
                    .collect::<Vec<_>>()
            });
            let incoming = Self::owners(tree, incoming)?
                .into_iter()
                .filter(|owner| *owner != candidate && !associated.contains(owner))
                .collect::<BTreeSet<_>>();
            let outgoing = Self::owners(tree, outgoing.chain(handler_outgoing))?
                .into_iter()
                .filter(|owner| *owner != candidate && !associated.contains(owner))
                .collect::<BTreeSet<_>>();
            if incoming.is_empty() || outgoing.is_empty() {
                continue;
            }
            let boundaries = incoming.union(&outgoing).copied().collect::<BTreeSet<_>>();
            let Some(owner) = Self::common_owner(tree, &boundaries)? else {
                continue;
            };
            if owner == current
                || !tree.is_ancestor(current, owner)?
                || tree.is_ancestor(candidate, owner)?
            {
                continue;
            }
            let mut enclosed_handlers = BTreeSet::new();
            for handler in &associated {
                if tree.is_ancestor(owner, *handler)? {
                    enclosed_handlers.insert(*handler);
                }
            }
            for handler in &enclosed_handlers {
                Self::claim_handler_body(cfg, tree, *handler, owner)?;
            }
            let additions = std::iter::once(candidate)
                .chain(enclosed_handlers.iter().copied())
                .flat_map(|region| {
                    tree.region(region)
                        .into_iter()
                        .flat_map(|region| region.blocks.iter().copied())
                })
                .collect::<BTreeSet<_>>();
            if !Self::accepts(tree, facts, owner, &additions)? {
                continue;
            }
            for block in additions {
                tree.add_block(owner, block)?;
            }
            return Ok(true);
        }
        Ok(false)
    }

    fn accepts(
        tree: &RegionTree,
        facts: &ControlFlowFacts,
        owner: RegionId,
        additions: &BTreeSet<BlockId>,
    ) -> Result<bool, RegionInvariantError> {
        let region = tree
            .region(owner)
            .ok_or(RegionInvariantError::UnknownRegion(owner))?;
        let Some(entry) = region.entry else {
            return Ok(matches!(&region.kind, RegionKind::Method));
        };
        Ok(additions
            .iter()
            .all(|block| facts.semantic_dominators().dominates(entry, *block)))
    }

    fn claim_handler_body(
        cfg: &CFG,
        tree: &mut RegionTree,
        handler: RegionId,
        owner: RegionId,
    ) -> Result<(), RegionInvariantError> {
        let predecessors = cfg.normal_predecessor_snapshot();
        loop {
            let scope = tree
                .region(handler)
                .ok_or(RegionInvariantError::UnknownRegion(handler))?
                .blocks
                .clone();
            if scope.is_empty() {
                return Ok(());
            }
            let candidates = scope
                .iter()
                .copied()
                .flat_map(|block| cfg.normal_successors(block))
                .filter(|block| !scope.contains(block))
                .collect::<BTreeSet<_>>();
            let mut additions = BTreeSet::new();
            for block in candidates {
                let private = predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .all(|predecessor| scope.contains(predecessor));
                if private && tree.owner(block)? == owner {
                    additions.insert(block);
                }
            }
            if additions.is_empty() {
                return Ok(());
            }
            for block in additions {
                tree.add_block(handler, block)?;
            }
        }
    }

    fn continuation(cfg: &CFG, start: BlockId) -> BlockId {
        let mut current = start;
        let mut visited = BTreeSet::new();
        while visited.insert(current) {
            let Some(block) = cfg.block(current) else {
                break;
            };
            if !block.insns.iter().all(|instruction| {
                matches!(
                    instruction.insn_type,
                    crate::ir::InsnType::Nop | crate::ir::InsnType::Phi | crate::ir::InsnType::Goto
                )
            }) {
                break;
            }
            let successors = cfg.normal_successors(current).collect::<Vec<_>>();
            let [successor] = successors.as_slice() else {
                break;
            };
            current = *successor;
        }
        current
    }

    fn is_non_throwing(cfg: &CFG, block: BlockId) -> bool {
        cfg.block(block).is_some_and(|block| {
            block
                .insns
                .iter()
                .all(|instruction| !instruction.can_throw())
                && cfg
                    .successors_with_kind(block.id)
                    .iter()
                    .all(|(_, kind)| !kind.is_exception())
        })
    }

    fn components(
        cfg: &CFG,
        predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
        candidates: &BTreeSet<BlockId>,
    ) -> Vec<BTreeSet<BlockId>> {
        let mut remaining = candidates.clone();
        let mut components = Vec::new();
        while let Some(seed) = remaining.pop_first() {
            let mut component = BTreeSet::new();
            let mut pending = vec![seed];
            while let Some(block) = pending.pop() {
                if !component.insert(block) {
                    continue;
                }
                let adjacent = predecessors
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .copied()
                    .chain(cfg.normal_successors(block));
                for neighbor in adjacent.filter(|neighbor| remaining.remove(neighbor)) {
                    pending.push(neighbor);
                }
            }
            components.push(component);
        }
        components
    }

    fn owners(
        tree: &RegionTree,
        blocks: impl Iterator<Item = BlockId>,
    ) -> Result<BTreeSet<RegionId>, RegionInvariantError> {
        blocks.map(|block| tree.owner(block)).collect()
    }

    fn common_owner(
        tree: &RegionTree,
        owners: &BTreeSet<RegionId>,
    ) -> Result<Option<RegionId>, RegionInvariantError> {
        let mut owners = owners.iter().copied();
        let Some(mut common) = owners.next() else {
            return Ok(None);
        };
        for owner in owners {
            common = tree.common_ancestor(common, owner)?;
        }
        Ok(Some(common))
    }
}
