use std::collections::BTreeSet;

use crate::ir::{BlockId, CFG};

/// A maximal canonical-entry portion of a semantic domain contained by one
/// lexical scope. Physical handler adapters may converge on the canonical
/// entry; the remainder is reached through exactly one normal-flow
/// continuation and cannot re-enter the contained portion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexicalBoundary {
    pub blocks: BTreeSet<BlockId>,
    pub continuation: BlockId,
}

/// Partitions a semantic domain at a lexical ownership boundary.
///
/// DEX protection intervals and monitor ranges may end in the middle of a
/// source-level handler. A region tree remains laminar by owning the maximal
/// entry component on the current side of the boundary and representing the
/// unique remaining path as a continuation.
pub struct LexicalBoundaryAnalysis<'cfg> {
    cfg: &'cfg CFG,
}

impl<'cfg> LexicalBoundaryAnalysis<'cfg> {
    pub fn new(cfg: &'cfg CFG) -> Self {
        Self { cfg }
    }

    pub fn partition(
        &self,
        entry: BlockId,
        domain: &BTreeSet<BlockId>,
        scope: &BTreeSet<BlockId>,
    ) -> Option<LexicalBoundary> {
        if !domain.contains(&entry) || !scope.contains(&entry) {
            return None;
        }

        let inside = domain.intersection(scope).copied().collect::<BTreeSet<_>>();
        let outside = domain.difference(scope).copied().collect::<BTreeSet<_>>();
        if outside.is_empty() {
            return None;
        }
        if !self.is_canonical_entry_domain(entry, &inside) {
            return None;
        }

        let exits = inside
            .iter()
            .flat_map(|block| self.cfg.normal_successors(*block))
            .filter(|target| outside.contains(target))
            .collect::<BTreeSet<_>>();
        let continuation = exits.iter().copied().next()?;
        if exits.len() != 1 || self.reachable(continuation, &outside) != outside {
            return None;
        }

        let reenters = outside
            .iter()
            .flat_map(|block| self.cfg.normal_successors(*block))
            .any(|target| inside.contains(&target));
        if reenters {
            return None;
        }

        Some(LexicalBoundary {
            blocks: inside,
            continuation,
        })
    }

    fn is_canonical_entry_domain(&self, entry: BlockId, allowed: &BTreeSet<BlockId>) -> bool {
        let mut covered = self.semantic_reachable(entry, allowed);
        covered.extend(self.semantic_reverse_reachable(entry, allowed));
        covered == *allowed
    }

    /// Reachability within one semantic domain includes exceptional transfers.
    ///
    /// A catch or cleanup body can contain an inner throwing operation whose
    /// handler rejoins the ordinary path. Excluding that edge makes the inner
    /// handler appear to be a disconnected lexical owner even though it is
    /// wholly contained by the domain.
    fn semantic_reachable(&self, entry: BlockId, allowed: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !allowed.contains(&block) || !reachable.insert(block) {
                continue;
            }
            pending.extend(self.cfg.successors(block));
        }
        reachable
    }

    fn semantic_reverse_reachable(
        &self,
        entry: BlockId,
        allowed: &BTreeSet<BlockId>,
    ) -> BTreeSet<BlockId> {
        let predecessors = self.cfg.predecessor_snapshot();
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !allowed.contains(&block) || !reachable.insert(block) {
                continue;
            }
            pending.extend(predecessors.get(&block).into_iter().flatten().copied());
        }
        reachable
    }

    fn reachable(&self, entry: BlockId, allowed: &BTreeSet<BlockId>) -> BTreeSet<BlockId> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !allowed.contains(&block) || !reachable.insert(block) {
                continue;
            }
            pending.extend(self.cfg.normal_successors(block));
        }
        reachable
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, EdgeKind};

    #[test]
    fn partitions_a_single_entry_domain_at_its_unique_continuation() {
        let mut cfg = CFG::new("lexical_boundary");
        for id in 0..=3 {
            cfg.add_block(Block::new(id));
        }
        for (source, target) in [(0, 1), (1, 2), (2, 3)] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), EdgeKind::Normal);
        }

        let domain = (0..=3).map(BlockId::new).collect();
        let scope = [BlockId::new(0), BlockId::new(1)].into_iter().collect();
        let boundary = LexicalBoundaryAnalysis::new(&cfg)
            .partition(BlockId::new(0), &domain, &scope)
            .unwrap();

        assert_eq!(
            boundary.blocks,
            [BlockId::new(0), BlockId::new(1)].into_iter().collect()
        );
        assert_eq!(boundary.continuation, BlockId::new(2));
    }

    #[test]
    fn rejects_a_domain_with_multiple_boundary_entries() {
        let mut cfg = CFG::new("crossing_boundary");
        for id in 0..=3 {
            cfg.add_block(Block::new(id));
        }
        for (source, target) in [(0, 1), (1, 2), (1, 3)] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), EdgeKind::Normal);
        }

        let domain = (0..=3).map(BlockId::new).collect();
        let scope = [BlockId::new(0), BlockId::new(1)].into_iter().collect();
        assert!(LexicalBoundaryAnalysis::new(&cfg)
            .partition(BlockId::new(0), &domain, &scope)
            .is_none());
    }

    #[test]
    fn accepts_handler_adapters_converging_on_the_canonical_entry() {
        let mut cfg = CFG::new("handler_adapter_boundary");
        for id in 0..=3 {
            cfg.add_block(Block::new(id));
        }
        for (source, target) in [(0, 1), (1, 2), (2, 3)] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), EdgeKind::Normal);
        }

        let domain = (0..=3).map(BlockId::new).collect();
        let scope = (0..=2).map(BlockId::new).collect();
        let boundary = LexicalBoundaryAnalysis::new(&cfg)
            .partition(BlockId::new(1), &domain, &scope)
            .unwrap();

        assert_eq!(boundary.blocks, scope);
        assert_eq!(boundary.continuation, BlockId::new(3));
    }

    #[test]
    fn accepts_an_internal_exception_handler_that_rejoins_the_domain() {
        let mut cfg = CFG::new("nested_handler_boundary");
        for id in 0..=5 {
            cfg.add_block(Block::new(id));
        }
        for (source, target, kind) in [
            (0, 1, EdgeKind::Normal),
            (1, 2, EdgeKind::Normal),
            (1, 3, EdgeKind::Exception),
            (3, 2, EdgeKind::Normal),
            (2, 4, EdgeKind::Normal),
            (4, 5, EdgeKind::Normal),
        ] {
            cfg.add_edge(BlockId::new(source), BlockId::new(target), kind);
        }

        let domain = (0..=5).map(BlockId::new).collect();
        let scope = (0..=4).map(BlockId::new).collect();
        let boundary = LexicalBoundaryAnalysis::new(&cfg)
            .partition(BlockId::new(0), &domain, &scope)
            .unwrap();

        assert_eq!(boundary.blocks, scope);
        assert_eq!(boundary.continuation, BlockId::new(5));
    }
}
