use std::collections::BTreeSet;

use crate::ir::CFG;

use super::{
    RegionEdge, RegionGraph, RegionInvariantError, RegionTransfer, RegionTransferKind,
    ResolvedRegionExit,
};

pub(super) struct RegionGraphVerifier<'a> {
    graph: &'a RegionGraph,
    cfg: &'a CFG,
}

impl<'a> RegionGraphVerifier<'a> {
    pub(super) fn new(graph: &'a RegionGraph, cfg: &'a CFG) -> Self {
        Self { graph, cfg }
    }

    pub(super) fn verify(&self) -> Result<(), RegionInvariantError> {
        self.graph.tree.verify(self.cfg)?;
        self.verify_leave_index()?;
        self.verify_elisions()?;
        self.verify_ownership()?;
        self.verify_transfers()?;
        self.verify_leaves()
    }

    fn verify_leave_index(&self) -> Result<(), RegionInvariantError> {
        let indexed = self
            .graph
            .leaves
            .iter()
            .filter_map(|resolved| resolved.leave.edge)
            .collect::<BTreeSet<_>>();
        let count = self
            .graph
            .leaves
            .iter()
            .filter(|resolved| resolved.leave.edge.is_some())
            .count();
        let valid = count == indexed.len()
            && indexed.len() == self.graph.edge_leaves.len()
            && indexed.iter().all(|edge| {
                self.graph
                    .leave_for_edge(*edge)
                    .is_some_and(|resolved| resolved.leave.edge == Some(*edge))
            });
        if valid {
            Ok(())
        } else {
            Err(RegionInvariantError::InvalidLeaveIndex)
        }
    }

    fn verify_elisions(&self) -> Result<(), RegionInvariantError> {
        for origin in &self.graph.elisions.candidates {
            let valid = self.cfg.block(origin.block).is_some_and(|block| {
                block
                    .insns
                    .iter()
                    .any(|instruction| instruction.id == origin.instruction)
            });
            if !valid {
                return Err(RegionInvariantError::InvalidElision(origin.clone()));
            }
        }
        Ok(())
    }

    fn verify_ownership(&self) -> Result<(), RegionInvariantError> {
        for block in self.cfg.block_ids() {
            let owner = self
                .graph
                .owner_of(block)
                .ok_or(RegionInvariantError::MissingOwner(block))?;
            let region = self
                .graph
                .tree
                .region(owner)
                .ok_or(RegionInvariantError::UnknownOwner { block, owner })?;
            if !region.owns_block(block) {
                return Err(RegionInvariantError::OwnerDoesNotContainBlock { block, owner });
            }
        }
        Ok(())
    }

    fn verify_transfers(&self) -> Result<(), RegionInvariantError> {
        for transfer in &self.graph.transfers {
            self.verify_transfer(transfer)?;
        }
        Ok(())
    }

    fn verify_transfer(&self, transfer: &RegionTransfer) -> Result<(), RegionInvariantError> {
        let source = self
            .graph
            .owner_of(transfer.source_block)
            .ok_or(RegionInvariantError::MissingOwner(transfer.source_block))?;
        if source != transfer.source_region {
            return Err(RegionInvariantError::TransferSourceMismatch {
                block: transfer.source_block,
                expected: source,
                actual: transfer.source_region,
            });
        }
        let target = self
            .graph
            .owner_of(transfer.target_block)
            .ok_or(RegionInvariantError::MissingOwner(transfer.target_block))?;
        if target != transfer.target_region {
            return Err(RegionInvariantError::TransferTargetMismatch {
                block: transfer.target_block,
                expected: target,
                actual: transfer.target_region,
            });
        }
        let destination = self
            .graph
            .tree
            .enter_destination(transfer.source_region, transfer.destination_block)?;
        if destination != transfer.destination_region {
            return Err(RegionInvariantError::TransferTargetMismatch {
                block: transfer.destination_block,
                expected: destination,
                actual: transfer.destination_region,
            });
        }
        let kind = self.transfer_kind(transfer)?;
        if transfer.kind != kind {
            return Err(RegionInvariantError::TransferKindMismatch {
                block: transfer.source_block,
                expected: kind,
                actual: transfer.kind,
            });
        }
        let leave_target = (kind == RegionTransferKind::Leave)
            .then(|| {
                self.graph
                    .tree
                    .common_ancestor(transfer.source_region, transfer.destination_region)
            })
            .transpose()?;
        if transfer.leave_target != leave_target {
            return Err(RegionInvariantError::LeaveTargetMismatch {
                block: transfer.source_block,
                expected: leave_target,
                actual: transfer.leave_target,
            });
        }
        self.verify_transfer_leave(transfer)
    }

    fn transfer_kind(
        &self,
        transfer: &RegionTransfer,
    ) -> Result<RegionTransferKind, RegionInvariantError> {
        Ok(if transfer.source_region == transfer.destination_region {
            RegionTransferKind::Local
        } else if self
            .graph
            .tree
            .is_ancestor(transfer.source_region, transfer.destination_region)?
        {
            RegionTransferKind::Enter
        } else {
            RegionTransferKind::Leave
        })
    }

    fn verify_transfer_leave(&self, transfer: &RegionTransfer) -> Result<(), RegionInvariantError> {
        if !transfer.requires_leave(self.cfg) {
            return Ok(());
        }
        let target = transfer.exit_destination(self.graph.tree.root());
        let represented = self
            .graph
            .leave_for_edge(RegionEdge {
                source: transfer.source_block,
                target: transfer.target_block,
                kind: transfer.edge_kind,
            })
            .is_some_and(|resolved| {
                resolved.leave.source == transfer.source_region
                    && resolved.leave.target == target
                    && resolved.leave.exit.kind() == transfer.exit_kind
            });
        if represented {
            Ok(())
        } else {
            Err(RegionInvariantError::MissingLeave {
                source_block: transfer.source_block,
                source: transfer.source_region,
                target,
                kind: transfer.exit_kind,
            })
        }
    }

    fn verify_leaves(&self) -> Result<(), RegionInvariantError> {
        for resolved in &self.graph.leaves {
            self.verify_leave(resolved)?;
        }
        Ok(())
    }

    fn verify_leave(&self, resolved: &ResolvedRegionExit) -> Result<(), RegionInvariantError> {
        if let Some(edge) = resolved.leave.edge {
            let transfer = self
                .graph
                .transfers
                .iter()
                .find(|transfer| {
                    transfer.source_block == edge.source
                        && transfer.target_block == edge.target
                        && transfer.edge_kind == edge.kind
                })
                .ok_or(RegionInvariantError::UnknownLeaveEdge(edge))?;
            if !transfer.requires_leave(self.cfg)
                || transfer.source_region != resolved.leave.source
                || transfer.exit_kind != resolved.leave.kind()
            {
                return Err(RegionInvariantError::InvalidLeaveEdge(edge));
            }
        }
        let expected = self
            .graph
            .cleanup_chain(resolved.leave.source, resolved.leave.target)?;
        if resolved.cleanup_regions == expected {
            Ok(())
        } else {
            Err(RegionInvariantError::CleanupChainMismatch {
                source: resolved.leave.source,
                target: resolved.leave.target,
                expected,
                actual: resolved.cleanup_regions.clone(),
            })
        }
    }
}
