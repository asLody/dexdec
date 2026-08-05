//! Region-local graph reduction.
//!
//! Each child region is contracted to one semantic node before its parent is
//! reduced. Exception dispatch edges never enter the ordinary graph reducer.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::semantic::SemanticFactory;
use crate::ir::{
    BlockId, RegionGraph, RegionId, RegionKind, SemanticBlock, SemanticCatch, SemanticFinally,
    SemanticFoldError, SemanticFolder, SemanticLeave, SemanticLeaveKind, SemanticNode,
    SemanticOperation, SemanticVisitor, StructuredRegion, CFG,
};

use super::{
    continuation::ContinuationFacts, graph_structurer::GraphStructurer,
    switch_structurer::SwitchStructurer, StructureError,
};

mod children;
mod cleanup;
mod envelopes;
mod handlers;
mod labels;
mod region_cfg;

use children::{ChildReducer, RegionChildren};
use cleanup::SemanticCleanupResolver;
use envelopes::ExceptionEnvelopeCanonicalizer;
use handlers::HandlerReducer;
use labels::LexicalLabels;
use region_cfg::{RegionAnchors, RegionCfg, RegionCfgBuilder, RegionEntryPorts};

pub struct RegionReducer<'a> {
    cfg: &'a CFG,
    regions: &'a RegionGraph,
    observer: &'a dyn crate::ir::AnalysisObserver,
    anchors: RegionAnchors,
    entry_ports: RegionEntryPorts,
    handler_bodies: BTreeSet<RegionId>,
}

impl<'a> RegionReducer<'a> {
    pub fn new(
        cfg: &'a CFG,
        regions: &'a RegionGraph,
        observer: &'a dyn crate::ir::AnalysisObserver,
    ) -> Result<Self, StructureError> {
        let handlers = HandlerReducer::new(regions);
        let handler_bodies = regions
            .tree()
            .regions()
            .flat_map(|owner| {
                regions
                    .handlers_of(owner.id)
                    .iter()
                    .copied()
                    .map(|handler| handlers.body_region(owner.id, handler))
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        Ok(Self {
            cfg,
            regions,
            observer,
            anchors: RegionAnchors::analyze(cfg, regions)?,
            entry_ports: RegionEntryPorts::analyze(cfg, regions)?,
            handler_bodies,
        })
    }

    pub fn reduce(self) -> Result<SemanticNode, StructureError> {
        let root = self.regions.tree().root();
        let mut order = Vec::new();
        let mut entered = BTreeSet::new();
        let mut pending = vec![(root, false)];
        while let Some((region, exiting)) = pending.pop() {
            if exiting {
                order.push(region);
                continue;
            }
            if !entered.insert(region) {
                continue;
            }
            let handlers = HandlerReducer::new(self.regions);
            let descriptor = self
                .regions
                .tree()
                .region(region)
                .ok_or(StructureError::UnknownRegion(region))?;
            if descriptor.entry.is_none()
                && matches!(
                    &descriptor.kind,
                    RegionKind::Catch(_) | RegionKind::Finally | RegionKind::Cleanup(_)
                )
            {
                let owner = descriptor.parent.unwrap_or(root);
                let body = handlers.body_region(owner, region)?;
                if body != region {
                    pending.push((body, false));
                    continue;
                }
            }
            pending.push((region, true));
            let children = RegionChildren::classify(self.cfg, self.regions, descriptor)?;
            let mut dependencies = children.ordinary;
            for handler in children.handlers {
                dependencies.push(handlers.body_region(region, handler)?);
                if let Some((target, _)) = handlers.forwarded_catch_target(handler)? {
                    // A split handler can be reduced before the shared catch
                    // body it forwards into. Make that body an explicit
                    // dependency unless it lexically contains this owner,
                    // which would create a region cycle.
                    if !self
                        .regions
                        .tree()
                        .is_ancestor(target, region)
                        .map_err(|_| StructureError::UnknownRegion(target))?
                    {
                        dependencies.push(target);
                    }
                }
            }
            dependencies.sort();
            dependencies.dedup();
            pending.extend(dependencies.into_iter().rev().map(|child| (child, false)));
        }
        let mut reduced = BTreeMap::<RegionId, ReducedRegion>::new();
        for region in order {
            let node = self.reduce_region(region, &mut reduced)?;
            reduced.insert(region, node);
        }
        let root_region = root;
        let mut root = reduced
            .remove(&root_region)
            .ok_or(StructureError::MissingReduction(root_region))?;
        let root_entry = self
            .regions
            .tree()
            .region(root_region)
            .and_then(|region| region.entry)
            .ok_or(StructureError::MissingEntry(root_region))?;
        let root = root
            .ports
            .remove(&root_entry)
            .ok_or(StructureError::RegionEntryMissing {
                region: root_region,
                entry: root_entry,
            })?;
        if let Some(port) = root.continuations.ports().iter().next() {
            return Err(StructureError::UnboundContinuation {
                scope: port.scope,
                target: port.target,
            });
        }
        Self::verify_root_labels("contracted", &root.body)?;
        Self::verify_node_limit(root_region, "contraction", &root.body)?;
        let body = ExceptionEnvelopeCanonicalizer::new(self.cfg, self.regions).apply(root.body)?;
        Self::verify_root_labels("exception-canonicalized", &body)?;
        Self::verify_node_limit(root_region, "exception canonicalization", &body)?;
        let mut body = LexicalLabels::uniquify(body).map_err(StructureError::from)?;
        Self::verify_root_labels("label-uniquified", &body)?;
        Self::verify_node_limit(root_region, "label repair", &body)?;
        SemanticCleanupResolver::apply(self.regions, &mut body);
        Ok(body)
    }

    fn verify_node_limit(
        region: RegionId,
        stage: &'static str,
        body: &SemanticNode,
    ) -> Result<(), StructureError> {
        const MAX_SEMANTIC_ITEMS: usize = 100_000;
        let mut count = SemanticComplexity::default();
        count.visit_node(body);
        if count.items > MAX_SEMANTIC_ITEMS {
            Err(StructureError::SemanticItemLimit {
                region,
                stage,
                items: count.items,
                limit: MAX_SEMANTIC_ITEMS,
            })
        } else {
            Ok(())
        }
    }

    fn verify_root_labels(stage: &'static str, body: &SemanticNode) -> Result<(), StructureError> {
        match LexicalLabels::escaped_loop(body) {
            Some(label) => Err(StructureError::EscapedRootLabel { stage, label }),
            None => Ok(()),
        }
    }

    fn reduce_region(
        &self,
        region_id: RegionId,
        reduced: &mut BTreeMap<RegionId, ReducedRegion>,
    ) -> Result<ReducedRegion, StructureError> {
        let region = self
            .regions
            .tree()
            .region(region_id)
            .ok_or(StructureError::UnknownRegion(region_id))?
            .clone();
        let children = RegionChildren::classify(self.cfg, self.regions, &region)?;
        let contraction = ChildReducer::new(
            self.cfg,
            self.regions,
            region_id,
            &children.ordinary,
            &self.handler_bodies,
            &self.anchors,
            self.observer,
        )
        .reduce(reduced)?;
        let entries = self.entry_ports.of(region_id)?.clone();
        if entries.is_empty() {
            let mut region_cfg = RegionCfgBuilder::new(
                self.cfg,
                self.regions,
                region_id,
                &children.ordinary,
                &contraction.ports,
                &self.anchors,
                &contraction.flows,
                &entries,
                None,
            )
            .build()?;
            self.prepare_region_cfg(region_id, &region, &mut region_cfg)?;
            let body = self.structure_region_cfg(
                region_id,
                &region.kind,
                &mut region_cfg,
                contraction.seeded,
            )?;
            return Ok(ReducedRegion {
                ports: BTreeMap::new(),
                detached: Some(ReducedPort::new(body)),
            });
        }
        let mut region_cfgs = BTreeMap::new();
        for entry in &entries {
            let mut region_cfg = RegionCfgBuilder::new(
                self.cfg,
                self.regions,
                region_id,
                &children.ordinary,
                &contraction.ports,
                &self.anchors,
                &contraction.flows,
                &entries,
                Some(*entry),
            )
            .build()?;
            self.prepare_region_cfg(region_id, &region, &mut region_cfg)?;
            region_cfgs.insert(*entry, region_cfg);
        }

        let handlers = if matches!(&region.kind, RegionKind::Try | RegionKind::Synchronized(_)) {
            let primary = region
                .entry
                .ok_or(StructureError::MissingEntry(region_id))?;
            let region_cfg =
                region_cfgs
                    .get(&primary)
                    .ok_or(StructureError::RegionEntryMissing {
                        region: region_id,
                        entry: primary,
                    })?;
            Some(
                HandlerReducer::new(self.regions)
                    .reduce(region_id, &children, region_cfg, reduced)?,
            )
        } else {
            None
        };
        let envelope = handlers.as_ref().map(|handlers| &handlers.envelope);

        let mut ports = BTreeMap::new();
        let port_count = region_cfgs.len();
        let mut seeded = contraction.seeded;
        for (index, (entry, mut region_cfg)) in region_cfgs.into_iter().enumerate() {
            let catches_reachable = envelope.is_some_and(|envelope| {
                region_cfg.reaches_any_handler(self.cfg, self.regions, envelope.catch_regions())
            });
            let port_seeded = if index + 1 == port_count {
                std::mem::take(&mut seeded)
            } else {
                seeded.clone()
            };
            let mut port_seeded = port_seeded;
            let enclosed = matches!(&region.kind, RegionKind::Try | RegionKind::Synchronized(_))
                .then(|| region_cfg.take_enclosed_body(entry, &mut port_seeded))
                .flatten();
            let body = match enclosed {
                Some(body) => body,
                None => self.structure_region_cfg(
                    region_id,
                    &region.kind,
                    &mut region_cfg,
                    port_seeded,
                )?,
            };
            let body = match envelope {
                Some(envelope) if envelope.required_for(catches_reachable) => {
                    envelope.clone().attach(region_id, body)
                }
                None => body,
                Some(_) => body,
            };
            let body = match &region.kind {
                RegionKind::Synchronized(synchronized) => SemanticNode::Synchronized {
                    region: region_id,
                    lock: crate::ir::SemanticOperand::new(
                        crate::ir::SemanticExpression::from_argument(synchronized.lock.clone())?,
                    ),
                    method: synchronized.method,
                    body: Box::new(body),
                },
                _ => body,
            };
            ports.insert(entry, ReducedPort::new(body));
        }
        if let Some(handlers) = handlers {
            for (entry, handler_port) in handlers.ports {
                let mut body = handler_port.port.body;
                if let Some(finally) = handlers
                    .envelope
                    .finally
                    .clone()
                    .filter(|finally| finally.region != handler_port.handler)
                {
                    body = ExceptionEnvelope {
                        catches: Vec::new(),
                        finally: Some(finally),
                    }
                    .attach(region_id, body);
                }
                if ports.insert(entry, ReducedPort::new(body)).is_some() {
                    return Err(StructureError::ConflictingEntryPort {
                        owner: region_id,
                        entry,
                    });
                }
            }
        }
        Ok(ReducedRegion {
            ports,
            detached: None,
        })
    }

    fn prepare_region_cfg(
        &self,
        region_id: RegionId,
        region: &StructuredRegion,
        region_cfg: &mut RegionCfg,
    ) -> Result<(), StructureError> {
        if matches!(&region.kind, RegionKind::Loop(_)) {
            let header = region
                .entry
                .ok_or(StructureError::MissingEntry(region_id))?;
            let back_sources = region_cfg
                .cfg
                .block_ids()
                .into_iter()
                .filter(|source| region_cfg.cfg.has_edge(*source, header))
                .collect::<Vec<_>>();
            for source in back_sources {
                region_cfg.cfg.remove_edge(source, header);
            }
        }
        self.observer.observe(crate::ir::AnalysisEvent::RegionCfg {
            region: region_id,
            kind: &region.kind,
            source_cfg: self.cfg,
            region_cfg: &region_cfg.cfg,
            mapping: &region_cfg.mapping,
            open_flows: &region_cfg.open_flows,
        });
        Ok(())
    }

    fn structure_region_cfg(
        &self,
        region_id: RegionId,
        kind: &RegionKind,
        region_cfg: &mut RegionCfg,
        mut seeded: BTreeMap<BlockId, SemanticNode>,
    ) -> Result<SemanticNode, StructureError> {
        let semantic = SemanticFactory::new(self.cfg, self.regions, region_id);
        if region_cfg.representatives.is_empty() {
            let leaves = self
                .regions
                .leaves()
                .iter()
                .filter(|leave| {
                    leave.leave.source == region_id && leave.leave.source_block.is_none()
                })
                .map(|leave| semantic.leave(leave))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(SemanticNode::sequence(leaves));
        }
        if !region_cfg.entry_boundaries.is_empty() {
            let cuts = region_cfg
                .entry_boundaries
                .iter()
                .map(|(boundary, target)| (*target, *boundary))
                .collect::<BTreeMap<_, _>>();
            for body in seeded.values_mut() {
                let mut binding = EntryCutBinding {
                    region: region_id,
                    cuts: &cuts,
                };
                *body = binding
                    .fold_node(std::mem::replace(body, SemanticNode::Empty))
                    .map_err(StructureError::from)?;
            }
        }
        for (block, leave) in &region_cfg.boundaries {
            let mut node = semantic.leave(leave)?;
            let mut anchor_blocks = leave
                .leave
                .source_block
                .into_iter()
                .filter(|source| self.anchors.phi_copy_blocks().contains(source))
                .collect::<Vec<_>>();
            if let Some(target) = leave
                .leave
                .edge
                .map(|edge| edge.target)
                .filter(|target| self.anchors.phi_copy_blocks().contains(target))
                .filter(|target| !region_cfg.representatives.contains(target))
            {
                anchor_blocks.push(target);
            }
            if let crate::ir::RegionExit::FallThrough(target) = &leave.leave.exit {
                if self.anchors.phi_copy_blocks().contains(target) {
                    anchor_blocks.push(*target);
                }
            }
            let mut seen_anchors = BTreeSet::new();
            anchor_blocks.retain(|anchor| seen_anchors.insert(*anchor));
            for anchor in anchor_blocks.into_iter().rev() {
                node = Self::anchor_block(anchor, node);
            }
            seeded.insert(*block, node);
        }
        for (block, target) in &region_cfg.entry_boundaries {
            let leave = SemanticNode::Leave(SemanticLeave {
                site: None,
                condition: None,
                kind: SemanticLeaveKind::FallThrough(*target),
                edge: None,
                origin: None,
                source: region_id,
                destination: region_id,
                target: region_id,
                cleanup: Vec::new(),
            });
            seeded.insert(
                *block,
                if self.anchors.phi_copy_blocks().contains(target) {
                    Self::anchor_block(*target, leave)
                } else {
                    leave
                },
            );
        }
        let terminal_seeds = region_cfg
            .boundaries
            .keys()
            .copied()
            .chain(region_cfg.terminal_seeds.iter().copied())
            .collect();
        let local = &region_cfg.cfg;
        let has_open_flows = !region_cfg.open_flows.is_empty();
        let is_switch_dispatch = Self::has_direct_switch_dispatch(
            kind,
            self.regions
                .tree()
                .region(region_id)
                .and_then(|region| region.entry),
            local,
        );
        if is_switch_dispatch {
            return SwitchStructurer::new(local, &semantic, region_id, seeded)
                .terminal_seeds(terminal_seeds)
                .structure();
        }
        GraphStructurer::new(local, &semantic, region_id)
            .seeded(seeded)
            .terminal_seeds(terminal_seeds)
            .force_graph_reduction(has_open_flows)
            .structure()
    }

    fn has_direct_switch_dispatch(
        kind: &RegionKind,
        region_entry: Option<BlockId>,
        local: &CFG,
    ) -> bool {
        // A child region can own the same physical entry as its switch parent.
        // RegionCfgBuilder then preserves the entry as a contracted nop whose
        // semantic body is supplied through `seeded`; only the original switch
        // header satisfies SwitchStructurer's input contract.
        matches!(kind, RegionKind::Switch(_))
            && region_entry == Some(local.entry)
            && local
                .block(local.entry)
                .and_then(|block| block.terminator())
                .is_some_and(|terminator| terminator.insn_type == crate::ir::InsnType::Switch)
    }

    fn anchor_block(block: BlockId, continuation: SemanticNode) -> SemanticNode {
        SemanticNode::sequence([
            SemanticNode::BasicBlock(SemanticBlock {
                id: block,
                statements: Vec::new(),
            }),
            continuation,
        ])
    }
}

#[derive(Default)]
struct SemanticComplexity {
    items: usize,
}

impl SemanticVisitor for SemanticComplexity {
    fn enter_node(&mut self, _node: &SemanticNode) {
        self.items = self.items.saturating_add(1);
    }

    fn enter_operation(&mut self, _operation: &SemanticOperation) {
        self.items = self.items.saturating_add(1);
    }
}

struct EntryCutBinding<'a> {
    region: RegionId,
    cuts: &'a BTreeMap<BlockId, BlockId>,
}

impl SemanticFolder for EntryCutBinding<'_> {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::Leave(mut leave) = node else {
            return Ok(node);
        };
        if leave.target != self.region {
            return Ok(SemanticNode::Leave(leave));
        }
        let target = match &mut leave.kind {
            SemanticLeaveKind::FallThrough(target) | SemanticLeaveKind::Jump(target) => target,
            _ => return Ok(SemanticNode::Leave(leave)),
        };
        if let Some(boundary) = self.cuts.get(target) {
            *target = *boundary;
        }
        Ok(SemanticNode::Leave(leave))
    }
}

#[derive(Clone, Default)]
pub(super) struct ExceptionEnvelope {
    catches: Vec<SemanticCatch>,
    finally: Option<SemanticFinally>,
}

impl ExceptionEnvelope {
    fn catch_regions(&self) -> impl Iterator<Item = RegionId> + '_ {
        self.catches.iter().map(|catch| catch.region)
    }

    fn required_for(&self, exceptional: bool) -> bool {
        self.finally.is_some() || (exceptional && !self.catches.is_empty())
    }

    fn attach(self, owner: RegionId, body: SemanticNode) -> SemanticNode {
        if self.catches.is_empty() && self.finally.is_none() {
            return body;
        }
        SemanticNode::Try {
            region: owner,
            body: Box::new(body),
            catches: self.catches,
            finally: self.finally,
        }
    }
}

#[derive(Clone)]
pub(super) struct ReducedRegion {
    pub(super) ports: BTreeMap<BlockId, ReducedPort>,
    pub(super) detached: Option<ReducedPort>,
}

#[derive(Clone)]
pub(super) struct ReducedPort {
    pub(super) body: SemanticNode,
    pub(super) continuations: ContinuationFacts,
}

impl ReducedPort {
    fn new(body: SemanticNode) -> Self {
        let continuations = ContinuationFacts::analyze(&body);
        Self {
            body,
            continuations,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::RegionReducer;
    use crate::ir::{Block, BlockId, InsnNode, InsnType, RegionKind, SwitchRegion, CFG};

    #[test]
    fn contracted_switch_header_uses_general_structurer() {
        let entry = BlockId::new(0);
        let kind = RegionKind::Switch(SwitchRegion { follow: None });

        let mut direct = CFG::new("direct_switch");
        let mut header = Block::new(entry.raw());
        header.push(InsnNode::new(InsnType::Switch, 0));
        direct.add_block(header);
        assert!(RegionReducer::has_direct_switch_dispatch(
            &kind,
            Some(entry),
            &direct,
        ));

        let mut contracted = CFG::new("contracted_switch");
        let mut header = Block::new(entry.raw());
        header.push(InsnNode::nop());
        contracted.add_block(header);
        assert!(!RegionReducer::has_direct_switch_dispatch(
            &kind,
            Some(entry),
            &contracted,
        ));
    }
}
