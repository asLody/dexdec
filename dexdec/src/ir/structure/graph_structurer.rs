//! Region-local semantic graph structuring.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::StrongComponents;
use crate::ir::semantic::SemanticFactory;
use crate::ir::{BlockId, RegionId, SemanticNode, CFG};

use super::{
    acyclic::{AcyclicStructure, AcyclicStructurer},
    flow_graph::SemanticFlowGraph,
    StructureError,
};

pub(super) struct GraphStructurer<'a, 'semantic> {
    cfg: &'a CFG,
    semantic: &'semantic SemanticFactory<'semantic>,
    region: RegionId,
    seeded: BTreeMap<BlockId, SemanticNode>,
    terminal_seeds: BTreeSet<BlockId>,
    force_graph_reduction: bool,
}

impl<'a, 'semantic> GraphStructurer<'a, 'semantic> {
    pub(super) fn new(
        cfg: &'a CFG,
        semantic: &'semantic SemanticFactory<'semantic>,
        region: RegionId,
    ) -> Self {
        Self {
            cfg,
            semantic,
            region,
            seeded: BTreeMap::new(),
            terminal_seeds: BTreeSet::new(),
            force_graph_reduction: false,
        }
    }

    pub(super) fn seeded(mut self, nodes: BTreeMap<BlockId, SemanticNode>) -> Self {
        self.seeded = nodes;
        self
    }

    pub(super) fn terminal_seeds(mut self, blocks: BTreeSet<BlockId>) -> Self {
        self.terminal_seeds = blocks;
        self
    }

    pub(super) fn force_graph_reduction(mut self, force: bool) -> Self {
        self.force_graph_reduction = force;
        self
    }

    pub(super) fn structure(mut self) -> Result<SemanticNode, StructureError> {
        let nodes = self.cfg.graph_node_ids();
        if nodes.is_empty() {
            return Ok(SemanticNode::Empty);
        }
        let components = StrongComponents::analyze(self.cfg, nodes.iter().copied());
        if self.force_graph_reduction || !self.terminal_seeds.is_empty() || !components.is_acyclic()
        {
            return self.reduce_graph();
        }
        let acyclic = AcyclicStructurer::new(self.cfg, self.semantic, &mut self.seeded)
            .structure()
            .map_err(|source| StructureError::Acyclic {
                region: self.region,
                source,
            })?;
        match acyclic {
            AcyclicStructure::Structured(node) => Ok(node),
            AcyclicStructure::RequiresGraphReduction(_) => self.reduce_graph(),
        }
    }

    fn reduce_graph(&self) -> Result<SemanticNode, StructureError> {
        SemanticFlowGraph::build(
            self.cfg,
            self.semantic,
            self.region,
            &self.seeded,
            &self.terminal_seeds,
        )?
        .reduce(self.semantic)
    }
}
