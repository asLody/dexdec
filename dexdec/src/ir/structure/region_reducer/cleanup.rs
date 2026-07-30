use crate::ir::{RegionGraph, RegionId, SemanticLoopControl, SemanticNode, SemanticSwitchCase};

#[derive(Clone, Copy)]
struct CleanupFrame {
    owner_depth: usize,
    cleanup: RegionId,
}

pub(super) struct SemanticCleanupResolver<'a> {
    graph: &'a RegionGraph,
    regions: Vec<RegionId>,
    cleanups: Vec<CleanupFrame>,
}

impl<'a> SemanticCleanupResolver<'a> {
    pub(super) fn apply(graph: &'a RegionGraph, root: &mut SemanticNode) {
        let method = graph.tree().root();
        let mut resolver = Self {
            graph,
            regions: vec![method],
            cleanups: Vec::new(),
        };
        resolver.resolve(root);
    }

    fn resolve(&mut self, node: &mut SemanticNode) {
        match node {
            SemanticNode::Empty | SemanticNode::BasicBlock(_) => {}
            SemanticNode::Sequence(nodes) => {
                for node in nodes {
                    self.resolve(node);
                }
            }
            SemanticNode::If {
                then_node,
                else_node,
                ..
            } => {
                self.resolve(then_node);
                if let Some(else_node) = else_node {
                    self.resolve(else_node);
                }
            }
            SemanticNode::Loop {
                control,
                test,
                body,
                ..
            } => {
                self.with_control(*control, |resolver| {
                    resolver.resolve(&mut test.setup);
                    resolver.resolve(body);
                });
            }
            SemanticNode::For { control, body, .. }
            | SemanticNode::ForEach { control, body, .. } => {
                self.with_control(*control, |resolver| resolver.resolve(body));
            }
            SemanticNode::Switch { region, cases, .. } => {
                self.with_optional_region(*region, |resolver| {
                    for SemanticSwitchCase { body, .. } in cases {
                        resolver.resolve(body);
                    }
                });
            }
            SemanticNode::Try {
                region,
                body,
                catches,
                finally,
            } => {
                self.push_region(*region);
                if let Some(finally) = finally.as_ref() {
                    self.push_cleanup(finally.region);
                }
                self.resolve(body);
                for catch in catches {
                    self.push_region(catch.region);
                    self.resolve(&mut catch.body);
                    self.pop_region(catch.region);
                }
                if finally.is_some() {
                    self.cleanups.pop();
                }
                if let Some(finally) = finally {
                    self.push_region(finally.region);
                    self.resolve(&mut finally.body);
                    self.pop_region(finally.region);
                }
                self.pop_region(*region);
            }
            SemanticNode::Synchronized { region, body, .. } => {
                self.push_region(*region);
                self.push_cleanup(*region);
                self.resolve(body);
                self.cleanups.pop();
                self.pop_region(*region);
            }
            SemanticNode::Label { label, body } => {
                self.push_region(label.region);
                self.resolve(body);
                self.pop_region(label.region);
            }
            SemanticNode::Leave(leave) => {
                let destination_depth = self
                    .regions
                    .iter()
                    .rposition(|region| *region == leave.destination);
                leave.cleanup = self
                    .cleanups
                    .iter()
                    .rev()
                    .filter(|frame| destination_depth.is_none_or(|depth| depth < frame.owner_depth))
                    .map(|frame| frame.cleanup)
                    .collect();
            }
        }
    }

    fn with_control(&mut self, control: SemanticLoopControl, apply: impl FnOnce(&mut Self)) {
        let region = match control {
            SemanticLoopControl::Region(region) => region,
            SemanticLoopControl::Label(label) => label.region,
        };
        self.push_region(region);
        apply(self);
        self.pop_region(region);
    }

    fn with_optional_region(&mut self, region: Option<RegionId>, apply: impl FnOnce(&mut Self)) {
        if let Some(region) = region {
            self.push_region(region);
        }
        apply(self);
        if let Some(region) = region {
            self.pop_region(region);
        }
    }

    fn push_region(&mut self, region: RegionId) {
        debug_assert!(self.graph.tree().region(region).is_some());
        self.regions.push(region);
    }

    fn pop_region(&mut self, region: RegionId) {
        debug_assert_eq!(self.regions.pop(), Some(region));
    }

    fn push_cleanup(&mut self, cleanup: RegionId) {
        self.cleanups.push(CleanupFrame {
            owner_depth: self.regions.len() - 1,
            cleanup,
        });
    }
}
