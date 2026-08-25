use crate::ir::{SemanticFoldError, SemanticNode, SemanticSiteId, SemanticVisitor};

pub(crate) struct SemanticSiteNumbering {
    next: u64,
}

impl SemanticSiteNumbering {
    /// Site ids in the same node order `assign` writes them.
    pub(crate) fn fingerprint(root: &SemanticNode) -> Vec<u64> {
        let mut visitor = SiteFingerprint { sites: Vec::new() };
        visitor.visit_node(root);
        visitor.sites
    }

    pub(crate) fn assign(root: &mut SemanticNode) -> Result<(), SemanticFoldError> {
        Self { next: 0 }.assign_node(root);
        Ok(())
    }

    /// Post-order site assignment matching `SemanticFolder::finish_node`.
    ///
    /// Child visit order follows `fold_node`, not the pre-order fingerprint walk.
    fn assign_node(&mut self, node: &mut SemanticNode) {
        match node {
            SemanticNode::Empty => {}
            SemanticNode::Sequence(children) => {
                for child in children {
                    self.assign_node(child);
                }
            }
            SemanticNode::BasicBlock(block) => {
                for statement in &mut block.statements {
                    statement.site = Some(self.next_site());
                }
            }
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                self.assign_node(then_node.as_mut());
                if let Some(else_node) = else_node {
                    self.assign_node(else_node.as_mut());
                }
                condition.site = Some(self.next_site());
            }
            SemanticNode::Loop { test, body, .. } => {
                self.assign_node(test.setup.as_mut());
                self.assign_node(body.as_mut());
                test.condition.site = Some(self.next_site());
            }
            SemanticNode::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                self.assign_node(body.as_mut());
                init.site = Some(self.next_site());
                condition.site = Some(self.next_site());
                update.site = Some(self.next_site());
            }
            SemanticNode::ForEach { iterable, body, .. } => {
                self.assign_node(body.as_mut());
                iterable.site = Some(self.next_site());
            }
            SemanticNode::Switch {
                selector, cases, ..
            } => {
                for case in cases {
                    self.assign_node(&mut case.body);
                }
                selector.site = Some(self.next_site());
            }
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                self.assign_node(body.as_mut());
                for catch in catches {
                    self.assign_node(&mut catch.body);
                }
                if let Some(finally) = finally {
                    self.assign_node(finally.body.as_mut());
                }
            }
            SemanticNode::Synchronized { lock, body, .. } => {
                self.assign_node(body.as_mut());
                lock.site = Some(self.next_site());
            }
            SemanticNode::Label { body, .. } => {
                self.assign_node(body.as_mut());
            }
            SemanticNode::Leave(leave) => {
                leave.site = Some(self.next_site());
            }
        }
    }
}

struct SiteFingerprint {
    sites: Vec<u64>,
}

impl SiteFingerprint {
    fn push(&mut self, site: Option<SemanticSiteId>) {
        if let Some(site) = site {
            self.sites.push(site.0);
        }
    }
}

impl SemanticVisitor for SiteFingerprint {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::BasicBlock(block) => {
                for statement in &block.statements {
                    self.push(statement.site);
                }
            }
            SemanticNode::For {
                init,
                condition,
                update,
                ..
            } => {
                self.push(init.site);
                self.push(condition.site);
                self.push(update.site);
            }
            SemanticNode::If { condition, .. } => self.push(condition.site),
            SemanticNode::Loop { test, .. } => self.push(test.condition.site),
            SemanticNode::ForEach { iterable, .. } => self.push(iterable.site),
            SemanticNode::Switch { selector, .. } => self.push(selector.site),
            SemanticNode::Synchronized { lock, .. } => self.push(lock.site),
            SemanticNode::Leave(leave) => self.push(leave.site),
            _ => {}
        }
    }
}

impl SemanticSiteNumbering {
    fn next_site(&mut self) -> SemanticSiteId {
        let site = SemanticSiteId(self.next);
        self.next += 1;
        site
    }
}
