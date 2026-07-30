use crate::ir::{SemanticFoldError, SemanticFolder, SemanticNode, SemanticSiteId};

pub(crate) struct SemanticSiteNumbering {
    next: u64,
}

impl SemanticSiteNumbering {
    pub(crate) fn assign(root: &mut SemanticNode) -> Result<(), SemanticFoldError> {
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = Self { next: 0 }.fold_node(body)?;
        Ok(())
    }
}

impl SemanticFolder for SemanticSiteNumbering {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        match &mut node {
            SemanticNode::BasicBlock(block) => {
                for statement in &mut block.statements {
                    statement.site = Some(self.next_site());
                }
            }
            SemanticNode::For {
                init,
                condition,
                update,
                ..
            } => {
                init.site = Some(self.next_site());
                condition.site = Some(self.next_site());
                update.site = Some(self.next_site());
            }
            SemanticNode::If { condition, .. } => {
                condition.site = Some(self.next_site());
            }
            SemanticNode::Loop { test, .. } => {
                test.condition.site = Some(self.next_site());
            }
            SemanticNode::ForEach { iterable, .. } => {
                iterable.site = Some(self.next_site());
            }
            SemanticNode::Switch { selector, .. } => {
                selector.site = Some(self.next_site());
            }
            SemanticNode::Synchronized { lock, .. } => {
                lock.site = Some(self.next_site());
            }
            SemanticNode::Leave(leave) => {
                leave.site = Some(self.next_site());
            }
            _ => {}
        }
        Ok(node)
    }
}

impl SemanticSiteNumbering {
    fn next_site(&mut self) -> SemanticSiteId {
        let site = SemanticSiteId(self.next);
        self.next += 1;
        site
    }
}
