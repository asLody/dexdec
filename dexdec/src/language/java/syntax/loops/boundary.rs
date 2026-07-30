use crate::ir::{
    SemanticFoldError, SemanticFolder, SemanticNode, SemanticSiteId, SemanticStatement,
};

#[derive(Clone, Copy)]
pub(super) enum Boundary {
    First,
    Last,
}

pub(super) struct StatementBoundary;

impl StatementBoundary {
    pub(super) fn linear(node: &SemanticNode) -> Option<Vec<&SemanticStatement>> {
        let mut statements = Vec::new();
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Empty => {}
                SemanticNode::BasicBlock(block) => statements.extend(&block.statements),
                SemanticNode::Sequence(children) => pending.extend(children.iter().rev()),
                _ => return None,
            }
        }
        Some(statements)
    }

    pub(super) fn is_reorderable(node: &SemanticNode) -> bool {
        Self::linear(node).is_some_and(|statements| {
            statements.iter().all(|statement| {
                statement
                    .instruction_ref()
                    .is_some_and(|instruction| instruction.effects().is_pure())
            })
        })
    }

    pub(super) fn first(node: &SemanticNode) -> Option<&SemanticStatement> {
        Self::find(node, Boundary::First)
    }

    pub(super) fn last(node: &SemanticNode) -> Option<&SemanticStatement> {
        Self::find(node, Boundary::Last)
    }

    pub(super) fn take(node: &mut SemanticNode, boundary: Boundary) -> Option<SemanticStatement> {
        let root = std::mem::replace(node, SemanticNode::Empty);
        let (statement, rebuilt) = Self::extract(root, boundary);
        *node = rebuilt;
        statement
    }

    pub(super) fn take_site(
        node: &mut SemanticNode,
        site: SemanticSiteId,
    ) -> Option<SemanticStatement> {
        let root = std::mem::replace(node, SemanticNode::Empty);
        let mut extraction = StatementExtraction {
            site,
            statement: None,
        };
        *node = extraction.fold_node(root).ok()?;
        extraction.statement
    }

    fn find(node: &SemanticNode, boundary: Boundary) -> Option<&SemanticStatement> {
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::BasicBlock(block) if !block.statements.is_empty() => {
                    return match boundary {
                        Boundary::First => block.statements.first(),
                        Boundary::Last => block.statements.last(),
                    };
                }
                SemanticNode::Sequence(children) => match boundary {
                    Boundary::First => pending.extend(children.iter().rev()),
                    Boundary::Last => pending.extend(children.iter()),
                },
                _ => {}
            }
        }
        None
    }

    fn extract(
        root: SemanticNode,
        boundary: Boundary,
    ) -> (Option<SemanticStatement>, SemanticNode) {
        let mut current = root;
        let mut frames = Vec::new();
        let statement = loop {
            match current {
                SemanticNode::BasicBlock(mut block) if !block.statements.is_empty() => {
                    let statement = match boundary {
                        Boundary::First => {
                            let mut statements = block.statements.into_iter();
                            let statement = statements.next();
                            block.statements = statements.collect();
                            statement
                        }
                        Boundary::Last => block.statements.pop(),
                    };
                    current = SemanticNode::BasicBlock(block);
                    break statement;
                }
                SemanticNode::Sequence(mut children) => {
                    let index = match boundary {
                        Boundary::First => children
                            .iter()
                            .position(|child| Self::first(child).is_some()),
                        Boundary::Last => children
                            .iter()
                            .rposition(|child| Self::last(child).is_some()),
                    };
                    let Some(index) = index else {
                        current = SemanticNode::Sequence(children);
                        break None;
                    };
                    let mut selected_and_suffix = children.split_off(index);
                    let selected = selected_and_suffix.remove(0);
                    frames.push(BoundaryFrame {
                        prefix: children,
                        suffix: selected_and_suffix,
                    });
                    current = selected;
                }
                other => {
                    current = other;
                    break None;
                }
            }
        };
        while let Some(frame) = frames.pop() {
            current = SemanticNode::sequence(
                frame
                    .prefix
                    .into_iter()
                    .chain([current])
                    .chain(frame.suffix),
            );
        }
        (statement, current)
    }
}

struct StatementExtraction {
    site: SemanticSiteId,
    statement: Option<SemanticStatement>,
}

impl SemanticFolder for StatementExtraction {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        if let SemanticNode::BasicBlock(block) = &mut node {
            if let Some(index) = block
                .statements
                .iter()
                .position(|statement| statement.site == Some(self.site))
            {
                if self.statement.is_some() {
                    return Err(SemanticFoldError::MalformedWorkStack);
                }
                self.statement = Some(block.statements.remove(index));
            }
        }
        Ok(match node {
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            node => node,
        })
    }
}

struct BoundaryFrame {
    prefix: Vec<SemanticNode>,
    suffix: Vec<SemanticNode>,
}
