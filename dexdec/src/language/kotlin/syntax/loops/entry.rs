//! First source-observable evaluation performed by one loop iteration.

use crate::ir::{
    SemanticExpression, SemanticNode, SemanticOperation, SemanticPredicate, SemanticStatement,
};

pub(super) struct IterationEntry<'a> {
    pub(super) instruction: &'a SemanticOperation,
    pub(super) statement: Option<&'a SemanticStatement>,
}

impl<'a> IterationEntry<'a> {
    pub(super) fn find(node: &'a SemanticNode) -> Option<Self> {
        match Self::search(node) {
            EntrySearch::Found(entry) => Some(entry),
            EntrySearch::Transparent | EntrySearch::Blocked => None,
        }
    }

    fn search(node: &'a SemanticNode) -> EntrySearch<'a> {
        match node {
            SemanticNode::Empty => EntrySearch::Transparent,
            SemanticNode::Sequence(children) => {
                for child in children {
                    match Self::search(child) {
                        EntrySearch::Transparent => {}
                        result => return result,
                    }
                }
                EntrySearch::Transparent
            }
            SemanticNode::BasicBlock(block) => {
                let Some(statement) = block.statements.first() else {
                    return EntrySearch::Transparent;
                };
                let Some(instruction) = statement.instruction_ref() else {
                    return EntrySearch::Blocked;
                };
                EntrySearch::Found(Self {
                    instruction,
                    statement: Some(statement),
                })
            }
            SemanticNode::If { condition, .. } => Self::predicate(condition)
                .map(EntrySearch::Found)
                .unwrap_or(EntrySearch::Blocked),
            SemanticNode::ForEach { iterable, .. }
            | SemanticNode::Switch {
                selector: iterable, ..
            }
            | SemanticNode::Synchronized { lock: iterable, .. } => Self::argument(iterable)
                .map(EntrySearch::Found)
                .unwrap_or(EntrySearch::Blocked),
            SemanticNode::For { init, .. } => init
                .instruction_ref()
                .map(|instruction| {
                    EntrySearch::Found(Self {
                        instruction,
                        statement: Some(init),
                    })
                })
                .unwrap_or(EntrySearch::Blocked),
            SemanticNode::Label { body, .. } => Self::search(body),
            SemanticNode::Loop { .. } | SemanticNode::Try { .. } | SemanticNode::Leave(_) => {
                EntrySearch::Blocked
            }
        }
    }

    fn argument(argument: &'a SemanticExpression) -> Option<Self> {
        argument.as_operation().map(|instruction| Self {
            instruction,
            statement: None,
        })
    }

    fn predicate(predicate: &'a SemanticPredicate) -> Option<Self> {
        let mut predicate = predicate;
        loop {
            match predicate {
                SemanticPredicate::Test(instruction) => {
                    return Some(Self {
                        instruction,
                        statement: None,
                    });
                }
                SemanticPredicate::Not(inner) => predicate = inner,
                SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                    predicate = terms.first()?;
                }
                SemanticPredicate::True | SemanticPredicate::False => return None,
            }
        }
    }
}

enum EntrySearch<'a> {
    Transparent,
    Found(IterationEntry<'a>),
    Blocked,
}
