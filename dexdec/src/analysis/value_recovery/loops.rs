//! Loop-invariant motion over source identities.

use std::collections::BTreeSet;

use crate::ir::{
    SemanticExpressionFacts, SemanticFoldError, SemanticFolder, SemanticLoopKind, SemanticNode,
};

pub(super) struct LoopInvariantMotion {
    changed: bool,
}

impl LoopInvariantMotion {
    pub(super) fn apply(root: &mut SemanticNode) -> Result<bool, SemanticFoldError> {
        let before = crate::ir::semantic::SemanticCompletion::analyze(root);
        let body = std::mem::replace(root, SemanticNode::Empty);
        let mut motion = Self { changed: false };
        *root = motion.fold_node(body)?;
        let after = crate::ir::semantic::SemanticCompletion::analyze(root);
        if before != after {
            return Err(SemanticFoldError::CompletionChanged {
                transform: "loop-invariant-motion",
            });
        }
        Ok(motion.changed)
    }

    fn split_setup(setup: SemanticNode, body: &SemanticNode) -> (Vec<SemanticNode>, SemanticNode) {
        let mut nodes = match setup {
            SemanticNode::Sequence(nodes) => nodes,
            SemanticNode::Empty => Vec::new(),
            node => vec![node],
        };
        let mut loop_facts = SemanticExpressionFacts::of_node(body);
        for node in &nodes {
            loop_facts.merge(&SemanticExpressionFacts::of_node(node));
        }
        let loop_definitions = loop_facts.defined_variables().collect::<BTreeSet<_>>();
        let mut count = 0;
        for node in &nodes {
            let SemanticNode::BasicBlock(block) = node else {
                break;
            };
            if block.statements.is_empty()
                || block.statements.iter().any(|statement| {
                    statement
                        .instruction_ref()
                        .is_none_or(|instruction| !instruction.effects().is_pure())
                })
            {
                break;
            }
            let facts = SemanticExpressionFacts::of_node(node);
            let definitions = facts.defined_variables().collect::<BTreeSet<_>>();
            let uses = facts.used_variables().collect::<BTreeSet<_>>();
            if definitions.is_empty()
                || !definitions.is_disjoint(&uses)
                || uses
                    .iter()
                    .any(|variable| loop_definitions.contains(variable))
                || definitions.iter().any(|variable| {
                    loop_facts.definition_count(*variable) != facts.definition_count(*variable)
                })
            {
                break;
            }
            count += 1;
        }
        let remainder = nodes.split_off(count);
        (nodes, SemanticNode::sequence(remainder))
    }
}

impl SemanticFolder for LoopInvariantMotion {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            mut test,
            body,
        } = node
        else {
            return Ok(node);
        };
        let (hoisted, setup) = Self::split_setup(*test.setup, &body);
        test.setup = Box::new(setup);
        let loop_node = SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            test,
            body,
        };
        if hoisted.is_empty() {
            return Ok(loop_node);
        }
        self.changed = true;
        Ok(SemanticNode::sequence(
            hoisted.into_iter().chain(std::iter::once(loop_node)),
        ))
    }
}
