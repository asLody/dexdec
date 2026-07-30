//! Promotion of a loop-entry control guard into the Kotlin loop condition.

use crate::ir::{
    SemanticLeaveKind, SemanticLoopControl, SemanticLoopKind, SemanticNode, SemanticPredicate,
};

pub(super) struct LoopGuardCondition;

impl LoopGuardCondition {
    pub(super) fn apply(node: SemanticNode) -> SemanticNode {
        let SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            mut test,
            body,
        } = node
        else {
            return node;
        };
        let body = *body;
        let Some((guard, guarded_body)) = GuardedIteration::analyze(control, body.clone()) else {
            return SemanticNode::Loop {
                control,
                header,
                kind: SemanticLoopKind::PreTested,
                test,
                body: Box::new(body),
            };
        };
        test.condition.value = Self::and(test.condition.value, guard);
        SemanticNode::Loop {
            control,
            header,
            kind: SemanticLoopKind::PreTested,
            test,
            body: Box::new(guarded_body),
        }
    }

    fn and(left: SemanticPredicate, right: SemanticPredicate) -> SemanticPredicate {
        match (left, right) {
            (SemanticPredicate::False, _) | (_, SemanticPredicate::False) => {
                SemanticPredicate::False
            }
            (SemanticPredicate::True, right) => right,
            (left, SemanticPredicate::True) => left,
            (SemanticPredicate::And(mut left), SemanticPredicate::And(right)) => {
                left.extend(right);
                SemanticPredicate::And(left)
            }
            (SemanticPredicate::And(mut terms), right) => {
                terms.push(right);
                SemanticPredicate::And(terms)
            }
            (left, SemanticPredicate::And(mut terms)) => {
                terms.insert(0, left);
                SemanticPredicate::And(terms)
            }
            (left, right) => SemanticPredicate::And(vec![left, right]),
        }
    }
}

struct GuardedIteration;

impl GuardedIteration {
    fn analyze(
        control: SemanticLoopControl,
        body: SemanticNode,
    ) -> Option<(SemanticPredicate, SemanticNode)> {
        if let Some(guarded) = Self::guard_with_trailing_exit(control, &body) {
            return Some(guarded);
        }
        let (mut prefix, decision, suffix) = Self::single_decision(body)?;
        let SemanticNode::If {
            condition,
            then_node,
            else_node,
        } = decision
        else {
            return None;
        };
        let else_node = else_node?;
        let condition = condition.into_inner();
        let (guard, continuing, exiting) = if Self::is_local_break(&then_node, control) {
            (condition.clone().negate(), *else_node, *then_node)
        } else if Self::is_local_break(&else_node, control) {
            (condition, *then_node, *else_node)
        } else {
            return None;
        };
        let continuing = Self::remove_terminal_continue(continuing, control)?;
        prefix.push(continuing);
        prefix.extend(Self::empty_blocks(&exiting));
        prefix.extend(suffix);
        Some((guard, SemanticNode::sequence(prefix)))
    }

    fn guard_with_trailing_exit(
        control: SemanticLoopControl,
        body: &SemanticNode,
    ) -> Option<(SemanticPredicate, SemanticNode)> {
        let nodes = match body {
            SemanticNode::Sequence(nodes) => nodes,
            node => std::slice::from_ref(node),
        };
        let meaningful = nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| !Self::empty(node))
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let [guard_index, exit_index] = meaningful.as_slice() else {
            return None;
        };
        Self::is_local_break(&nodes[*exit_index], control).then_some(())?;
        let SemanticNode::If {
            condition,
            then_node,
            else_node,
        } = &nodes[*guard_index]
        else {
            return None;
        };
        else_node.as_deref().is_none_or(Self::empty).then_some(())?;
        let continuing = Self::remove_terminal_continue((**then_node).clone(), control)?;
        let mut result = nodes[..*guard_index].to_vec();
        result.push(continuing);
        if let Some(else_node) = else_node {
            result.extend(Self::empty_blocks(else_node));
        }
        result.extend(Self::empty_blocks(&nodes[*exit_index]));
        result.extend(nodes[*exit_index + 1..].iter().cloned());
        Some((condition.value.clone(), SemanticNode::sequence(result)))
    }

    fn single_decision(
        body: SemanticNode,
    ) -> Option<(Vec<SemanticNode>, SemanticNode, Vec<SemanticNode>)> {
        let nodes = match body {
            SemanticNode::Sequence(nodes) => nodes,
            node => vec![node],
        };
        let index = nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| !Self::empty(node))
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let [decision] = index.as_slice() else {
            return None;
        };
        let mut prefix = nodes[..*decision].to_vec();
        let selected = nodes[*decision].clone();
        let suffix = nodes[decision + 1..].to_vec();
        prefix.retain(|node| Self::empty(node));
        Some((prefix, selected, suffix))
    }

    fn remove_terminal_continue(
        body: SemanticNode,
        control: SemanticLoopControl,
    ) -> Option<SemanticNode> {
        let mut nodes = match body {
            SemanticNode::Sequence(nodes) => nodes,
            node => vec![node],
        };
        let index = nodes.iter().rposition(|node| !Self::empty(node))?;
        Self::is_local_continue(&nodes[index], control).then_some(())?;
        nodes.remove(index);
        Some(SemanticNode::sequence(nodes))
    }

    fn is_local_break(node: &SemanticNode, control: SemanticLoopControl) -> bool {
        Self::single_leave(node).is_some_and(|leave| match control {
            SemanticLoopControl::Region(region) => {
                matches!(leave.kind, SemanticLeaveKind::Break) && leave.target == region
            }
            SemanticLoopControl::Label(label) => {
                matches!(leave.kind, SemanticLeaveKind::BreakLabel(target) if target == label)
            }
        })
    }

    fn is_local_continue(node: &SemanticNode, control: SemanticLoopControl) -> bool {
        Self::single_leave(node).is_some_and(|leave| match control {
            SemanticLoopControl::Region(region) => {
                matches!(leave.kind, SemanticLeaveKind::Continue) && leave.target == region
            }
            SemanticLoopControl::Label(label) => {
                matches!(leave.kind, SemanticLeaveKind::ContinueLabel(target) if target == label)
            }
        })
    }

    fn single_leave(node: &SemanticNode) -> Option<&crate::ir::SemanticLeave> {
        match node {
            SemanticNode::Leave(leave) if leave.cleanup.is_empty() => Some(leave),
            SemanticNode::Sequence(nodes) => {
                let mut meaningful = nodes.iter().filter(|node| !Self::empty(node));
                let leave = meaningful.next().and_then(Self::single_leave)?;
                meaningful.next().is_none().then_some(leave)
            }
            _ => None,
        }
    }

    fn empty(node: &SemanticNode) -> bool {
        match node {
            SemanticNode::Empty => true,
            SemanticNode::BasicBlock(block) => block.statements.is_empty(),
            SemanticNode::Sequence(nodes) => nodes.iter().all(Self::empty),
            _ => false,
        }
    }

    fn empty_blocks(root: &SemanticNode) -> Vec<SemanticNode> {
        let mut pending = vec![root];
        let mut blocks = Vec::new();
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::BasicBlock(block) if block.statements.is_empty() => {
                    blocks.push(node.clone())
                }
                SemanticNode::Sequence(nodes) => pending.extend(nodes.iter().rev()),
                SemanticNode::If {
                    then_node,
                    else_node,
                    ..
                } => {
                    if let Some(else_node) = else_node {
                        pending.push(else_node);
                    }
                    pending.push(then_node);
                }
                _ => {}
            }
        }
        blocks
    }
}
