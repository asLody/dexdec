//! Lexical label hygiene for cloned semantic regions.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    BlockId, SemanticFoldError, SemanticFolder, SemanticLabel, SemanticLabelKind,
    SemanticLeaveKind, SemanticLoopControl, SemanticNode, SemanticVisitor,
};

/// Alpha-renames bindings duplicated by multi-entry and shared-handler
/// contraction. Labels are lexical identities, so cloning a bound subtree
/// must create fresh identities just like cloning an SSA scope.
pub(super) struct LexicalLabels {
    duplicates: BTreeSet<SemanticLabel>,
    used: BTreeSet<SemanticLabel>,
    used_blocks: BTreeSet<BlockId>,
    next_block: u32,
}

impl LexicalLabels {
    pub(super) fn uniquify(root: SemanticNode) -> Result<SemanticNode, SemanticFoldError> {
        let mut definitions = LabelDefinitions::default();
        definitions.visit_node(&root);
        let duplicates = definitions
            .counts
            .iter()
            .filter_map(|(label, count)| (*count > 1).then_some(*label))
            .collect::<BTreeSet<_>>();
        let mut root = if duplicates.is_empty() {
            root
        } else {
            Self {
                duplicates,
                used: definitions.counts.into_keys().collect(),
                next_block: definitions
                    .used_blocks
                    .last()
                    .map(|block| block.raw().wrapping_add(1))
                    .unwrap_or_default(),
                used_blocks: definitions.used_blocks,
            }
            .fold_node(root)?
        };

        let mut unique = LabelDefinitions::default();
        unique.visit_node(&root);
        for label in unique.counts.into_iter().filter_map(|(label, count)| {
            (count == 1 && label.kind == SemanticLabelKind::Block).then_some(label)
        }) {
            root = LexicalLabelScope::repair(root, label)?;
        }
        Ok(root)
    }

    pub(super) fn escaped_loop(root: &SemanticNode) -> Option<SemanticLabel> {
        let mut definitions = LabelDefinitions::default();
        definitions.visit_node(root);
        let loop_labels = definitions
            .counts
            .into_keys()
            .filter(|label| label.kind == SemanticLabelKind::Loop)
            .collect::<BTreeSet<_>>();
        let mut scopes = LoopLabelScopes {
            definitions: loop_labels,
            active: BTreeMap::new(),
            escaped: None,
        };
        scopes.visit_node(root);
        scopes.escaped
    }

    fn binding(node: &SemanticNode) -> Option<SemanticLabel> {
        match node {
            SemanticNode::Loop {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::For {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::ForEach {
                control: SemanticLoopControl::Label(label),
                ..
            }
            | SemanticNode::Label { label, .. } => Some(*label),
            _ => None,
        }
    }

    fn fresh(&mut self, template: SemanticLabel) -> SemanticLabel {
        loop {
            let block = BlockId::new(self.next_block);
            self.next_block = self.next_block.wrapping_add(1);
            if !self.used_blocks.insert(block) {
                continue;
            }
            let label = SemanticLabel { block, ..template };
            if self.used.insert(label) {
                return label;
            }
        }
    }
}

struct LoopLabelScopes {
    definitions: BTreeSet<SemanticLabel>,
    active: BTreeMap<SemanticLabel, usize>,
    escaped: Option<SemanticLabel>,
}

impl SemanticVisitor for LoopLabelScopes {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let Some(label) =
            LexicalLabels::binding(node).filter(|label| label.kind == SemanticLabelKind::Loop)
        {
            *self.active.entry(label).or_default() += 1;
        }
        if let SemanticNode::Leave(leave) = node {
            let label = match leave.kind {
                SemanticLeaveKind::BreakLabel(label) | SemanticLeaveKind::ContinueLabel(label) => {
                    label
                }
                _ => return,
            };
            if self.definitions.contains(&label)
                && !self.active.contains_key(&label)
                && self.escaped.is_none()
            {
                self.escaped = Some(label);
            }
        }
    }

    fn exit_node(&mut self, node: &SemanticNode) {
        let Some(label) =
            LexicalLabels::binding(node).filter(|label| label.kind == SemanticLabelKind::Loop)
        else {
            return;
        };
        let Some(depth) = self.active.get_mut(&label) else {
            return;
        };
        *depth -= 1;
        if *depth == 0 {
            self.active.remove(&label);
        }
    }
}

/// Places a block-label binding at the lowest semantic-tree ancestor that
/// contains both its definition and every transfer targeting it.
struct LexicalLabelScope {
    label: SemanticLabel,
    definition: Option<Vec<usize>>,
    references: Vec<Vec<usize>>,
}

impl LexicalLabelScope {
    fn repair(root: SemanticNode, label: SemanticLabel) -> Result<SemanticNode, SemanticFoldError> {
        let mut scope = Self {
            label,
            definition: None,
            references: Vec::new(),
        };
        scope.analyze(&root);
        let Some(definition) = scope.definition else {
            return Ok(root);
        };
        let mut binding = definition.clone();
        for reference in &scope.references {
            let common = binding
                .iter()
                .zip(reference)
                .take_while(|(left, right)| left == right)
                .count();
            binding.truncate(common);
        }
        LabelScopeRewrite {
            label,
            definition,
            binding,
            stack: Vec::new(),
        }
        .fold_node(root)
    }

    fn analyze(&mut self, root: &SemanticNode) {
        let mut pending = vec![(root, Vec::new())];
        while let Some((node, path)) = pending.pop() {
            match node {
                SemanticNode::Label { label, .. } if *label == self.label => {
                    self.definition = Some(path.clone());
                }
                SemanticNode::Leave(leave)
                    if matches!(
                        &leave.kind,
                        SemanticLeaveKind::BreakLabel(label)
                            | SemanticLeaveKind::ContinueLabel(label)
                            if *label == self.label
                    ) =>
                {
                    self.references.push(path.clone());
                }
                _ => {}
            }
            Self::push_children(node, &path, &mut pending);
        }
    }

    fn push_children<'a>(
        node: &'a SemanticNode,
        path: &[usize],
        pending: &mut Vec<(&'a SemanticNode, Vec<usize>)>,
    ) {
        let mut push = |child: &'a SemanticNode, index: usize| {
            let mut child_path = path.to_vec();
            child_path.push(index);
            pending.push((child, child_path));
        };
        match node {
            SemanticNode::Sequence(children) => {
                for (index, child) in children.iter().enumerate().rev() {
                    push(child, index);
                }
            }
            SemanticNode::If {
                then_node,
                else_node,
                ..
            } => {
                if let Some(else_node) = else_node {
                    push(else_node, 1);
                }
                push(then_node, 0);
            }
            SemanticNode::Loop { test, body, .. } => {
                push(body, 1);
                push(&test.setup, 0);
            }
            SemanticNode::For { body, .. }
            | SemanticNode::ForEach { body, .. }
            | SemanticNode::Synchronized { body, .. }
            | SemanticNode::Label { body, .. } => push(body, 0),
            SemanticNode::Switch { cases, .. } => {
                for (index, case) in cases.iter().enumerate().rev() {
                    push(&case.body, index);
                }
            }
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                if let Some(finally) = finally {
                    push(&finally.body, catches.len() + 1);
                }
                for (index, catch) in catches.iter().enumerate().rev() {
                    push(&catch.body, index + 1);
                }
                push(body, 0);
            }
            SemanticNode::Empty | SemanticNode::BasicBlock(_) | SemanticNode::Leave(_) => {}
        }
    }
}

struct LabelScopeRewrite {
    label: SemanticLabel,
    definition: Vec<usize>,
    binding: Vec<usize>,
    stack: Vec<PathFrame>,
}

struct PathFrame {
    path: Vec<usize>,
    next_child: usize,
}

impl SemanticFolder for LabelScopeRewrite {
    type Error = SemanticFoldError;

    fn enter_node(&mut self, _node: &SemanticNode) {
        let path = match self.stack.last_mut() {
            Some(parent) => {
                let index = parent.next_child;
                parent.next_child += 1;
                let mut path = parent.path.clone();
                path.push(index);
                path
            }
            None => Vec::new(),
        };
        self.stack.push(PathFrame {
            path,
            next_child: 0,
        });
    }

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let path = self
            .stack
            .pop()
            .ok_or(SemanticFoldError::MalformedWorkStack)?
            .path;
        let node = if path == self.definition {
            match node {
                SemanticNode::Label { label, body } if label == self.label => *body,
                node => node,
            }
        } else {
            node
        };
        Ok(if path == self.binding {
            SemanticNode::Label {
                label: self.label,
                body: Box::new(node),
            }
        } else {
            node
        })
    }
}

impl SemanticFolder for LexicalLabels {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        let Some(label) = Self::binding(&node).filter(|label| self.duplicates.contains(label))
        else {
            return Ok(node);
        };
        let replacement = self.fresh(label);
        LabelReferenceRewrite { label, replacement }.fold_node(node)
    }
}

#[derive(Default)]
struct LabelDefinitions {
    counts: BTreeMap<SemanticLabel, usize>,
    used_blocks: BTreeSet<BlockId>,
}

impl SemanticVisitor for LabelDefinitions {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::BasicBlock(block) = node {
            self.used_blocks.insert(block.id);
        }
        if let Some(label) = LexicalLabels::binding(node) {
            *self.counts.entry(label).or_default() += 1;
            self.used_blocks.insert(label.block);
        }
    }
}

struct LabelReferenceRewrite {
    label: SemanticLabel,
    replacement: SemanticLabel,
}

impl SemanticFolder for LabelReferenceRewrite {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        match &mut node {
            SemanticNode::Loop { control, .. }
            | SemanticNode::For { control, .. }
            | SemanticNode::ForEach { control, .. } => {
                if *control == SemanticLoopControl::Label(self.label) {
                    *control = SemanticLoopControl::Label(self.replacement);
                }
            }
            SemanticNode::Label { label, .. } if *label == self.label => {
                *label = self.replacement;
            }
            SemanticNode::Leave(leave) => match &mut leave.kind {
                SemanticLeaveKind::BreakLabel(label) | SemanticLeaveKind::ContinueLabel(label)
                    if *label == self.label =>
                {
                    *label = self.replacement;
                }
                _ => {}
            },
            _ => {}
        }
        Ok(node)
    }
}
