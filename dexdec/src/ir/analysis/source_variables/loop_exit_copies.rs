//! Placement of Phi edge copies around structured loop exits.
//!
//! Sparse SSA destruction initially places copies on their exact CFG edges.
//! When normal loop completion and an early loop exit feed the same Phi, that
//! exact placement can require a lexical block label.  This analysis moves the
//! normal-edge copies into the loop preheader only when data-flow proves that
//! every early exit overwrites them and the move cannot expose a value inside
//! the loop.

use std::collections::BTreeSet;

use crate::ir::{
    InsnType, SemanticExpressionFacts, SemanticFoldError, SemanticFolder, SemanticLabel,
    SemanticLeaveKind, SemanticLoopControl, SemanticNode, SemanticStatement,
};

pub(super) struct LoopExitCopyPlacement;

impl LoopExitCopyPlacement {
    pub(super) fn apply(root: &mut SemanticNode) -> Result<(), SemanticFoldError> {
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = Self.fold_node(body)?;
        Ok(())
    }

    fn fold_node(body: SemanticNode) -> Result<SemanticNode, SemanticFoldError> {
        let mut placement = Self;
        placement.fold_node(body)
    }

    fn rewrite(label: SemanticLabel, body: SemanticNode) -> SemanticNode {
        let SemanticNode::Sequence(mut nodes) = body else {
            return SemanticNode::Label {
                label,
                body: Box::new(body),
            };
        };
        let references = LabelReferenceCount::of(&SemanticNode::Sequence(nodes.clone()), label);
        if references == 0 {
            return SemanticNode::sequence(nodes);
        }

        for loop_index in 0..nodes.len() {
            let Some(control) = Self::loop_control(&nodes[loop_index]) else {
                continue;
            };
            if LabelReferenceCount::of(&nodes[loop_index], label) != references {
                continue;
            }
            let continuation = SemanticNode::sequence(nodes[loop_index + 1..].iter().cloned());
            let Some(copies) = EdgeCopySet::analyze(&continuation) else {
                continue;
            };
            let empty_edge = copies.destinations.is_empty();
            let exit_definitions = empty_edge
                || ExitDefinitionProof::verify(&nodes[loop_index], label, &copies.destinations);
            let definition_proof =
                DefiniteDefinition::analyze(&nodes[loop_index], &copies.destinations);
            let definite_definitions = definition_proof.valid;
            let loop_facts = SemanticExpressionFacts::of_node(&nodes[loop_index]);
            let invariant_sources = copies
                .sources
                .iter()
                .all(|variable| loop_facts.definition_count(*variable) == 0);
            if !exit_definitions {
                continue;
            }
            if !definite_definitions || !invariant_sources {
                continue;
            }

            let mut retargeting = LoopExitRetargeting {
                source: label,
                target: control,
                count: 0,
            };
            let Ok(loop_node) = retargeting.fold_node(nodes[loop_index].clone()) else {
                continue;
            };
            if retargeting.count != references {
                continue;
            }

            let mut rewritten = nodes.drain(..loop_index).collect::<Vec<_>>();
            if !empty_edge {
                rewritten.push(continuation);
            }
            rewritten.push(loop_node);
            return SemanticNode::sequence(rewritten);
        }

        SemanticNode::Label {
            label,
            body: Box::new(SemanticNode::sequence(nodes)),
        }
    }

    fn loop_control(node: &SemanticNode) -> Option<SemanticLoopControl> {
        match node {
            SemanticNode::Loop { control, .. }
            | SemanticNode::For { control, .. }
            | SemanticNode::ForEach { control, .. } => Some(*control),
            _ => None,
        }
    }
}

struct DefiniteDefinition<'a> {
    tracked: &'a BTreeSet<u32>,
    valid: bool,
}

impl<'a> DefiniteDefinition<'a> {
    fn analyze(node: &SemanticNode, tracked: &'a BTreeSet<u32>) -> Self {
        let mut proof = Self {
            tracked,
            valid: true,
        };
        proof.transfer(node, BTreeSet::new());
        proof
    }

    fn transfer(&mut self, node: &SemanticNode, input: BTreeSet<u32>) -> BTreeSet<u32> {
        if !self.valid {
            return input;
        }
        match node {
            SemanticNode::Empty | SemanticNode::Leave(_) => input,
            SemanticNode::BasicBlock(block) => block
                .statements
                .iter()
                .fold(input, |state, statement| self.statement(statement, state)),
            SemanticNode::Sequence(nodes) => nodes
                .iter()
                .fold(input, |state, node| self.transfer(node, state)),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                self.read_predicate(condition, &input);
                let when_true = self.transfer(then_node, input.clone());
                let when_false = match else_node.as_deref() {
                    Some(node) => self.transfer(node, input),
                    None => input,
                };
                when_true.intersection(&when_false).copied().collect()
            }
            SemanticNode::Loop {
                test, body, kind, ..
            } => {
                let after_setup = self.transfer(&test.setup, input.clone());
                self.read_predicate(&test.condition, &after_setup);
                self.transfer(body, after_setup);
                if matches!(kind, crate::ir::SemanticLoopKind::PostTested) {
                    self.read_predicate(&test.condition, &input);
                }
                input
            }
            SemanticNode::For {
                init,
                condition,
                update,
                body,
                ..
            } => {
                let initialized = self.statement(init, input.clone());
                self.read_predicate(condition, &initialized);
                let iteration = self.transfer(body, initialized);
                self.statement(update, iteration);
                input
            }
            SemanticNode::ForEach {
                variable,
                iterable,
                body,
                ..
            } => {
                self.read_expression(iterable, &input);
                let mut iteration = input.clone();
                if let Some(variable) = variable.code_var {
                    iteration.insert(variable);
                }
                self.transfer(body, iteration);
                input
            }
            SemanticNode::Label { body, .. } => self.transfer(body, input),
            SemanticNode::Switch {
                selector, cases, ..
            } => {
                self.read_expression(selector, &input);
                let mut outputs = cases
                    .iter()
                    .map(|case| self.transfer(&case.body, input.clone()));
                let Some(mut output) = outputs.next() else {
                    return input;
                };
                for state in outputs {
                    output.retain(|variable| state.contains(variable));
                }
                output
            }
            SemanticNode::Try { .. } | SemanticNode::Synchronized { .. } => {
                self.valid = false;
                input
            }
        }
    }

    fn statement(
        &mut self,
        statement: &SemanticStatement,
        mut state: BTreeSet<u32>,
    ) -> BTreeSet<u32> {
        if let Some(value) = statement.value() {
            self.read_expression(value, &state);
        } else if let Some(operation) = statement.instruction_ref() {
            self.read_operation(operation, &state);
        }
        if let Some(variable) = statement
            .result()
            .as_ref()
            .and_then(|result| result.code_var)
        {
            state.insert(variable);
        }
        state
    }

    fn read_predicate(&mut self, predicate: &crate::ir::SemanticPredicate, state: &BTreeSet<u32>) {
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                crate::ir::SemanticPredicate::Test(instruction) => {
                    self.read_operation(instruction, state)
                }
                crate::ir::SemanticPredicate::Not(inner) => pending.push(inner),
                crate::ir::SemanticPredicate::And(terms)
                | crate::ir::SemanticPredicate::Or(terms) => pending.extend(terms),
                crate::ir::SemanticPredicate::True | crate::ir::SemanticPredicate::False => {}
            }
        }
    }

    fn read_operation(&mut self, operation: &crate::ir::SemanticOperation, state: &BTreeSet<u32>) {
        let Ok(arguments) = operation.evaluation_operands() else {
            self.valid = false;
            return;
        };
        for argument in arguments {
            self.read_expression(argument, state);
        }
    }

    fn read_expression(
        &mut self,
        expression: &crate::ir::SemanticExpression,
        state: &BTreeSet<u32>,
    ) {
        match expression {
            crate::ir::SemanticExpression::Register(register) => {
                let mut facts = BTreeSet::new();
                facts.extend(register.code_var);
                if facts
                    .intersection(self.tracked)
                    .any(|variable| !state.contains(variable))
                {
                    self.valid = false;
                }
                return;
            }
            crate::ir::SemanticExpression::Operation(operation) => {
                self.read_operation(operation, state);
                return;
            }
            crate::ir::SemanticExpression::Select {
                condition,
                when_true,
                when_false,
            } => {
                self.read_predicate(condition, state);
                self.read_expression(when_true, state);
                self.read_expression(when_false, state);
            }
            crate::ir::SemanticExpression::Literal(_) => return,
        }
    }
}

impl SemanticFolder for LoopExitCopyPlacement {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Label { label, body } => Self::rewrite(label, *body),
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}

struct EdgeCopySet {
    destinations: BTreeSet<u32>,
    sources: BTreeSet<u32>,
}

impl EdgeCopySet {
    fn analyze(node: &SemanticNode) -> Option<Self> {
        let mut copies = Self {
            destinations: BTreeSet::new(),
            sources: BTreeSet::new(),
        };
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            match node {
                SemanticNode::Empty => {}
                SemanticNode::Sequence(nodes) => pending.extend(nodes),
                SemanticNode::BasicBlock(block) => {
                    for statement in &block.statements {
                        copies.record(statement)?;
                    }
                }
                _ => return None,
            }
        }
        Some(copies)
    }

    fn record(&mut self, statement: &SemanticStatement) -> Option<()> {
        let instruction = statement.instruction_ref()?;
        if instruction.insn_type != InsnType::Move || !instruction.payload.edge_copy {
            return None;
        }
        let destination = instruction.result.as_ref()?.code_var?;
        let source = instruction.operands().first()?;
        if !Self::constant(source) {
            let source = source.as_register()?.code_var?;
            self.sources.insert(source);
        }
        self.destinations.insert(destination);
        Some(())
    }

    fn constant(argument: &crate::ir::SemanticExpression) -> bool {
        match argument {
            crate::ir::SemanticExpression::Literal(_) => true,
            crate::ir::SemanticExpression::Operation(instruction) => {
                matches!(instruction.insn_type, InsnType::Const | InsnType::ConstStr)
            }
            crate::ir::SemanticExpression::Register(_)
            | crate::ir::SemanticExpression::Select { .. } => false,
        }
    }
}

struct ExitDefinitionProof {
    target: SemanticLabel,
    required: BTreeSet<u32>,
    exits: usize,
    valid: bool,
}

impl ExitDefinitionProof {
    fn verify(node: &SemanticNode, target: SemanticLabel, required: &BTreeSet<u32>) -> bool {
        let mut proof = Self {
            target,
            required: required.clone(),
            exits: 0,
            valid: true,
        };
        proof.transfer(node, BTreeSet::new());
        proof.valid && proof.exits != 0
    }

    fn transfer(&mut self, node: &SemanticNode, input: BTreeSet<u32>) -> Option<BTreeSet<u32>> {
        if !self.valid {
            return None;
        }
        match node {
            SemanticNode::Empty => Some(input),
            SemanticNode::BasicBlock(block) => {
                let mut output = input;
                for statement in &block.statements {
                    if let Some(variable) = statement.result().and_then(|result| result.code_var) {
                        output.insert(variable);
                    }
                }
                Some(output)
            }
            SemanticNode::Sequence(nodes) => {
                let mut state = Some(input);
                for node in nodes {
                    let Some(current) = state.take() else {
                        break;
                    };
                    state = self.transfer(node, current);
                }
                state
            }
            SemanticNode::If {
                then_node,
                else_node,
                ..
            } => {
                let when_true = self.transfer(then_node, input.clone());
                let when_false = match else_node {
                    Some(node) => self.transfer(node, input),
                    None => Some(input),
                };
                Self::meet(when_true, when_false)
            }
            SemanticNode::Loop { body, .. }
            | SemanticNode::For { body, .. }
            | SemanticNode::ForEach { body, .. } => {
                self.transfer(body, input.clone());
                Some(input)
            }
            SemanticNode::Label { body, .. } => self.transfer(body, input),
            SemanticNode::Leave(leave) if matches!(leave.kind, SemanticLeaveKind::BreakLabel(label) if label == self.target) =>
            {
                self.exits += 1;
                self.valid &= self.required.is_subset(&input) && leave.cleanup.is_empty();
                None
            }
            SemanticNode::Leave(_) => None,
            SemanticNode::Try { .. }
            | SemanticNode::Synchronized { .. }
            | SemanticNode::Switch { .. } => {
                self.valid = false;
                None
            }
        }
    }

    fn meet(left: Option<BTreeSet<u32>>, right: Option<BTreeSet<u32>>) -> Option<BTreeSet<u32>> {
        match (left, right) {
            (Some(left), Some(right)) => Some(left.intersection(&right).copied().collect()),
            (Some(state), None) | (None, Some(state)) => Some(state),
            (None, None) => None,
        }
    }
}

struct LabelReferenceCount {
    target: SemanticLabel,
    count: usize,
}

impl LabelReferenceCount {
    fn of(node: &SemanticNode, target: SemanticLabel) -> usize {
        let mut counter = Self { target, count: 0 };
        crate::ir::SemanticVisitor::visit_node(&mut counter, node);
        counter.count
    }
}

impl crate::ir::SemanticVisitor for LabelReferenceCount {
    fn enter_node(&mut self, node: &SemanticNode) {
        if matches!(node, SemanticNode::Leave(leave) if matches!(leave.kind, SemanticLeaveKind::BreakLabel(label) if label == self.target))
        {
            self.count += 1;
        }
    }
}

struct LoopExitRetargeting {
    source: SemanticLabel,
    target: SemanticLoopControl,
    count: usize,
}

impl SemanticFolder for LoopExitRetargeting {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        Ok(match node {
            SemanticNode::Leave(mut leave) if matches!(leave.kind, SemanticLeaveKind::BreakLabel(label) if label == self.source) =>
            {
                self.count += 1;
                match self.target {
                    SemanticLoopControl::Region(region) => {
                        leave.kind = SemanticLeaveKind::Break;
                        leave.target = region;
                    }
                    SemanticLoopControl::Label(label) => {
                        leave.kind = SemanticLeaveKind::BreakLabel(label);
                    }
                }
                SemanticNode::Leave(leave)
            }
            SemanticNode::Sequence(nodes) => SemanticNode::sequence(nodes),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => SemanticNode::branch(
                condition.into_inner(),
                *then_node,
                else_node.map(|node| *node),
            ),
            node => node,
        })
    }
}
