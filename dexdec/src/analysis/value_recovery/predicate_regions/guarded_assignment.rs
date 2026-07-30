//! Guarded-assignment recovery for self-selecting definitions.
//!
//! Gated-Phi recovery materializes a merge as one selection over the reaching
//! conditions of the join. Source-variable allocation then coalesces the inputs
//! of that merge into a single local, so every arm that carried an input the
//! destination already holds degenerates into a read of the destination itself.
//!
//! Such an arm stores the value that already reaches the statement, so the write
//! it describes is unobservable. Lowering the selection back to control flow,
//! with those arms as empty branches, recovers the regions the merge came from
//! instead of leaving each one to re-derive its predicate inside an expression.

use crate::ir::{
    semantic::SemanticCompletion, BlockId, SemanticBlock, SemanticExpression, SemanticNode,
    SemanticPredicate, SemanticStatement,
};

/// A definition whose selection tree reads its own destination.
pub(super) struct GuardedAssignment {
    block: BlockId,
    statement: SemanticStatement,
    variable: u32,
}

impl GuardedAssignment {
    /// Rewrites `statement` into the regions its selection describes.
    ///
    /// The lowering is exact rather than heuristic: every condition and every
    /// surviving arm keeps its position in the original evaluation order and
    /// appears exactly once, so effects are preserved in number and in order
    /// without requiring any of them to be pure. Only the stores that were
    /// already unobservable disappear.
    ///
    /// Returns the statement unchanged when it holds no self-selecting arm, or
    /// when the recovered regions would not complete like the original.
    pub(super) fn recover(
        statement: SemanticStatement,
        block: BlockId,
    ) -> Result<SemanticNode, SemanticStatement> {
        let Some(variable) = statement.result().and_then(|result| result.code_var) else {
            return Err(statement);
        };
        if statement.value().is_none() {
            return Err(statement);
        }
        Self {
            block,
            statement,
            variable,
        }
        .lower()
    }

    fn lower(self) -> Result<SemanticNode, SemanticStatement> {
        let Some(value) = self.statement.value() else {
            return Err(self.statement);
        };
        if !self.selects_destination(value) {
            return Err(self.statement);
        }
        let Some(recovered) = self.regions(value) else {
            return Err(self.statement);
        };
        // Guarding a store whose value cannot complete normally would give the
        // statement a normal exit it never had.
        if SemanticCompletion::analyze(&self.assignment(value.clone()))
            != SemanticCompletion::analyze(&recovered)
        {
            return Err(self.statement);
        }
        Ok(recovered)
    }

    /// Lowers one selection arm, mapping reads of the destination to no regions.
    ///
    /// Only the spine that reaches a self-selecting arm becomes control flow.
    /// A subtree that stores on every path already says so as an expression,
    /// and expanding it would trade one conditional value for a branch tree.
    fn regions(&self, value: &SemanticExpression) -> Option<SemanticNode> {
        if self.reads_destination(value) {
            return Some(SemanticNode::Empty);
        }
        // A read below an operation is an operand rather than a stored value,
        // so such an arm also keeps its expression unchanged.
        if !self.selects_destination(value) {
            return Some(self.assignment(value.clone()));
        }
        let SemanticExpression::Select {
            condition,
            when_true,
            when_false,
        } = value
        else {
            return Some(self.assignment(value.clone()));
        };
        let when_true = self.regions(when_true)?;
        let when_false = self.regions(when_false)?;
        // Both arms restore the destination, so the selection stores nothing.
        // Dropping it would also drop the evaluation of its condition.
        if matches!(when_true, SemanticNode::Empty) && matches!(when_false, SemanticNode::Empty) {
            return None;
        }
        Some(Self::merge_guards(SemanticNode::branch(
            condition.clone(),
            when_true,
            Some(when_false),
        )))
    }

    /// Collapses a guard over a lone guard into one conjunction.
    ///
    /// Consecutive self-selecting arms otherwise nest one region per arm, which
    /// states the same reaching condition across several lines.
    fn merge_guards(node: SemanticNode) -> SemanticNode {
        let SemanticNode::If {
            condition,
            then_node,
            else_node: None,
        } = node
        else {
            return node;
        };
        let SemanticNode::If {
            condition: inner,
            then_node: body,
            else_node: None,
        } = *then_node
        else {
            return SemanticNode::If {
                condition,
                then_node,
                else_node: None,
            };
        };
        SemanticNode::guard(
            Self::conjunction(condition.into_inner(), inner.into_inner()),
            *body,
        )
    }

    fn conjunction(left: SemanticPredicate, right: SemanticPredicate) -> SemanticPredicate {
        let mut terms = match left {
            SemanticPredicate::And(terms) => terms,
            left => vec![left],
        };
        match right {
            SemanticPredicate::And(inner) => terms.extend(inner),
            right => terms.push(right),
        }
        SemanticPredicate::And(terms)
    }

    /// Builds the store this arm performs.
    ///
    /// The destination is no longer defined on every path reaching its uses, so
    /// it is a write to the source variable rather than a value of its own.
    /// Dropping the SSA version keeps value-keyed analyses from typing the
    /// variable by one arm instead of joining every definition.
    fn assignment(&self, value: SemanticExpression) -> SemanticNode {
        let mut statement = self.statement.clone();
        statement.site = None;
        if let Some(target) = statement.value_mut() {
            *target = value;
        }
        if let Some(result) = statement.result_mut() {
            result.ssa_version = None;
        }
        SemanticNode::BasicBlock(SemanticBlock {
            id: self.block,
            statements: vec![statement],
        })
    }

    fn selects_destination(&self, value: &SemanticExpression) -> bool {
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            let SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } = value
            else {
                continue;
            };
            if self.reads_destination(when_true) || self.reads_destination(when_false) {
                return true;
            }
            pending.extend([when_true.as_ref(), when_false.as_ref()]);
        }
        false
    }

    fn reads_destination(&self, value: &SemanticExpression) -> bool {
        matches!(
            value,
            SemanticExpression::Register(register) if register.code_var == Some(self.variable)
        )
    }
}
