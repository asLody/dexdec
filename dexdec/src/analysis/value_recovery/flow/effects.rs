//! Location-sensitive effects used by semantic value scheduling.

use std::collections::BTreeSet;

use crate::ir::{
    analysis::InstructionEffects, InsnType, SemanticExpression, SemanticOperation,
    SemanticStatement, SemanticStatementKind,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum MemoryLocation {
    Field(u32),
    Array,
    UnknownHeap,
}

impl MemoryLocation {
    fn may_alias(self, other: Self) -> bool {
        self == other || matches!(self, Self::UnknownHeap) || matches!(other, Self::UnknownHeap)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct EffectSummary {
    instruction: InstructionEffects,
    reads: BTreeSet<MemoryLocation>,
    writes: BTreeSet<MemoryLocation>,
}

impl EffectSummary {
    pub(super) fn pure() -> Self {
        Self::default()
    }

    pub(super) fn synchronization() -> Self {
        Self {
            instruction: InstructionEffects::SYNCHRONIZATION,
            ..Self::default()
        }
    }

    pub(super) fn direct(operation: &SemanticOperation) -> Self {
        let instruction = operation.direct_effects();
        let mut summary = Self {
            instruction,
            ..Self::default()
        };
        match operation.insn_type {
            InsnType::Iget | InsnType::Sget => summary.read(Self::field_location(operation)),
            InsnType::Iput | InsnType::Sput => summary.write(Self::field_location(operation)),
            InsnType::ArrayLength | InsnType::Aget => summary.read(MemoryLocation::Array),
            InsnType::Aput | InsnType::FillArray => summary.write(MemoryLocation::Array),
            InsnType::CompoundAssign => {
                summary.read(MemoryLocation::UnknownHeap);
                summary.write(MemoryLocation::UnknownHeap);
            }
            InsnType::StringConcat
            | InsnType::FilledNewArray
            | InsnType::NewArray
            | InsnType::NewInstance
            | InsnType::Invoke
            | InsnType::MoveResult
            | InsnType::Constructor => {
                summary.read(MemoryLocation::UnknownHeap);
                summary.write(MemoryLocation::UnknownHeap);
            }
            _ => {}
        }
        if instruction.reads_memory() && summary.reads.is_empty() && instruction.calls() {
            summary.read(MemoryLocation::UnknownHeap);
        }
        if instruction.writes_memory() && summary.writes.is_empty() && instruction.calls() {
            summary.write(MemoryLocation::UnknownHeap);
        }
        summary
    }

    pub(super) fn expression(expression: &SemanticExpression) -> Self {
        let mut summary = Self::pure();
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                SemanticExpression::Register(_) | SemanticExpression::Literal(_) => {}
                SemanticExpression::Operation(operation) => {
                    summary = summary.join(Self::direct(operation));
                    pending.extend(operation.operands().iter().rev());
                    pending.extend(operation.compound_target());
                }
                SemanticExpression::Select {
                    condition,
                    when_true,
                    when_false,
                } => {
                    summary = summary.join(Self::predicate(condition).without_control());
                    pending.push(when_false);
                    pending.push(when_true);
                }
            }
        }
        summary
    }

    pub(super) fn operation(operation: &SemanticOperation) -> Self {
        let mut summary = Self::direct(operation);
        for operand in operation.operands() {
            summary = summary.join(Self::expression(operand));
        }
        if let Some(target) = operation.compound_target() {
            summary = summary.join(Self::expression(target));
        }
        summary
    }

    pub(super) fn operation_ignoring_edge_copy(operation: &SemanticOperation) -> Self {
        let mut operation = operation.clone();
        operation.payload.edge_copy = false;
        Self::operation(&operation)
    }

    pub(super) fn statement(statement: &SemanticStatement) -> Self {
        match &statement.kind {
            SemanticStatementKind::Instruction(operation) if operation.payload.edge_copy => {
                Self::operation_ignoring_edge_copy(operation)
            }
            SemanticStatementKind::Instruction(operation) => Self::operation(operation),
            SemanticStatementKind::Definition { value, .. } => {
                match value.as_operation().filter(|value| value.payload.edge_copy) {
                    Some(operation) => Self::operation_ignoring_edge_copy(operation),
                    None => Self::expression(value),
                }
            }
        }
    }

    pub(super) fn predicate(predicate: &crate::ir::SemanticPredicate) -> Self {
        let mut summary = Self::pure();
        let mut pending = vec![predicate];
        while let Some(predicate) = pending.pop() {
            match predicate {
                crate::ir::SemanticPredicate::Test(operation) => {
                    summary = summary.join(Self::operation(operation));
                }
                crate::ir::SemanticPredicate::Not(inner) => pending.push(inner),
                crate::ir::SemanticPredicate::And(terms)
                | crate::ir::SemanticPredicate::Or(terms) => pending.extend(terms),
                crate::ir::SemanticPredicate::True | crate::ir::SemanticPredicate::False => {}
            }
        }
        summary
    }

    pub(super) fn join(mut self, other: Self) -> Self {
        self.instruction = self.instruction.join(other.instruction);
        self.reads.extend(other.reads);
        self.writes.extend(other.writes);
        self
    }

    pub(super) fn without_control(mut self) -> Self {
        self.instruction = self.instruction.without_control();
        self
    }

    pub(super) fn is_pure(&self) -> bool {
        self.instruction.is_pure()
    }

    pub(super) fn can_relocate(&self) -> bool {
        self.instruction.can_relocate()
    }

    pub(super) fn can_predicate(&self) -> bool {
        self.instruction.can_predicate()
    }

    pub(super) fn conflicts_with(&self, other: &Self) -> bool {
        if self.is_pure() || other.is_pure() {
            return false;
        }
        if self.instruction.controls()
            || other.instruction.controls()
            || self.instruction.synchronizes()
            || other.instruction.synchronizes()
            || self.instruction.calls()
            || other.instruction.calls()
            || (self.instruction.may_throw() && other.instruction.may_throw())
        {
            return true;
        }
        self.writes.iter().any(|write| {
            other
                .reads
                .iter()
                .chain(&other.writes)
                .any(|other| write.may_alias(*other))
        }) || other.writes.iter().any(|write| {
            self.reads
                .iter()
                .chain(&self.writes)
                .any(|other| write.may_alias(*other))
        })
    }

    fn read(&mut self, location: MemoryLocation) {
        self.reads.insert(location);
    }

    fn write(&mut self, location: MemoryLocation) {
        self.writes.insert(location);
    }

    fn field_location(operation: &SemanticOperation) -> MemoryLocation {
        operation
            .payload
            .field_index
            .map(MemoryLocation::Field)
            .unwrap_or(MemoryLocation::UnknownHeap)
    }
}
