//! Source-language evaluation order for instruction trees.

use crate::ir::{InsnArg, InsnNode, InsnType, InstructionId};

use super::InstructionEffects;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceEvaluationError {
    MalformedConstructor(u32),
    InvalidArity {
        instruction: InsnType,
        offset: u32,
        actual: usize,
    },
}

impl std::fmt::Display for SourceEvaluationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedConstructor(offset) => {
                write!(formatter, "constructor at {offset:#x} has no receiver")
            }
            Self::InvalidArity {
                instruction,
                offset,
                actual,
            } => write!(
                formatter,
                "{instruction:?} at {offset:#x} has {actual} operands for source evaluation"
            ),
        }
    }
}

impl std::error::Error for SourceEvaluationError {}

pub struct SourceEvaluation;

impl SourceEvaluation {
    pub fn arguments(instruction: &InsnNode) -> Result<Vec<&InsnArg>, SourceEvaluationError> {
        let arity = || SourceEvaluationError::InvalidArity {
            instruction: instruction.insn_type,
            offset: instruction.offset,
            actual: instruction.args.len(),
        };
        Ok(match instruction.insn_type {
            InsnType::Constructor => instruction
                .args
                .get(1..)
                .ok_or(SourceEvaluationError::MalformedConstructor(
                    instruction.offset,
                ))?
                .iter()
                .collect(),
            InsnType::Iput => {
                if instruction.args.len() != 2 {
                    return Err(arity());
                }
                vec![&instruction.args[1], &instruction.args[0]]
            }
            InsnType::Aput => {
                if instruction.args.len() != 3 {
                    return Err(arity());
                }
                vec![
                    &instruction.args[1],
                    &instruction.args[2],
                    &instruction.args[0],
                ]
            }
            InsnType::CompoundAssign => {
                let target = instruction
                    .payload
                    .compound_target
                    .as_ref()
                    .ok_or_else(arity)?;
                let value = instruction.args.last().ok_or_else(arity)?;
                vec![target, value]
            }
            _ => {
                let mut arguments = instruction.args.iter().collect::<Vec<_>>();
                arguments.extend(instruction.payload.compound_target.iter());
                arguments
            }
        })
    }

    pub fn effects_before(
        root: &InsnNode,
        target: InstructionId,
    ) -> Result<Option<InstructionEffects>, SourceEvaluationError> {
        if root.id == target {
            return Ok(Some(InstructionEffects::PURE));
        }
        let mut effects = InstructionEffects::PURE;
        let mut pending = vec![EvaluationTask::Effect(root)];
        pending.extend(
            Self::arguments(root)?
                .into_iter()
                .rev()
                .map(EvaluationTask::Argument),
        );
        while let Some(task) = pending.pop() {
            match task {
                EvaluationTask::Argument(InsnArg::Wrapped(instruction)) => {
                    if instruction.id == target {
                        return Ok(Some(effects));
                    }
                    pending.push(EvaluationTask::Effect(instruction));
                    pending.extend(
                        Self::arguments(instruction)?
                            .into_iter()
                            .rev()
                            .map(EvaluationTask::Argument),
                    );
                }
                EvaluationTask::Argument(InsnArg::Reg(_) | InsnArg::Lit(_)) => {}
                EvaluationTask::Effect(instruction) => {
                    effects = effects.join(InstructionEffects::of(instruction));
                }
            }
        }
        Ok(None)
    }
}

enum EvaluationTask<'a> {
    Argument(&'a InsnArg),
    Effect(&'a InsnNode),
}
