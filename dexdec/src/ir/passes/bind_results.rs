//! Bind DEX `move-result` pseudo-definitions to their instruction-stream producer.

use std::collections::BTreeMap;

use crate::ir::analysis::InsnPosition;
use crate::ir::{ArgType, BlockId, InsnNode, InsnType, MemberReference, RegisterArg, CFG};

use super::{Pass, PassResult};

#[derive(Debug, Clone)]
struct ResultBinding {
    producer: InsnPosition,
    pseudo: InsnPosition,
    value: RegisterArg,
}

struct ResultBindingAnalysis;

#[derive(Debug)]
pub enum ResultBindingError {
    MissingInstruction(InsnPosition),
    MissingProducer(u32),
    InvalidProducer { offset: u32, instruction: InsnType },
    NonLinearFallthrough(u32),
    NonAdjacent(u32),
    MissingDestination(u32),
    MissingReference(u32),
    InvalidReferenceKind(u32),
    VoidResult(u32),
    MissingBlock(BlockId),
}

impl std::fmt::Display for ResultBindingError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingInstruction(position) => {
                write!(formatter, "missing instruction at {position:?}")
            }
            Self::MissingProducer(offset) => {
                write!(formatter, "move-result at {offset} has no producer")
            }
            Self::InvalidProducer {
                offset,
                instruction,
            } => write!(
                formatter,
                "move-result at {offset} follows {instruction:?}, not a result producer"
            ),
            Self::NonLinearFallthrough(offset) => write!(
                formatter,
                "move-result at {offset} is not on the producer fallthrough edge"
            ),
            Self::NonAdjacent(offset) => {
                write!(
                    formatter,
                    "move-result at {offset} is not adjacent to its producer"
                )
            }
            Self::MissingDestination(offset) => {
                write!(formatter, "move-result at {offset} has no destination")
            }
            Self::MissingReference(offset) => {
                write!(
                    formatter,
                    "result producer at {offset} has no method reference"
                )
            }
            Self::InvalidReferenceKind(offset) => {
                write!(
                    formatter,
                    "result producer at {offset} has a non-method reference"
                )
            }
            Self::VoidResult(offset) => {
                write!(
                    formatter,
                    "void producer at {offset} is followed by move-result"
                )
            }
            Self::MissingBlock(block) => write!(formatter, "missing result block {block}"),
        }
    }
}

impl std::error::Error for ResultBindingError {}

impl ResultBindingAnalysis {
    fn analyze(cfg: &CFG) -> Result<Vec<ResultBinding>, ResultBindingError> {
        let mut order = cfg
            .blocks
            .values()
            .flat_map(|block| {
                block
                    .insns
                    .iter()
                    .enumerate()
                    .map(move |(index, instruction)| {
                        (
                            instruction.offset,
                            InsnPosition {
                                block: block.id,
                                index,
                            },
                        )
                    })
            })
            .collect::<Vec<_>>();
        order.sort_by_key(|(offset, position)| (*offset, position.block, position.index));

        let mut bindings = Vec::new();
        for (stream_index, (_, pseudo)) in order.iter().enumerate() {
            let instruction = Self::instruction(cfg, *pseudo)?;
            if instruction.insn_type != InsnType::MoveResult {
                continue;
            }
            let (_, producer) = stream_index
                .checked_sub(1)
                .and_then(|index| order.get(index))
                .ok_or(ResultBindingError::MissingProducer(instruction.offset))?;
            let producer_instruction = Self::instruction(cfg, *producer)?;
            if !matches!(
                producer_instruction.insn_type,
                InsnType::Invoke | InsnType::FilledNewArray
            ) {
                return Err(ResultBindingError::InvalidProducer {
                    offset: instruction.offset,
                    instruction: producer_instruction.insn_type,
                });
            }
            if producer.block != pseudo.block {
                let linear =
                    cfg.successors_with_kind(producer.block)
                        .iter()
                        .any(|(target, kind)| {
                            *target == pseudo.block && *kind == crate::ir::EdgeKind::Normal
                        });
                if !linear {
                    return Err(ResultBindingError::NonLinearFallthrough(instruction.offset));
                }
            } else if producer.index + 1 != pseudo.index {
                return Err(ResultBindingError::NonAdjacent(instruction.offset));
            }
            let value = instruction
                .result
                .clone()
                .ok_or(ResultBindingError::MissingDestination(instruction.offset))?;
            bindings.push(ResultBinding {
                producer: *producer,
                pseudo: *pseudo,
                value,
            });
        }
        Ok(bindings)
    }

    fn instruction(cfg: &CFG, position: InsnPosition) -> Result<&InsnNode, ResultBindingError> {
        cfg.block(position.block)
            .and_then(|block| block.insns.get(position.index))
            .ok_or(ResultBindingError::MissingInstruction(position))
    }

    fn result_type(producer: &InsnNode) -> Result<ArgType, ResultBindingError> {
        match producer.insn_type {
            InsnType::Invoke => {
                let method = producer
                    .payload
                    .reference
                    .as_ref()
                    .ok_or(ResultBindingError::MissingReference(producer.offset))?;
                let MemberReference::Method(method) = method else {
                    return Err(ResultBindingError::InvalidReferenceKind(producer.offset));
                };
                if method.descriptor.return_type == ArgType::VOID {
                    return Err(ResultBindingError::VoidResult(producer.offset));
                }
                Ok(method.descriptor.return_type.clone())
            }
            InsnType::FilledNewArray => producer
                .payload
                .class_type
                .clone()
                .ok_or(ResultBindingError::MissingReference(producer.offset)),
            _ => Err(ResultBindingError::InvalidProducer {
                offset: producer.offset,
                instruction: producer.insn_type,
            }),
        }
    }
}

#[derive(Debug, Default)]
pub struct BindResults;

impl Pass for BindResults {
    type Error = ResultBindingError;

    fn name(&self) -> &'static str {
        "bind_results"
    }

    fn run(&mut self, cfg: &mut CFG) -> Result<PassResult, Self::Error> {
        let bindings = ResultBindingAnalysis::analyze(cfg)?;
        if bindings.is_empty() {
            return Ok(PassResult::Unchanged);
        }

        for binding in &bindings {
            let producer = cfg
                .block_mut(binding.producer.block)
                .and_then(|block| block.insns.get_mut(binding.producer.index))
                .ok_or(ResultBindingError::MissingInstruction(binding.producer))?;
            let mut result = binding.value.clone();
            if !result.ty.is_known() {
                result.ty = ResultBindingAnalysis::result_type(producer)?;
            }
            producer.result = Some(result);
        }

        let mut removals = BTreeMap::<BlockId, Vec<usize>>::new();
        for binding in bindings {
            removals
                .entry(binding.pseudo.block)
                .or_default()
                .push(binding.pseudo.index);
        }
        for (block, mut indices) in removals {
            indices.sort_unstable_by(|left, right| right.cmp(left));
            let instructions = &mut cfg
                .block_mut(block)
                .ok_or(ResultBindingError::MissingBlock(block))?
                .insns;
            for index in indices {
                if index >= instructions.len() {
                    return Err(ResultBindingError::MissingInstruction(InsnPosition {
                        block,
                        index,
                    }));
                }
                instructions.remove(index);
            }
        }
        Ok(PassResult::Changed)
    }
}
