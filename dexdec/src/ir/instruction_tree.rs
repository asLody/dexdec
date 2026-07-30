//! Iterative traversal and ownership-preserving transformation of instruction trees.

use super::{InsnArg, InsnNode, RegisterArg};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstructionTreeError {
    MalformedWorkStack,
    ChildArity { expected: usize, actual: usize },
}

impl std::fmt::Display for InstructionTreeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedWorkStack => formatter.write_str("malformed instruction tree stack"),
            Self::ChildArity { expected, actual } => write!(
                formatter,
                "instruction tree frame has {actual} children, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for InstructionTreeError {}

/// Typed callbacks for read-only instruction-tree analyses.
pub trait InstructionVisitor {
    fn visit_register(&mut self, _register: &RegisterArg) {}

    fn visit_instruction(&mut self, _instruction: &InsnNode) {}
}

/// Typed callbacks for bottom-up instruction-tree transformations.
pub trait InstructionTransform {
    fn transform_register(&mut self, register: RegisterArg) -> InsnArg {
        InsnArg::Reg(register)
    }

    fn transform_instruction(&mut self, instruction: InsnNode) -> InsnNode {
        instruction
    }

    fn transform_result(&mut self, result: RegisterArg) -> RegisterArg {
        result
    }

    fn transform_wrapped(&mut self, instruction: InsnNode) -> InsnArg {
        InsnArg::wrap(self.transform_instruction(instruction))
    }
}

/// Stack-safe traversal of wrapped instructions and their arguments.
pub struct InstructionTree;

impl InstructionTree {
    pub fn visit_arg<V>(argument: &InsnArg, visitor: &mut V)
    where
        V: InstructionVisitor + ?Sized,
    {
        let mut pending = vec![argument];
        while let Some(argument) = pending.pop() {
            match argument {
                InsnArg::Reg(register) => visitor.visit_register(register),
                InsnArg::Lit(_) => {}
                InsnArg::Wrapped(instruction) => {
                    visitor.visit_instruction(instruction);
                    pending.extend(instruction.payload.compound_target.iter());
                    pending.extend(instruction.args.iter().rev());
                }
            }
        }
    }

    pub fn visit_args<V>(instruction: &InsnNode, visitor: &mut V)
    where
        V: InstructionVisitor + ?Sized,
    {
        for argument in &instruction.args {
            Self::visit_arg(argument, visitor);
        }
        if let Some(target) = &instruction.payload.compound_target {
            Self::visit_arg(target, visitor);
        }
    }

    pub fn transform_arg<T>(
        argument: InsnArg,
        transform: &mut T,
    ) -> Result<InsnArg, InstructionTreeError>
    where
        T: InstructionTransform + ?Sized,
    {
        let mut pending = vec![TransformTask::Argument(argument)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                TransformTask::Argument(argument) => match argument {
                    InsnArg::Reg(register) => {
                        results.push(transform.transform_register(register));
                    }
                    InsnArg::Lit(literal) => results.push(InsnArg::Lit(literal)),
                    InsnArg::Wrapped(instruction) => {
                        let mut instruction = (*instruction).clone();
                        let argument_count = instruction.args.len();
                        let has_target = instruction.payload.compound_target.is_some();
                        let mut children = std::mem::take(&mut instruction.args);
                        children.extend(instruction.payload.compound_target.take());
                        pending.push(TransformTask::Instruction {
                            instruction,
                            argument_count,
                            has_target,
                        });
                        pending.extend(children.into_iter().rev().map(TransformTask::Argument));
                    }
                },
                TransformTask::Instruction {
                    mut instruction,
                    argument_count,
                    has_target,
                } => {
                    let child_count = argument_count + usize::from(has_target);
                    let start = results
                        .len()
                        .checked_sub(child_count)
                        .ok_or(InstructionTreeError::MalformedWorkStack)?;
                    let children = results.drain(start..).collect::<Vec<_>>();
                    let mut children = children.into_iter();
                    instruction
                        .args
                        .extend(children.by_ref().take(argument_count));
                    if has_target {
                        instruction.payload.compound_target =
                            Some(children.next().ok_or(InstructionTreeError::ChildArity {
                                expected: child_count,
                                actual: child_count.saturating_sub(1),
                            })?);
                    }
                    results.push(transform.transform_wrapped(instruction));
                }
            }
        }
        if results.len() != 1 {
            return Err(InstructionTreeError::MalformedWorkStack);
        }
        results
            .pop()
            .ok_or(InstructionTreeError::MalformedWorkStack)
    }

    pub fn transform_args<T>(
        instruction: &mut InsnNode,
        transform: &mut T,
    ) -> Result<(), InstructionTreeError>
    where
        T: InstructionTransform + ?Sized,
    {
        instruction.args = std::mem::take(&mut instruction.args)
            .into_iter()
            .map(|argument| Self::transform_arg(argument, transform))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(target) = instruction.payload.compound_target.take() {
            instruction.payload.compound_target = Some(Self::transform_arg(target, transform)?);
        }
        Ok(())
    }

    pub fn transform<T>(
        mut instruction: InsnNode,
        transform: &mut T,
    ) -> Result<InsnNode, InstructionTreeError>
    where
        T: InstructionTransform + ?Sized,
    {
        Self::transform_args(&mut instruction, transform)?;
        instruction.result = instruction
            .result
            .take()
            .map(|result| transform.transform_result(result));
        Ok(transform.transform_instruction(instruction))
    }
}

enum TransformTask {
    Argument(InsnArg),
    Instruction {
        instruction: InsnNode,
        argument_count: usize,
        has_target: bool,
    },
}
