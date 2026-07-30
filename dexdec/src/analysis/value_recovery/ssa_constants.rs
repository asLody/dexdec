//! Sparse constant propagation over the complete SSA CFG.

use std::collections::BTreeMap;

use crate::ir::{analysis::SsaVar, ArgType, InsnArg, InsnNode, InsnType, Utf16String, CFG};

use super::constant::ConstantEvaluator;

pub(super) struct SparseConstantPropagation<'a> {
    cfg: &'a CFG,
}

impl<'a> SparseConstantPropagation<'a> {
    pub(super) fn new(cfg: &'a CFG) -> Self {
        Self { cfg }
    }

    pub(super) fn solve(&self) -> BTreeMap<SsaVar, InsnArg> {
        let mut states = self
            .cfg
            .blocks
            .values()
            .flat_map(|block| &block.insns)
            .filter_map(|instruction| {
                instruction
                    .result
                    .as_ref()
                    .and_then(SsaVar::from_reg)
                    .map(|value| (value, ConstantState::Unknown))
            })
            .collect::<BTreeMap<_, _>>();

        loop {
            let mut changed = false;
            for block in self.cfg.blocks.values() {
                for instruction in &block.insns {
                    let Some(value) = instruction.result.as_ref().and_then(SsaVar::from_reg) else {
                        continue;
                    };
                    let next = self.evaluate(instruction, &states);
                    let state = states.entry(value).or_insert(ConstantState::Unknown);
                    changed |= state.advance(next);
                }
            }
            if !changed {
                break;
            }
        }

        states
            .into_iter()
            .filter_map(|(value, state)| match state {
                ConstantState::Constant(constant) => Some((value, constant)),
                ConstantState::Unknown | ConstantState::Varying => None,
            })
            .collect()
    }

    fn evaluate(
        &self,
        instruction: &InsnNode,
        states: &BTreeMap<SsaVar, ConstantState>,
    ) -> ConstantState {
        match instruction.insn_type {
            InsnType::Const | InsnType::ConstStr => {
                ConstantState::Constant(InsnArg::wrap(instruction.clone()))
            }
            InsnType::Move => instruction
                .args
                .first()
                .map(|argument| Self::argument(argument, states))
                .unwrap_or(ConstantState::Varying),
            InsnType::Phi => Self::merge(&instruction.args, states),
            InsnType::Arith
            | InsnType::Neg
            | InsnType::Not
            | InsnType::Cast
            | InsnType::Cmp
            | InsnType::InstanceOf => self.fold(instruction, states),
            _ => ConstantState::Varying,
        }
    }

    fn merge(arguments: &[InsnArg], states: &BTreeMap<SsaVar, ConstantState>) -> ConstantState {
        let mut constant = None;
        for argument in arguments {
            match Self::argument(argument, states) {
                // Undefined values are the bottom element of the SCCP
                // lattice. Treating them as a conflicting value prevents a
                // loop-invariant constant from ever crossing its back edge.
                ConstantState::Unknown => continue,
                ConstantState::Varying => return ConstantState::Varying,
                ConstantState::Constant(candidate) => match &constant {
                    Some(existing) if !same_constant(existing, &candidate) => {
                        return ConstantState::Varying;
                    }
                    Some(_) => {}
                    None => constant = Some(candidate),
                },
            }
        }
        constant.map_or(ConstantState::Unknown, ConstantState::Constant)
    }

    fn fold(
        &self,
        instruction: &InsnNode,
        states: &BTreeMap<SsaVar, ConstantState>,
    ) -> ConstantState {
        let mut arguments = Vec::with_capacity(instruction.args.len());
        for argument in &instruction.args {
            match Self::argument(argument, states) {
                ConstantState::Unknown => return ConstantState::Unknown,
                ConstantState::Varying => return ConstantState::Varying,
                ConstantState::Constant(constant) => arguments.push(constant),
            }
        }
        ConstantEvaluator::fold(instruction, &arguments)
            .map(ConstantState::Constant)
            .unwrap_or(ConstantState::Varying)
    }

    fn argument(argument: &InsnArg, states: &BTreeMap<SsaVar, ConstantState>) -> ConstantState {
        match argument {
            InsnArg::Lit(_) => ConstantState::Constant(argument.clone()),
            InsnArg::Reg(register) => SsaVar::from_reg(register)
                .and_then(|value| states.get(&value))
                .cloned()
                .unwrap_or(ConstantState::Varying),
            InsnArg::Wrapped(instruction)
                if matches!(instruction.insn_type, InsnType::Const | InsnType::ConstStr) =>
            {
                ConstantState::Constant(argument.clone())
            }
            InsnArg::Wrapped(_) => ConstantState::Varying,
        }
    }
}

#[derive(Clone)]
enum ConstantState {
    Unknown,
    Constant(InsnArg),
    Varying,
}

impl ConstantState {
    fn advance(&mut self, next: Self) -> bool {
        let merged = match (&*self, next) {
            (Self::Varying, _) => return false,
            (Self::Unknown, next) => next,
            (Self::Constant(current), Self::Unknown) => Self::Constant(current.clone()),
            (Self::Constant(current), Self::Constant(next)) if same_constant(current, &next) => {
                return false;
            }
            (Self::Constant(_), Self::Constant(_) | Self::Varying) => Self::Varying,
        };
        if matches!((&*self, &merged), (Self::Unknown, Self::Unknown)) {
            return false;
        }
        *self = merged;
        true
    }
}

fn same_constant(left: &InsnArg, right: &InsnArg) -> bool {
    match (constant_key(left), constant_key(right)) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
}

#[derive(PartialEq, Eq)]
enum ConstantKey<'a> {
    Literal(i64, &'a ArgType),
    String(&'a Utf16String),
}

fn constant_key(value: &InsnArg) -> Option<ConstantKey<'_>> {
    match value {
        InsnArg::Lit(literal) => Some(ConstantKey::Literal(literal.value, &literal.ty)),
        InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::Const => {
            let literal = instruction.args.first()?.as_literal()?;
            Some(ConstantKey::Literal(
                literal.value,
                instruction
                    .result
                    .as_ref()
                    .map(|result| &result.ty)
                    .unwrap_or(&literal.ty),
            ))
        }
        InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::ConstStr => Some(
            ConstantKey::String(instruction.payload.string_value.as_ref()?),
        ),
        InsnArg::Reg(_) | InsnArg::Wrapped(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loop_phi_discovers_an_invariant_constant_before_the_back_edge() {
        let entry = SsaVar::new(0, 1);
        let back_edge = SsaVar::new(0, 2);
        let constant = InsnArg::lit(1, ArgType::INT);
        let states = BTreeMap::from([
            (entry, ConstantState::Constant(constant.clone())),
            (back_edge, ConstantState::Unknown),
        ]);
        let arguments = [
            InsnArg::reg_ssa(entry.reg_num, entry.version, ArgType::INT),
            InsnArg::reg_ssa(back_edge.reg_num, back_edge.version, ArgType::INT),
        ];

        let ConstantState::Constant(actual) = SparseConstantPropagation::merge(&arguments, &states)
        else {
            panic!("loop invariant was not discovered");
        };
        assert!(same_constant(&actual, &constant));
    }
}
