//! Source-observable instruction effects shared by dataflow analyses.

use crate::ir::{ArgType, InsnArg, InsnNode, InsnType, MemberReference, MethodReference};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ThrowEffect {
    None,
    SubtypesOf(&'static str),
    Any,
}

impl ThrowEffect {
    pub fn of_tree(instruction: &InsnNode) -> Self {
        let mut effect = Self::None;
        let mut pending = vec![instruction];
        while let Some(instruction) = pending.pop() {
            effect = effect.join(Self::of(instruction));
            pending.extend(
                instruction
                    .args
                    .iter()
                    .chain(instruction.payload.compound_target.iter())
                    .filter_map(|argument| match argument {
                        InsnArg::Wrapped(child) => Some(child.as_ref()),
                        InsnArg::Reg(_) | InsnArg::Lit(_) => None,
                    }),
            );
        }
        effect
    }

    fn of(instruction: &InsnNode) -> Self {
        if !instruction.can_throw() {
            Self::None
        } else if instruction.insn_type == InsnType::ConstClass {
            Self::SubtypesOf("java/lang/LinkageError")
        } else {
            Self::Any
        }
    }

    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, effect) | (effect, Self::None) => effect,
            (Self::SubtypesOf(left), Self::SubtypesOf(right)) if left == right => self,
            _ => Self::Any,
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionEffects {
    reads: bool,
    writes: bool,
    calls: bool,
    may_throw: bool,
    synchronizes: bool,
    controls: bool,
}

impl InstructionEffects {
    pub const PURE: Self = Self {
        reads: false,
        writes: false,
        calls: false,
        may_throw: false,
        synchronizes: false,
        controls: false,
    };

    pub const CONTROL: Self = Self {
        controls: true,
        ..Self::PURE
    };

    pub const SYNCHRONIZATION: Self = Self {
        synchronizes: true,
        may_throw: true,
        ..Self::PURE
    };

    const UNKNOWN_CALL: Self = Self {
        reads: true,
        writes: true,
        calls: true,
        may_throw: true,
        synchronizes: false,
        controls: false,
    };

    pub fn of(instruction: &InsnNode) -> Self {
        if instruction.payload.edge_copy {
            return Self {
                writes: true,
                controls: true,
                ..Self::PURE
            };
        }
        if instruction.insn_type == InsnType::Invoke {
            if let Some(effects) = IntrinsicMethodEffects::resolve(instruction) {
                return effects;
            }
        }
        let mut effects = match instruction.insn_type {
            InsnType::Const
            | InsnType::ConstStr
            | InsnType::Move
            | InsnType::Neg
            | InsnType::Not
            | InsnType::Cast
            | InsnType::Cmp
            | InsnType::InstanceOf
            | InsnType::Nop
            | InsnType::Phi
            | InsnType::Arith
            | InsnType::Ternary => Self::PURE,
            InsnType::ConstClass => Self {
                reads: true,
                ..Self::PURE
            },
            InsnType::CheckCast
            | InsnType::ArrayLength
            | InsnType::Aget
            | InsnType::Iget
            | InsnType::Sget => Self {
                reads: true,
                may_throw: true,
                ..Self::PURE
            },
            InsnType::CompoundAssign
            | InsnType::FillArray
            | InsnType::Aput
            | InsnType::Iput
            | InsnType::Sput => Self {
                writes: true,
                may_throw: true,
                ..Self::PURE
            },
            InsnType::Invoke => Self::UNKNOWN_CALL,
            InsnType::StringConcat
            | InsnType::FilledNewArray
            | InsnType::NewArray
            | InsnType::NewInstance
            | InsnType::MoveResult
            | InsnType::Constructor => Self {
                reads: true,
                writes: true,
                calls: true,
                may_throw: true,
                ..Self::PURE
            },
            InsnType::MonitorEnter | InsnType::MonitorExit => Self {
                synchronizes: true,
                may_throw: true,
                ..Self::PURE
            },
            InsnType::Return
            | InsnType::Goto
            | InsnType::Throw
            | InsnType::MoveException
            | InsnType::If
            | InsnType::Switch
            | InsnType::Break
            | InsnType::Continue => Self::CONTROL,
        };
        effects.may_throw |= instruction.can_throw();
        effects
    }

    /// Computes the source-observable effects of an instruction and every
    /// wrapped instruction evaluated as one expression.
    pub fn of_tree(instruction: &InsnNode) -> Self {
        let mut combined = Self::PURE;
        let mut pending = vec![instruction];
        while let Some(instruction) = pending.pop() {
            combined = combined.join(Self::of(instruction));
            pending.extend(
                instruction
                    .args
                    .iter()
                    .chain(instruction.payload.compound_target.iter())
                    .filter_map(|argument| match argument {
                        InsnArg::Wrapped(child) => Some(child.as_ref()),
                        InsnArg::Reg(_) | InsnArg::Lit(_) => None,
                    }),
            );
        }
        combined
    }

    pub fn of_argument(argument: &InsnArg) -> Self {
        match argument {
            InsnArg::Wrapped(instruction) => Self::of_tree(instruction),
            InsnArg::Reg(_) | InsnArg::Lit(_) => Self::PURE,
        }
    }

    pub fn join(self, other: Self) -> Self {
        Self {
            reads: self.reads || other.reads,
            writes: self.writes || other.writes,
            calls: self.calls || other.calls,
            may_throw: self.may_throw || other.may_throw,
            synchronizes: self.synchronizes || other.synchronizes,
            controls: self.controls || other.controls,
        }
    }

    pub fn is_pure(self) -> bool {
        self == Self::PURE
    }

    pub fn may_throw(self) -> bool {
        self.may_throw
    }

    pub fn reads_memory(self) -> bool {
        self.reads
    }

    pub fn writes_memory(self) -> bool {
        self.writes
    }

    pub fn calls(self) -> bool {
        self.calls
    }

    pub fn synchronizes(self) -> bool {
        self.synchronizes
    }

    pub fn controls(self) -> bool {
        self.controls
    }

    pub fn is_ssa_bookkeeping(instruction: &InsnNode) -> bool {
        matches!(
            instruction.insn_type,
            InsnType::Nop
                | InsnType::Goto
                | InsnType::Move
                | InsnType::MoveException
                | InsnType::Phi
        )
    }

    pub fn can_relocate(self) -> bool {
        !self.synchronizes && !self.controls
    }

    /// Whether an instruction can remain inside an explicit execution domain.
    ///
    /// Predication preserves evaluation order and exception timing, so reads
    /// and potentially-throwing expressions are legal. Observable writes,
    /// calls, synchronization, and control transfers still require their
    /// original structured node.
    pub fn can_predicate(self) -> bool {
        !self.writes && !self.calls && !self.synchronizes && !self.controls
    }

    pub fn without_control(mut self) -> Self {
        self.controls = false;
        self
    }

    pub fn is_control_only(self) -> bool {
        self.controls && self.without_control().is_pure()
    }

    pub fn conflicts_with(self, other: Self) -> bool {
        if self.is_pure() || other.is_pure() {
            return false;
        }
        if self.controls || other.controls || self.synchronizes || other.synchronizes {
            return true;
        }
        if self.calls || other.calls {
            return true;
        }
        if (self.writes && (other.reads || other.writes))
            || (other.writes && (self.reads || self.writes))
        {
            return true;
        }
        self.may_throw && other.may_throw
    }
}

struct IntrinsicMethodEffects;

impl IntrinsicMethodEffects {
    fn resolve(instruction: &InsnNode) -> Option<InstructionEffects> {
        let MemberReference::Method(method) = instruction.payload.reference.as_ref()? else {
            return None;
        };
        Self::floating_predicate(method).then_some(InstructionEffects::PURE)
    }

    fn floating_predicate(method: &MethodReference) -> bool {
        let operand = if method.owner == ArgType::object("java/lang/Float") {
            ArgType::FLOAT
        } else if method.owner == ArgType::object("java/lang/Double") {
            ArgType::DOUBLE
        } else {
            return false;
        };
        matches!(method.name.as_str(), "isNaN" | "isInfinite")
            && method.descriptor.parameters == [operand]
            && method.descriptor.return_type == ArgType::BOOLEAN
    }
}
