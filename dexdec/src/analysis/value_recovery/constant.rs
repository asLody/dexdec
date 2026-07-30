//! Kotlin-compatible evaluation for the constant arm of the SSA value lattice.

use crate::ir::{
    ArgType, ArithOp, CmpBias, InsnArg, InsnNode, InsnType, LiteralArg, PrimitiveType, UnaryOp,
};

pub(super) struct ConstantEvaluator;

impl ConstantEvaluator {
    pub(super) fn fold(instruction: &InsnNode, arguments: &[InsnArg]) -> Option<InsnArg> {
        let result = instruction.result.as_ref()?;
        let value = match instruction.insn_type {
            InsnType::Const => Self::value(arguments.first()?)?,
            InsnType::Arith => Self::arithmetic(
                instruction.payload.arith_op?,
                &result.ty,
                Self::value(arguments.first()?)?,
                Self::value(arguments.get(1)?)?,
            )?,
            InsnType::Neg => Self::negate(&result.ty, Self::value(arguments.first()?)?)?,
            InsnType::Not => Self::bitwise_not(&result.ty, Self::value(arguments.first()?)?)?,
            InsnType::Cast => Self::cast(
                instruction.payload.unary_op?,
                Self::value(arguments.first()?)?,
            )?,
            InsnType::Cmp => Self::compare(
                instruction.payload.cmp_bias?,
                arguments.first()?.declared_type()?,
                Self::value(arguments.first()?)?,
                Self::value(arguments.get(1)?)?,
            )?,
            InsnType::InstanceOf
                if arguments
                    .first()?
                    .declared_type()
                    .is_some_and(|ty| matches!(ty, ArgType::Object(_) | ArgType::Array(_)))
                    && Self::value(arguments.first()?)? == 0 =>
            {
                0
            }
            _ => return None,
        };
        Some(InsnArg::Lit(LiteralArg::new(value, result.ty.clone())))
    }

    fn value(argument: &InsnArg) -> Option<i64> {
        argument.literal_value()
    }

    fn arithmetic(op: ArithOp, ty: &ArgType, left: i64, right: i64) -> Option<i64> {
        match ty.as_primitive()? {
            PrimitiveType::Boolean => match op {
                ArithOp::And | ArithOp::Or | ArithOp::Xor => {
                    Self::int_arithmetic(op, left as i32, right as i32)
                        .map(|value| i64::from(value))
                }
                _ => None,
            },
            PrimitiveType::Byte
            | PrimitiveType::Short
            | PrimitiveType::Char
            | PrimitiveType::Int => {
                Self::int_arithmetic(op, left as i32, right as i32).map(|value| i64::from(value))
            }
            PrimitiveType::Long => Self::long_arithmetic(op, left, right),
            PrimitiveType::Float => {
                let left = f32::from_bits(left as u32);
                let right = f32::from_bits(right as u32);
                let value = match op {
                    ArithOp::Add => left + right,
                    ArithOp::Sub => left - right,
                    ArithOp::Rsub => right - left,
                    ArithOp::Mul => left * right,
                    ArithOp::Div => left / right,
                    ArithOp::Rem => left % right,
                    _ => return None,
                };
                Some(i64::from(value.to_bits()))
            }
            PrimitiveType::Double => {
                let left = f64::from_bits(left as u64);
                let right = f64::from_bits(right as u64);
                let value = match op {
                    ArithOp::Add => left + right,
                    ArithOp::Sub => left - right,
                    ArithOp::Rsub => right - left,
                    ArithOp::Mul => left * right,
                    ArithOp::Div => left / right,
                    ArithOp::Rem => left % right,
                    _ => return None,
                };
                Some(value.to_bits() as i64)
            }
            PrimitiveType::Void | PrimitiveType::Object | PrimitiveType::Array => None,
        }
    }

    fn int_arithmetic(op: ArithOp, left: i32, right: i32) -> Option<i32> {
        let shift = (right as u32) & 0x1f;
        Some(match op {
            ArithOp::Add => left.wrapping_add(right),
            ArithOp::Sub => left.wrapping_sub(right),
            ArithOp::Rsub => right.wrapping_sub(left),
            ArithOp::Mul => left.wrapping_mul(right),
            ArithOp::Div if right == 0 => return None,
            ArithOp::Div if left == i32::MIN && right == -1 => i32::MIN,
            ArithOp::Div => left / right,
            ArithOp::Rem if right == 0 => return None,
            ArithOp::Rem if left == i32::MIN && right == -1 => 0,
            ArithOp::Rem => left % right,
            ArithOp::And => left & right,
            ArithOp::Or => left | right,
            ArithOp::Xor => left ^ right,
            ArithOp::Shl => left.wrapping_shl(shift),
            ArithOp::Shr => left.wrapping_shr(shift),
            ArithOp::Ushr => ((left as u32) >> shift) as i32,
        })
    }

    fn long_arithmetic(op: ArithOp, left: i64, right: i64) -> Option<i64> {
        let shift = (right as u32) & 0x3f;
        Some(match op {
            ArithOp::Add => left.wrapping_add(right),
            ArithOp::Sub => left.wrapping_sub(right),
            ArithOp::Rsub => right.wrapping_sub(left),
            ArithOp::Mul => left.wrapping_mul(right),
            ArithOp::Div if right == 0 => return None,
            ArithOp::Div if left == i64::MIN && right == -1 => i64::MIN,
            ArithOp::Div => left / right,
            ArithOp::Rem if right == 0 => return None,
            ArithOp::Rem if left == i64::MIN && right == -1 => 0,
            ArithOp::Rem => left % right,
            ArithOp::And => left & right,
            ArithOp::Or => left | right,
            ArithOp::Xor => left ^ right,
            ArithOp::Shl => left.wrapping_shl(shift),
            ArithOp::Shr => left.wrapping_shr(shift),
            ArithOp::Ushr => ((left as u64) >> shift) as i64,
        })
    }

    fn negate(ty: &ArgType, value: i64) -> Option<i64> {
        match ty.as_primitive()? {
            PrimitiveType::Byte
            | PrimitiveType::Short
            | PrimitiveType::Char
            | PrimitiveType::Int => Some(i64::from((value as i32).wrapping_neg())),
            PrimitiveType::Long => Some(value.wrapping_neg()),
            PrimitiveType::Float => Some(i64::from((-f32::from_bits(value as u32)).to_bits())),
            PrimitiveType::Double => Some((-f64::from_bits(value as u64)).to_bits() as i64),
            _ => None,
        }
    }

    fn bitwise_not(ty: &ArgType, value: i64) -> Option<i64> {
        match ty.as_primitive()? {
            PrimitiveType::Byte
            | PrimitiveType::Short
            | PrimitiveType::Char
            | PrimitiveType::Int => Some(i64::from(!(value as i32))),
            PrimitiveType::Long => Some(!value),
            _ => None,
        }
    }

    fn cast(op: UnaryOp, value: i64) -> Option<i64> {
        Some(match op {
            UnaryOp::IntToLong => i64::from(value as i32),
            UnaryOp::IntToFloat => i64::from((value as i32 as f32).to_bits()),
            UnaryOp::IntToDouble => (value as i32 as f64).to_bits() as i64,
            UnaryOp::LongToInt => i64::from(value as i32),
            UnaryOp::LongToFloat => i64::from((value as f32).to_bits()),
            UnaryOp::LongToDouble => (value as f64).to_bits() as i64,
            UnaryOp::FloatToInt => i64::from(f32::from_bits(value as u32) as i32),
            UnaryOp::FloatToLong => f32::from_bits(value as u32) as i64,
            UnaryOp::FloatToDouble => (f32::from_bits(value as u32) as f64).to_bits() as i64,
            UnaryOp::DoubleToInt => i64::from(f64::from_bits(value as u64) as i32),
            UnaryOp::DoubleToLong => f64::from_bits(value as u64) as i64,
            UnaryOp::DoubleToFloat => i64::from((f64::from_bits(value as u64) as f32).to_bits()),
            UnaryOp::IntToByte => i64::from(value as i8),
            UnaryOp::IntToChar => i64::from(value as u16),
            UnaryOp::IntToShort => i64::from(value as i16),
            UnaryOp::Neg | UnaryOp::Not => return None,
        })
    }

    fn compare(bias: CmpBias, ty: &ArgType, left: i64, right: i64) -> Option<i64> {
        let ordering = match ty.as_primitive()? {
            PrimitiveType::Long => left.cmp(&right),
            PrimitiveType::Float => {
                let left = f32::from_bits(left as u32);
                let right = f32::from_bits(right as u32);
                if left.is_nan() || right.is_nan() {
                    return Some(match bias {
                        CmpBias::Lt => -1,
                        CmpBias::Gt => 1,
                        CmpBias::None => return None,
                    });
                }
                left.partial_cmp(&right)?
            }
            PrimitiveType::Double => {
                let left = f64::from_bits(left as u64);
                let right = f64::from_bits(right as u64);
                if left.is_nan() || right.is_nan() {
                    return Some(match bias {
                        CmpBias::Lt => -1,
                        CmpBias::Gt => 1,
                        CmpBias::None => return None,
                    });
                }
                left.partial_cmp(&right)?
            }
            _ => return None,
        };
        Some(match ordering {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        })
    }
}
