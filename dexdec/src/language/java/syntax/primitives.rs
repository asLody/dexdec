//! Java primitive expression typing and numeric promotion.

use crate::ir::{ArithOp, PrimitiveType};

/// Source-level primitive typing applied after DEX values have acquired their
/// Java operand types.
pub(in crate::language::java) struct JavaPrimitiveSemantics;

impl JavaPrimitiveSemantics {
    pub(in crate::language::java) fn numeric(primitive: PrimitiveType) -> Option<PrimitiveType> {
        matches!(
            primitive,
            PrimitiveType::Byte
                | PrimitiveType::Short
                | PrimitiveType::Char
                | PrimitiveType::Int
                | PrimitiveType::Long
                | PrimitiveType::Float
                | PrimitiveType::Double
        )
        .then_some(primitive)
    }

    pub(in crate::language::java) fn unary_numeric_promotion(
        primitive: PrimitiveType,
    ) -> Option<PrimitiveType> {
        match Self::numeric(primitive)? {
            PrimitiveType::Byte | PrimitiveType::Short | PrimitiveType::Char => {
                Some(PrimitiveType::Int)
            }
            primitive => Some(primitive),
        }
    }

    pub(in crate::language::java) fn binary_numeric_promotion(
        left: PrimitiveType,
        right: PrimitiveType,
    ) -> Option<PrimitiveType> {
        let left = Self::unary_numeric_promotion(left)?;
        let right = Self::unary_numeric_promotion(right)?;
        [
            PrimitiveType::Double,
            PrimitiveType::Float,
            PrimitiveType::Long,
            PrimitiveType::Int,
        ]
        .into_iter()
        .find(|candidate| left == *candidate || right == *candidate)
    }

    pub(in crate::language::java) fn arithmetic_result(
        operator: ArithOp,
        left: PrimitiveType,
        right: PrimitiveType,
    ) -> Option<PrimitiveType> {
        if matches!(operator, ArithOp::And | ArithOp::Or | ArithOp::Xor)
            && left == PrimitiveType::Boolean
            && right == PrimitiveType::Boolean
        {
            return Some(PrimitiveType::Boolean);
        }
        if matches!(operator, ArithOp::Shl | ArithOp::Shr | ArithOp::Ushr) {
            Self::unary_numeric_promotion(right)?;
            return Self::unary_numeric_promotion(left);
        }
        Self::binary_numeric_promotion(left, right)
    }

    pub(in crate::language::java) fn is_widening(
        source: PrimitiveType,
        target: PrimitiveType,
    ) -> bool {
        use PrimitiveType::{Byte, Char, Double, Float, Int, Long, Short};
        matches!(
            (source, target),
            (Byte, Short | Int | Long | Float | Double)
                | (Short | Char, Int | Long | Float | Double)
                | (Int, Long | Float | Double)
                | (Long, Float | Double)
                | (Float, Double)
        )
    }
}
