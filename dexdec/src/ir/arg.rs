//! Instruction Arguments
//!
//! This module defines the argument types for IR instructions, inspired by jadx.
//!
//! ## Argument Types
//!
//! - `RegisterArg` - A register reference (v0, v1, etc.)
//! - `LiteralArg` - A literal value (integer, long, etc.)
//! - `WrappedArg` - A wrapped instruction (for expression inlining)
//! - `InsnArg` - Unified argument type

use super::insn::InsnNode;
use super::instruction_tree::{InstructionTree, InstructionVisitor};
use super::ty::ArgType;
use std::fmt;
use std::sync::Arc;

/// Register number type
pub type RegNum = u32;

/// Instruction argument - can be a register, literal, or wrapped instruction
#[derive(Debug, Clone)]
pub enum InsnArg {
    /// Register argument
    Reg(RegisterArg),
    /// Literal argument
    Lit(LiteralArg),
    /// Wrapped instruction (for expression inlining)
    Wrapped(Arc<InsnNode>),
}

// Manual PartialEq impl: wrapped instructions compare by Arc pointer equality
impl PartialEq for InsnArg {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (InsnArg::Reg(a), InsnArg::Reg(b)) => a == b,
            (InsnArg::Lit(a), InsnArg::Lit(b)) => a == b,
            (InsnArg::Wrapped(a), InsnArg::Wrapped(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }
}

impl InsnArg {
    /// Create a register argument
    pub fn reg(reg_num: RegNum, ty: ArgType) -> Self {
        InsnArg::Reg(RegisterArg::new(reg_num, ty))
    }

    /// Create a register argument with SSA version
    pub fn reg_ssa(reg_num: RegNum, version: u32, ty: ArgType) -> Self {
        InsnArg::Reg(RegisterArg::with_ssa(reg_num, ty, version))
    }

    /// Create a literal argument
    pub fn lit(value: i64, ty: ArgType) -> Self {
        InsnArg::Lit(LiteralArg::new(value, ty))
    }

    /// Wrap an instruction as an argument (for expression inlining)
    pub fn wrap(insn: InsnNode) -> Self {
        InsnArg::Wrapped(Arc::new(insn))
    }

    /// Return the type carried by this IR value, if it has one.
    pub fn declared_type(&self) -> Option<&ArgType> {
        match self {
            InsnArg::Reg(register) => Some(&register.ty),
            InsnArg::Lit(literal) => Some(&literal.ty),
            InsnArg::Wrapped(instruction) => instruction.result.as_ref().map(|result| &result.ty),
        }
    }

    /// Check if this is a register argument
    pub fn is_register(&self) -> bool {
        matches!(self, InsnArg::Reg(_))
    }

    /// Check if this is a literal argument
    pub fn is_literal(&self) -> bool {
        matches!(self, InsnArg::Lit(_))
    }

    /// Check if this is a wrapped instruction
    pub fn is_wrapped(&self) -> bool {
        matches!(self, InsnArg::Wrapped(_))
    }

    /// Get as register argument
    pub fn as_register(&self) -> Option<&RegisterArg> {
        match self {
            InsnArg::Reg(r) => Some(r),
            _ => None,
        }
    }

    /// Get all registers used by this argument (recursively if wrapped)
    pub fn regs_used(&self) -> Vec<RegNum> {
        let mut collector = RegisterNumbers::default();
        InstructionTree::visit_arg(self, &mut collector);
        collector.registers
    }

    /// Get as literal argument
    pub fn as_literal(&self) -> Option<&LiteralArg> {
        match self {
            InsnArg::Lit(l) => Some(l),
            _ => None,
        }
    }

    pub fn literal_value(&self) -> Option<i64> {
        let mut current = self;
        loop {
            match current {
                InsnArg::Lit(literal) => return Some(literal.value),
                InsnArg::Wrapped(instruction)
                    if matches!(
                        instruction.insn_type,
                        super::InsnType::Const | super::InsnType::Move
                    ) =>
                {
                    current = instruction.args.first()?;
                }
                InsnArg::Reg(_) | InsnArg::Wrapped(_) => return None,
            }
        }
    }

    /// Get as wrapped instruction
    pub fn as_wrapped(&self) -> Option<&InsnNode> {
        match self {
            InsnArg::Wrapped(insn) => Some(insn.as_ref()),
            _ => None,
        }
    }

    /// Get register number if this is a register
    pub fn reg_num(&self) -> Option<RegNum> {
        self.as_register().map(|r| r.reg_num)
    }

    /// Get constant value if this is a literal argument
    pub fn const_value(&self) -> Option<i64> {
        self.as_literal().map(|l| l.value)
    }
}

#[derive(Default)]
struct RegisterNumbers {
    registers: Vec<RegNum>,
}

impl InstructionVisitor for RegisterNumbers {
    fn visit_register(&mut self, register: &RegisterArg) {
        self.registers.push(register.reg_num);
    }
}

impl fmt::Display for InsnArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InsnArg::Reg(r) => write!(f, "{}", r),
            InsnArg::Lit(l) => write!(f, "{}", l),
            InsnArg::Wrapped(insn) => write!(f, "<wrapped:{:?}>", insn.insn_type),
        }
    }
}

/// Register argument - references a Dalvik register
#[derive(Debug, Clone, PartialEq)]
pub struct RegisterArg {
    /// Register number (v0, v1, etc.)
    pub reg_num: RegNum,
    /// Type of the value in this register
    pub ty: ArgType,
    /// SSA version (for SSA form)
    pub ssa_version: Option<u32>,
    /// Source-level variable identity recovered from SSA/code-var analysis.
    pub code_var: Option<u32>,
}

impl RegisterArg {
    /// Create a new register argument
    pub fn new(reg_num: RegNum, ty: ArgType) -> Self {
        Self {
            reg_num,
            ty,
            ssa_version: None,
            code_var: None,
        }
    }

    /// Create with SSA version
    pub fn with_ssa(reg_num: RegNum, ty: ArgType, version: u32) -> Self {
        Self {
            reg_num,
            ty,
            ssa_version: Some(version),
            code_var: None,
        }
    }

    /// Alias for with_ssa for convenience
    pub fn new_ssa(reg_num: RegNum, version: u32, ty: ArgType) -> Self {
        Self::with_ssa(reg_num, ty, version)
    }
}

impl fmt::Display for RegisterArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ver) = self.ssa_version {
            write!(f, "v{}_{}", self.reg_num, ver)
        } else {
            write!(f, "v{}", self.reg_num)
        }
    }
}

/// Literal argument - an immediate value
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralArg {
    /// The literal value
    pub value: i64,
    /// Type of the literal
    pub ty: ArgType,
}

impl LiteralArg {
    /// Create a new literal argument
    pub fn new(value: i64, ty: ArgType) -> Self {
        Self { value, ty }
    }

    /// Create an integer literal
    pub fn int(value: i32) -> Self {
        Self::new(value as i64, ArgType::INT)
    }

    /// Create a long literal
    pub fn long(value: i64) -> Self {
        Self::new(value, ArgType::LONG)
    }

    /// Create a float literal (from raw bits)
    pub fn float_bits(bits: u32) -> Self {
        Self::new(bits as i64, ArgType::FLOAT)
    }

    /// Create a double literal (from raw bits)
    pub fn double_bits(bits: u64) -> Self {
        Self::new(bits as i64, ArgType::DOUBLE)
    }

    /// Get the value as an integer
    pub fn as_int(&self) -> i32 {
        self.value as i32
    }

    /// Get the value as a long
    pub fn as_long(&self) -> i64 {
        self.value
    }

    /// Get the value as a float
    pub fn as_float(&self) -> f32 {
        f32::from_bits(self.value as u32)
    }

    /// Get the value as a double
    pub fn as_double(&self) -> f64 {
        f64::from_bits(self.value as u64)
    }

    /// Check if this is a zero value
    pub fn is_zero(&self) -> bool {
        self.value == 0
    }

    /// Check if this is a null reference
    pub fn is_null(&self) -> bool {
        self.value == 0 && self.ty.is_object()
    }
}

impl fmt::Display for LiteralArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ty {
            ArgType::Primitive(super::ty::PrimitiveType::Float) => {
                write!(f, "{}f", self.as_float())
            }
            ArgType::Primitive(super::ty::PrimitiveType::Double) => {
                write!(f, "{}d", self.as_double())
            }
            ArgType::Primitive(super::ty::PrimitiveType::Long) => {
                write!(f, "{}L", self.value)
            }
            ArgType::Primitive(super::ty::PrimitiveType::Boolean) => {
                if self.value == 0 {
                    write!(f, "false")
                } else {
                    write!(f, "true")
                }
            }
            ArgType::Primitive(super::ty::PrimitiveType::Char) => {
                let c = self.value as u32;
                if let Some(ch) = char::from_u32(c) {
                    if ch.is_ascii_graphic() {
                        write!(f, "'{}'", ch)
                    } else {
                        write!(f, "'\\u{:04x}'", c)
                    }
                } else {
                    write!(f, "{}", self.value)
                }
            }
            ArgType::Object(_) | ArgType::Array(_) => {
                if self.value == 0 {
                    write!(f, "null")
                } else {
                    write!(f, "0x{:x}", self.value)
                }
            }
            _ => write!(f, "{}", self.value),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_arg() {
        let reg = RegisterArg::new(0, ArgType::INT);
        assert_eq!(reg.reg_num, 0);
        assert_eq!(format!("{}", reg), "v0");

        let ssa_reg = RegisterArg::with_ssa(1, ArgType::INT, 2);
        assert_eq!(format!("{}", ssa_reg), "v1_2");
    }

    #[test]
    fn test_literal_arg() {
        let int_lit = LiteralArg::int(42);
        assert_eq!(int_lit.as_int(), 42);
        assert_eq!(format!("{}", int_lit), "42");

        let bool_lit = LiteralArg::new(1, ArgType::BOOLEAN);
        assert_eq!(format!("{}", bool_lit), "true");

        let null_lit = LiteralArg::new(0, ArgType::object("java/lang/Object"));
        assert!(null_lit.is_null());
        assert_eq!(format!("{}", null_lit), "null");
    }

    #[test]
    fn test_insn_arg() {
        let reg = InsnArg::reg(0, ArgType::INT);
        assert!(reg.is_register());
        assert_eq!(reg.reg_num(), Some(0));

        let lit = InsnArg::lit(100, ArgType::INT);
        assert!(lit.is_literal());
    }
}
