//! Instructions
//!
//! This module defines IR instructions, inspired by jadx's instruction design.
//!
//! ## Instruction Types
//!
//! Based on jadx's InsnType enum, covering all Dalvik operations.

use super::arg::{InsnArg, RegNum, RegisterArg};
use super::block::BlockId;
use super::bool_expr::BoolExpr;
use super::cfg::EdgeKind;
use super::ty::{ArgType, PrimitiveType};
use std::fmt;

/// Instruction types - based on jadx's InsnType
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InsnType {
    // ==================== Constants ====================
    /// Load constant value
    Const,
    /// Load string constant
    ConstStr,
    /// Load class constant
    ConstClass,

    // ==================== Arithmetic ====================
    /// Arithmetic operation (add, sub, mul, div, rem, and, or, xor, shl, shr, ushr)
    Arith,
    /// Kotlin string concatenation expression.
    StringConcat,
    /// Negation
    Neg,
    /// Bitwise NOT
    Not,

    // ==================== Data Movement ====================
    /// Move value between registers
    Move,
    /// Compound assignment / increment-decrement statement
    CompoundAssign,
    /// Type cast
    Cast,

    // ==================== Control Flow ====================
    /// Return from method
    Return,
    /// Unconditional jump
    Goto,
    /// Throw exception
    Throw,
    /// Move exception reference
    MoveException,

    // ==================== Comparison ====================
    /// Compare (cmpl, cmpg for float/double, cmp for long)
    Cmp,
    /// Conditional branch
    If,
    /// Switch statement
    Switch,

    // ==================== Synchronization ====================
    /// Monitor enter
    MonitorEnter,
    /// Monitor exit
    MonitorExit,

    // ==================== Type Operations ====================
    /// Check cast
    CheckCast,
    /// Instance of
    InstanceOf,

    // ==================== Array Operations ====================
    /// Array length
    ArrayLength,
    /// Fill array with data
    FillArray,
    /// Create filled array
    FilledNewArray,
    /// Array get
    Aget,
    /// Array put
    Aput,
    /// New array
    NewArray,

    // ==================== Object Operations ====================
    /// New instance
    NewInstance,
    /// Instance field get
    Iget,
    /// Instance field put
    Iput,
    /// Static field get
    Sget,
    /// Static field put
    Sput,

    // ==================== Method Invocation ====================
    /// Method invocation
    Invoke,
    /// Move result of method call
    MoveResult,

    /// Constructor call (merges new-instance and <init> invoke)
    Constructor,

    // ==================== SSA/Analysis ====================
    /// No operation
    Nop,
    /// PHI node for SSA
    Phi,

    // ==================== Structured Control Flow ====================
    /// Break from loop
    Break,
    /// Continue loop
    Continue,
    /// Ternary expression (generated during structuring)
    Ternary,
}

impl InsnType {
    /// Check if this instruction is a control flow instruction
    pub fn is_control_flow(&self) -> bool {
        matches!(
            self,
            InsnType::Goto | InsnType::If | InsnType::Switch | InsnType::Return | InsnType::Throw
        )
    }

    /// Check if this instruction terminates the method
    pub fn is_terminal(&self) -> bool {
        matches!(self, InsnType::Return | InsnType::Throw)
    }

    /// Check if this is a branch instruction (Goto, If, Switch)
    /// These are typically handled by the structuring algorithm.
    pub fn is_branch(&self) -> bool {
        matches!(self, InsnType::Goto | InsnType::If | InsnType::Switch)
    }

    /// Check if this instruction can have a result
    pub fn has_result(&self) -> bool {
        matches!(
            self,
            InsnType::Const
                | InsnType::ConstStr
                | InsnType::ConstClass
                | InsnType::Arith
                | InsnType::StringConcat
                | InsnType::Neg
                | InsnType::Not
                | InsnType::Move
                | InsnType::CompoundAssign
                | InsnType::Cast
                | InsnType::CheckCast
                | InsnType::MoveException
                | InsnType::Cmp
                | InsnType::InstanceOf
                | InsnType::ArrayLength
                | InsnType::Aget
                | InsnType::NewArray
                | InsnType::NewInstance
                | InsnType::FilledNewArray
                | InsnType::Iget
                | InsnType::Sget
                | InsnType::MoveResult
                | InsnType::Phi
        )
    }
}

/// Arithmetic operation type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithOp {
    Add,
    Sub,
    /// Reverse subtraction (b - a instead of a - b)
    Rsub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Ushr,
}

/// Unary operation type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    /// Negate (-)
    Neg,
    /// Bitwise NOT (~)
    Not,
    /// Conversion operations
    IntToLong,
    IntToFloat,
    IntToDouble,
    LongToInt,
    LongToFloat,
    LongToDouble,
    FloatToInt,
    FloatToLong,
    FloatToDouble,
    DoubleToInt,
    DoubleToLong,
    DoubleToFloat,
    IntToByte,
    IntToChar,
    IntToShort,
}

impl fmt::Display for ArithOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            ArithOp::Add => "+",
            ArithOp::Sub => "-",
            ArithOp::Rsub => "-r",
            ArithOp::Mul => "*",
            ArithOp::Div => "/",
            ArithOp::Rem => "%",
            ArithOp::And => "&",
            ArithOp::Or => "|",
            ArithOp::Xor => "^",
            ArithOp::Shl => "<<",
            ArithOp::Shr => ">>",
            ArithOp::Ushr => ">>>",
        };
        write!(f, "{}", s)
    }
}

/// Comparison operation type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IfOp {
    Eq,
    Ne,
    Lt,
    Ge,
    Gt,
    Le,
}

impl IfOp {
    /// Invert the comparison
    pub fn invert(&self) -> IfOp {
        match self {
            IfOp::Eq => IfOp::Ne,
            IfOp::Ne => IfOp::Eq,
            IfOp::Lt => IfOp::Ge,
            IfOp::Ge => IfOp::Lt,
            IfOp::Gt => IfOp::Le,
            IfOp::Le => IfOp::Gt,
        }
    }
}

impl fmt::Display for IfOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            IfOp::Eq => "==",
            IfOp::Ne => "!=",
            IfOp::Lt => "<",
            IfOp::Ge => ">=",
            IfOp::Gt => ">",
            IfOp::Le => "<=",
        };
        write!(f, "{}", s)
    }
}

/// Invocation type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvokeType {
    Virtual,
    Super,
    Direct,
    Static,
    Interface,
    Polymorphic,
    Custom,
}

/// Comparison bias for floating-point/long comparisons
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpBias {
    /// Compare less (NaN -> -1)
    Lt,
    /// Compare greater (NaN -> 1)
    Gt,
    /// Compare (no bias, for long)
    None,
}

/// Stable method-local identity assigned at the SSA/region phase boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InstructionId(usize);

impl InstructionId {
    pub const INVALID: Self = Self(usize::MAX);

    pub const fn new(value: usize) -> Self {
        Self(value)
    }

    pub const fn raw(self) -> usize {
        self.0
    }

    pub const fn is_valid(self) -> bool {
        self.0 != usize::MAX
    }
}

impl fmt::Display for InstructionId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "I{}", self.0)
    }
}

/// Instruction node - represents a single IR instruction
#[derive(Debug, Clone)]
pub struct InsnNode {
    /// Stable identity for semantic ownership facts.
    pub id: InstructionId,

    /// Instruction type
    pub insn_type: InsnType,

    /// Result register (if this instruction produces a result)
    pub result: Option<RegisterArg>,

    /// Arguments to the instruction
    pub args: Vec<InsnArg>,

    /// Offset in the original bytecode (for debugging)
    pub offset: u32,

    /// Additional data depending on instruction type
    pub payload: InsnPayload,
}

/// Semantic equality for instruction operations whose control targets are
/// represented by CFG edges. Results, operands, Phi predecessor identities,
/// offsets, and stable origins are compared by the owning graph analysis.
pub trait InstructionEquivalence {
    fn operation_equivalent(&self, other: &Self) -> bool;
}

impl InstructionEquivalence for InsnNode {
    fn operation_equivalent(&self, other: &Self) -> bool {
        self.insn_type == other.insn_type
            && self.payload.arith_op == other.payload.arith_op
            && self.payload.unary_op == other.payload.unary_op
            && self.payload.if_op == other.payload.if_op
            && self.payload.invoke_type == other.payload.invoke_type
            && self.payload.no_return == other.payload.no_return
            && self.payload.reference == other.payload.reference
            && self.payload.string_value == other.payload.string_value
            && self.payload.class_type == other.payload.class_type
            && self.payload.cast_type == other.payload.cast_type
            && self.payload.cmp_bias == other.payload.cmp_bias
            && self.payload.is_static == other.payload.is_static
            && self.payload.is_get == other.payload.is_get
            && self.payload.is_length == other.payload.is_length
            && self.payload.is_enter == other.payload.is_enter
            && self.payload.fill_array_data == other.payload.fill_array_data
            && self.switch_keys() == other.switch_keys()
            && self.payload.switch_default.is_some() == other.payload.switch_default.is_some()
            && self.payload.bool_expr == other.payload.bool_expr
            && self.payload.edge_copy == other.payload.edge_copy
    }
}

impl InsnNode {
    fn switch_keys(&self) -> Option<Vec<i32>> {
        self.payload
            .switch_cases
            .as_ref()
            .map(|cases| cases.iter().map(|(value, _)| *value).collect())
    }
}

/// Payload for DEX `fill-array-data`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FillArrayData {
    pub element_width: u16,
    pub size: u32,
    pub data: Vec<u8>,
}

impl FillArrayData {
    pub fn new(element_width: u16, size: u32, data: Vec<u8>) -> Self {
        Self {
            element_width,
            size,
            data,
        }
    }

    pub fn default_element_type(&self) -> ArgType {
        match self.element_width {
            1 => ArgType::BYTE,
            2 => ArgType::SHORT,
            4 => ArgType::INT,
            8 => ArgType::LONG,
            _ => ArgType::INT,
        }
    }

    pub fn literal_args(&self, element_type: &ArgType) -> Vec<InsnArg> {
        (0..self.size as usize)
            .filter_map(|idx| self.literal_arg(idx, element_type))
            .collect()
    }

    pub fn literal_arg(&self, index: usize, element_type: &ArgType) -> Option<InsnArg> {
        let ty = self.literal_type(element_type);
        let raw = self.raw_element(index)?;
        Some(InsnArg::lit(self.literal_value(raw, &ty), ty))
    }

    fn literal_type(&self, element_type: &ArgType) -> ArgType {
        if self.type_matches_width(element_type) {
            return element_type.clone();
        }
        if let ArgType::Unknown(types) = element_type {
            if let Some(primitive) = types
                .iter()
                .copied()
                .find(|primitive| self.primitive_matches_width(*primitive))
            {
                return ArgType::Primitive(primitive);
            }
        }
        self.default_element_type()
    }

    fn type_matches_width(&self, ty: &ArgType) -> bool {
        ty.as_primitive()
            .is_some_and(|primitive| self.primitive_matches_width(primitive))
    }

    fn primitive_matches_width(&self, primitive: PrimitiveType) -> bool {
        matches!(
            (self.element_width, primitive),
            (1, PrimitiveType::Boolean | PrimitiveType::Byte)
                | (2, PrimitiveType::Short | PrimitiveType::Char)
                | (4, PrimitiveType::Int | PrimitiveType::Float)
                | (8, PrimitiveType::Long | PrimitiveType::Double)
        )
    }

    fn raw_element(&self, index: usize) -> Option<u64> {
        let width = self.element_width as usize;
        let start = index.checked_mul(width)?;
        let bytes = self.data.get(start..start + width)?;
        Some(
            bytes
                .iter()
                .enumerate()
                .fold(0u64, |acc, (idx, byte)| acc | ((*byte as u64) << (idx * 8))),
        )
    }

    fn literal_value(&self, raw: u64, ty: &ArgType) -> i64 {
        match ty.as_primitive() {
            Some(PrimitiveType::Boolean) => i64::from(raw != 0),
            Some(PrimitiveType::Byte) => (raw as u8 as i8) as i64,
            Some(PrimitiveType::Short) => (raw as u16 as i16) as i64,
            Some(PrimitiveType::Char) => raw as u16 as i64,
            Some(PrimitiveType::Float) => raw as u32 as i64,
            Some(PrimitiveType::Long) => raw as i64,
            Some(PrimitiveType::Double) => raw as i64,
            _ => match self.element_width {
                1 => (raw as u8 as i8) as i64,
                2 => (raw as u16 as i16) as i64,
                4 => (raw as u32 as i32) as i64,
                8 => raw as i64,
                _ => raw as i64,
            },
        }
    }
}

/// Additional instruction-specific data
#[derive(Debug, Clone, Default)]
pub struct InsnPayload {
    /// For Arith: the arithmetic operation
    pub arith_op: Option<ArithOp>,

    /// For Unary: the unary operation
    pub unary_op: Option<UnaryOp>,

    /// For If: the comparison operation
    pub if_op: Option<IfOp>,

    /// For If/Goto: target offset
    pub target: Option<i32>,

    /// For Invoke: invocation type
    pub invoke_type: Option<InvokeType>,

    /// The resolved call target cannot complete normally.
    ///
    /// This is an interprocedural fact, not a DEX opcode property. It is
    /// attached before SSA construction so CFG and semantic completion use
    /// the same call behavior.
    pub no_return: bool,

    /// For Invoke/Field: method or field reference
    pub reference: Option<super::MemberReference>,

    /// For ConstStr: string value
    pub string_value: Option<super::Utf16String>,

    /// For ConstStr: string index in DEX string pool
    pub string_index: Option<u32>,

    /// For ConstClass: class type
    pub class_type: Option<ArgType>,

    /// For type-related ops: type index in DEX type pool
    pub type_index: Option<u32>,

    /// For field ops: field index in DEX field pool
    pub field_index: Option<u32>,

    /// For field ops: is this a static field?
    pub is_static: Option<bool>,

    /// For field/array ops: is this a get (read) operation?
    pub is_get: Option<bool>,

    /// For array ops: is this array-length?
    pub is_length: Option<bool>,

    /// For monitor: is this enter or exit?
    pub is_enter: Option<bool>,

    /// For method ops: method index in DEX method pool
    pub method_index: Option<u32>,

    /// For Switch: switch cases (value -> offset)
    pub switch_cases: Option<Vec<(i32, i32)>>,

    /// For Switch: default target
    pub switch_default: Option<i32>,

    /// For Cmp: comparison bias
    pub cmp_bias: Option<CmpBias>,

    /// For Cast: target type
    pub cast_type: Option<ArgType>,

    /// For FillArray: decoded fill-array-data payload.
    pub fill_array_data: Option<FillArrayData>,

    /// For structured expression nodes: recovered boolean condition.
    pub bool_expr: Option<BoolExpr>,

    /// For compound assignments: statement target expression.
    pub compound_target: Option<InsnArg>,

    /// For Phi: incoming CFG edges corresponding one-to-one with `args`.
    ///
    /// Keeping edge identity on the Phi is essential: CFG rewrites and
    /// exceptional predecessors make positional reconstruction ambiguous.
    pub phi_edges: Vec<(BlockId, EdgeKind)>,

    /// Ordered assignment produced while eliminating a parallel Phi copy.
    pub edge_copy: bool,
}

impl InsnNode {
    /// Type produced by an explicit DEX or Kotlin conversion operation.
    ///
    /// DEX `check-cast` stores its indexed reference type in `class_type`,
    /// while primitive conversion instructions store it in `cast_type`.
    /// Consumers should use this semantic accessor instead of depending on
    /// the decoder-level payload representation.
    pub fn conversion_type(&self) -> Option<&ArgType> {
        match self.insn_type {
            InsnType::Cast => self.payload.cast_type.as_ref(),
            InsnType::CheckCast => self
                .payload
                .class_type
                .as_ref()
                .or(self.payload.cast_type.as_ref()),
            _ => None,
        }
        .or_else(|| self.result.as_ref().map(|result| &result.ty))
        .filter(|ty| ty.is_known())
    }

    pub fn can_throw(&self) -> bool {
        match self.insn_type {
            InsnType::Arith => {
                let integral = self
                    .result
                    .as_ref()
                    .map(|result| {
                        !matches!(
                            result.ty.as_primitive(),
                            Some(PrimitiveType::Float | PrimitiveType::Double)
                        )
                    })
                    .unwrap_or(true);
                integral && matches!(self.payload.arith_op, Some(ArithOp::Div | ArithOp::Rem))
            }
            InsnType::Throw
            | InsnType::Invoke
            | InsnType::Constructor
            | InsnType::ConstClass
            | InsnType::Aget
            | InsnType::Aput
            | InsnType::Iget
            | InsnType::Iput
            | InsnType::Sget
            | InsnType::Sput
            | InsnType::NewInstance
            | InsnType::NewArray
            | InsnType::FilledNewArray
            | InsnType::FillArray
            | InsnType::CheckCast
            | InsnType::ArrayLength
            | InsnType::MonitorEnter
            | InsnType::MonitorExit => true,
            _ => false,
        }
    }

    /// Create a new instruction node
    pub fn new(insn_type: InsnType, args_count: usize) -> Self {
        Self {
            id: InstructionId::INVALID,
            insn_type,
            result: None,
            args: Vec::with_capacity(args_count),
            offset: 0,
            payload: InsnPayload::default(),
        }
    }

    /// Set the result register
    pub fn set_result(&mut self, result: RegisterArg) {
        self.result = Some(result);
    }

    /// Add an argument
    pub fn add_arg(&mut self, arg: InsnArg) {
        self.args.push(arg);
    }

    /// Set the offset
    pub fn set_offset(&mut self, offset: u32) {
        self.offset = offset;
    }

    /// Get the number of arguments
    pub fn args_count(&self) -> usize {
        self.args.len()
    }

    /// Get argument at index
    pub fn get_arg(&self, index: usize) -> Option<&InsnArg> {
        self.args.get(index)
    }

    /// Check if this instruction has a result
    pub fn has_result(&self) -> bool {
        self.result.is_some()
    }

    /// Get the result register number
    pub fn result_reg(&self) -> Option<RegNum> {
        self.result.as_ref().map(|r| r.reg_num)
    }

    // ==================== Builder Methods ====================

    /// Create a NOP instruction
    pub fn nop() -> Self {
        Self::new(InsnType::Nop, 0)
    }

    /// Create a CONST instruction
    pub fn const_val(dest: RegisterArg, value: i64, ty: ArgType) -> Self {
        let mut insn = Self::new(InsnType::Const, 1);
        insn.set_result(dest);
        insn.add_arg(InsnArg::lit(value, ty));
        insn
    }

    /// Create a CONST instruction (alias for const_val with inferred type)
    pub fn const_value(dest: RegisterArg, value: i64) -> Self {
        let ty = if value >= i32::MIN as i64 && value <= i32::MAX as i64 {
            ArgType::INT
        } else {
            ArgType::LONG
        };
        Self::const_val(dest, value, ty)
    }

    /// Create a MOVE instruction
    pub fn mov(dest: RegisterArg, src: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::Move, 1);
        insn.set_result(dest);
        insn.add_arg(src);
        insn
    }

    /// Create a MOVE instruction (alias for mov)
    pub fn move_insn(dest: RegisterArg, src: InsnArg) -> Self {
        Self::mov(dest, src)
    }

    /// Create an ARITH instruction
    pub fn arith(
        op: ArithOp,
        dest: RegisterArg,
        src1: InsnArg,
        src2: InsnArg,
        _ty: ArgType,
    ) -> Self {
        let mut insn = Self::new(InsnType::Arith, 2);
        insn.set_result(dest);
        insn.add_arg(src1);
        insn.add_arg(src2);
        insn.payload.arith_op = Some(op);
        insn
    }

    /// Create a STRING_CONCAT instruction.
    pub fn string_concat(dest: RegisterArg, args: Vec<InsnArg>) -> Self {
        let mut insn = Self::new(InsnType::StringConcat, args.len());
        insn.set_result(dest);
        insn.args = args;
        insn
    }

    /// Create a RETURN instruction
    pub fn ret(value: Option<InsnArg>) -> Self {
        let mut insn = Self::new(InsnType::Return, if value.is_some() { 1 } else { 0 });
        if let Some(v) = value {
            insn.add_arg(v);
        }
        insn
    }

    /// Create a RETURN_VOID instruction
    pub fn return_void() -> Self {
        Self::new(InsnType::Return, 0)
    }

    /// Create a RETURN with value instruction
    pub fn return_value(value: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::Return, 1);
        insn.add_arg(value);
        insn
    }

    /// Create a RETURN instruction from RegisterArg
    pub fn return_insn(src: RegisterArg) -> Self {
        Self::return_value(InsnArg::Reg(src))
    }

    /// Create a CONST instruction (alias for const_value)
    pub fn const_insn(dest: RegisterArg, value: i64) -> Self {
        Self::const_value(dest, value)
    }

    /// Create a CONST_WIDE instruction
    pub fn const_wide(dest: RegisterArg, value: i64) -> Self {
        Self::const_val(dest, value, ArgType::LONG)
    }

    /// Create a GOTO instruction (target is relative offset or block ID)
    pub fn goto(target: i32) -> Self {
        let mut insn = Self::new(InsnType::Goto, 0);
        insn.payload.target = Some(target);
        insn
    }

    /// Create an IF instruction (target is relative offset or block ID)
    pub fn if_cmp(op: IfOp, left: InsnArg, right: InsnArg, target: i32) -> Self {
        let mut insn = Self::new(InsnType::If, 2);
        insn.add_arg(left);
        insn.add_arg(right);
        insn.payload.if_op = Some(op);
        insn.payload.target = Some(target);
        insn
    }

    /// Create a THROW instruction
    pub fn throw(exception: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::Throw, 1);
        insn.add_arg(exception);
        insn
    }

    /// Create a PHI instruction
    pub fn phi(dest: RegisterArg, sources: Vec<(u32, InsnArg)>) -> Self {
        let mut insn = Self::new(InsnType::Phi, sources.len());
        insn.set_result(dest);
        for (predecessor, arg) in sources {
            insn.payload
                .phi_edges
                .push((BlockId::new(predecessor), EdgeKind::Normal));
            insn.add_arg(arg);
        }
        insn
    }

    /// Create a CONST_STRING instruction
    pub fn const_string(dest: RegisterArg, string_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::ConstStr, 0);
        insn.set_result(dest);
        insn.payload.string_index = Some(string_idx);
        insn
    }

    /// Create a CONST_CLASS instruction
    pub fn const_class(dest: RegisterArg, type_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::ConstClass, 0);
        insn.set_result(dest);
        insn.payload.type_index = Some(type_idx);
        insn
    }

    /// Create a MONITOR_ENTER instruction
    pub fn monitor_enter(obj: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::MonitorEnter, 1);
        insn.add_arg(obj);
        insn.payload.is_enter = Some(true);
        insn
    }

    /// Create a MONITOR_EXIT instruction
    pub fn monitor_exit(obj: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::MonitorExit, 1);
        insn.add_arg(obj);
        insn.payload.is_enter = Some(false);
        insn
    }

    /// Create a CHECK_CAST instruction
    pub fn check_cast(obj: InsnArg, type_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::CheckCast, 1);
        insn.add_arg(obj);
        insn.payload.type_index = Some(type_idx);
        insn
    }

    /// Create an INSTANCE_OF instruction
    pub fn instance_of(dest: RegisterArg, obj: InsnArg, type_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::InstanceOf, 1);
        insn.set_result(dest);
        insn.add_arg(obj);
        insn.payload.type_index = Some(type_idx);
        insn
    }

    /// Create an ARRAY_LENGTH instruction
    pub fn array_length(dest: RegisterArg, array: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::ArrayLength, 1);
        insn.set_result(dest);
        insn.add_arg(array);
        insn.payload.is_length = Some(true);
        insn
    }

    /// Create an AGET instruction
    pub fn aget(dest: RegisterArg, array: InsnArg, index: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::Aget, 2);
        insn.set_result(dest);
        insn.add_arg(array);
        insn.add_arg(index);
        insn.payload.is_get = Some(true);
        insn
    }

    /// Create an APUT instruction
    pub fn aput(value: InsnArg, array: InsnArg, index: InsnArg) -> Self {
        let mut insn = Self::new(InsnType::Aput, 3);
        insn.add_arg(value);
        insn.add_arg(array);
        insn.add_arg(index);
        insn.payload.is_get = Some(false);
        insn
    }

    /// Create an IGET instruction
    pub fn iget(dest: RegisterArg, obj: InsnArg, field_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::Iget, 1);
        insn.set_result(dest);
        insn.add_arg(obj);
        insn.payload.field_index = Some(field_idx);
        insn.payload.is_static = Some(false);
        insn.payload.is_get = Some(true);
        insn
    }

    /// Create an IPUT instruction
    pub fn iput(value: InsnArg, obj: InsnArg, field_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::Iput, 2);
        insn.add_arg(value);
        insn.add_arg(obj);
        insn.payload.field_index = Some(field_idx);
        insn.payload.is_static = Some(false);
        insn.payload.is_get = Some(false);
        insn
    }

    /// Create an SGET instruction
    pub fn sget(dest: RegisterArg, field_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::Sget, 0);
        insn.set_result(dest);
        insn.payload.field_index = Some(field_idx);
        insn.payload.is_static = Some(true);
        insn.payload.is_get = Some(true);
        insn
    }

    /// Create an SPUT instruction
    pub fn sput(value: InsnArg, field_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::Sput, 1);
        insn.add_arg(value);
        insn.payload.field_index = Some(field_idx);
        insn.payload.is_static = Some(true);
        insn.payload.is_get = Some(false);
        insn
    }

    /// Create an INVOKE instruction
    pub fn invoke(invoke_type: InvokeType, method_idx: u32, args: Vec<InsnArg>) -> Self {
        let mut insn = Self::new(InsnType::Invoke, args.len());
        for arg in args {
            insn.add_arg(arg);
        }
        insn.payload.invoke_type = Some(invoke_type);
        insn.payload.method_index = Some(method_idx);
        insn
    }

    /// Create a NEW_INSTANCE instruction
    pub fn new_instance(dest: RegisterArg, type_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::NewInstance, 0);
        insn.set_result(dest);
        insn.payload.type_index = Some(type_idx);
        insn
    }

    /// Create a NEW_ARRAY instruction
    pub fn new_array(dest: RegisterArg, size: InsnArg, type_idx: u32) -> Self {
        let mut insn = Self::new(InsnType::NewArray, 1);
        insn.set_result(dest);
        insn.add_arg(size);
        insn.payload.type_index = Some(type_idx);
        insn
    }

    /// Create a SWITCH instruction (targets are offsets stored as i32)
    pub fn switch(value: InsnArg, cases: Vec<(i32, i32)>) -> Self {
        let mut insn = Self::new(InsnType::Switch, 1);
        insn.add_arg(value);
        insn.payload.switch_cases = Some(cases);
        insn
    }

    /// Create a CMP instruction
    pub fn cmp(dest: RegisterArg, src1: InsnArg, src2: InsnArg, bias: CmpBias) -> Self {
        let mut insn = Self::new(InsnType::Cmp, 2);
        insn.set_result(dest);
        insn.add_arg(src1);
        insn.add_arg(src2);
        insn.payload.cmp_bias = Some(bias);
        insn
    }

    /// Create a UNARY instruction (neg, not, or type conversion)
    pub fn unary(op: UnaryOp, dest: RegisterArg, src: InsnArg) -> Self {
        let insn_type = match op {
            UnaryOp::Neg => InsnType::Neg,
            UnaryOp::Not => InsnType::Not,
            _ => InsnType::Cast,
        };
        let mut insn = Self::new(insn_type, 1);
        if insn_type == InsnType::Cast {
            insn.payload.cast_type = Some(dest.ty.clone());
        }
        insn.set_result(dest);
        insn.add_arg(src);
        insn.payload.unary_op = Some(op);
        insn
    }

    /// Create a MOVE_RESULT instruction
    pub fn move_result(dest: RegisterArg) -> Self {
        let mut insn = Self::new(InsnType::MoveResult, 0);
        insn.set_result(dest);
        insn
    }

    /// Create a MOVE_EXCEPTION instruction
    pub fn move_exception(dest: RegisterArg) -> Self {
        let mut insn = Self::new(InsnType::MoveException, 0);
        insn.set_result(dest);
        insn
    }

    /// Create a FILL_ARRAY_DATA instruction
    pub fn fill_array(array: InsnArg, data_offset: u32) -> Self {
        Self::fill_array_with_data(array, data_offset, None)
    }

    /// Create a FILL_ARRAY_DATA instruction with decoded payload.
    pub fn fill_array_with_data(
        array: InsnArg,
        data_offset: u32,
        data: Option<FillArrayData>,
    ) -> Self {
        let mut insn = Self::new(InsnType::FillArray, 1);
        insn.add_arg(array);
        insn.payload.target = Some(data_offset as i32);
        insn.payload.fill_array_data = data;
        insn
    }

    /// Create a FILLED_NEW_ARRAY instruction
    pub fn filled_new_array(dest: RegisterArg, type_idx: u32, elements: Vec<InsnArg>) -> Self {
        let mut insn = Self::new(InsnType::FilledNewArray, elements.len());
        insn.set_result(dest);
        for elem in elements {
            insn.add_arg(elem);
        }
        insn.payload.type_index = Some(type_idx);
        insn
    }

    /// Get instruction type
    pub fn insn_type(&self) -> InsnType {
        self.insn_type
    }

    /// Get target offset for control flow instructions
    pub fn get_target(&self) -> Option<i32> {
        self.payload.target
    }

    /// Get switch cases
    pub fn get_switch_cases(&self) -> Option<&Vec<(i32, i32)>> {
        self.payload.switch_cases.as_ref()
    }
}

impl fmt::Display for InsnNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Result
        if let Some(ref result) = self.result {
            write!(f, "{} = ", result)?;
        }

        // Instruction type specific formatting
        match self.insn_type {
            InsnType::Const => {
                if let Some(arg) = self.args.first() {
                    write!(f, "{}", arg)?;
                }
            }
            InsnType::ConstStr => {
                if let Some(ref s) = self.payload.string_value {
                    write!(f, "\"{}\"", s)?;
                }
            }
            InsnType::ConstClass => {
                if let Some(ref ty) = self.payload.class_type {
                    write!(f, "{}.class", ty)?;
                }
            }
            InsnType::Arith => {
                if let (Some(op), Some(arg1), Some(arg2)) =
                    (self.payload.arith_op, self.args.get(0), self.args.get(1))
                {
                    write!(f, "{} {} {}", arg1, op, arg2)?;
                }
            }
            InsnType::StringConcat => {
                for (idx, arg) in self.args.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " + ")?;
                    }
                    write!(f, "{}", arg)?;
                }
            }
            InsnType::Neg => {
                if let Some(arg) = self.args.first() {
                    write!(f, "-{}", arg)?;
                }
            }
            InsnType::Not => {
                if let Some(arg) = self.args.first() {
                    write!(f, "~{}", arg)?;
                }
            }
            InsnType::Move => {
                if let Some(arg) = self.args.first() {
                    write!(f, "{}", arg)?;
                }
            }
            InsnType::Return => {
                write!(f, "return")?;
                if let Some(arg) = self.args.first() {
                    write!(f, " {}", arg)?;
                }
            }
            InsnType::Goto => {
                if let Some(target) = self.payload.target {
                    write!(f, "goto {:+}", target)?;
                }
            }
            InsnType::If => {
                if let (Some(op), Some(arg1), Some(arg2), Some(target)) = (
                    self.payload.if_op,
                    self.args.get(0),
                    self.args.get(1),
                    self.payload.target,
                ) {
                    write!(f, "if ({} {} {}) goto {:+}", arg1, op, arg2, target)?;
                }
            }
            InsnType::Throw => {
                if let Some(arg) = self.args.first() {
                    write!(f, "throw {}", arg)?;
                }
            }
            InsnType::Invoke => {
                if let Some(ref method) = self.payload.reference {
                    write!(f, "invoke {}", method)?;
                    write!(f, "(")?;
                    for (i, arg) in self.args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")?;
                }
            }
            InsnType::Phi => {
                write!(f, "phi(")?;
                for (i, arg) in self.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")?;
            }
            InsnType::Nop => {
                write!(f, "nop")?;
            }
            _ => {
                write!(f, "{:?}", self.insn_type)?;
                if !self.args.is_empty() {
                    write!(f, " ")?;
                    for (i, arg) in self.args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arith_op_display() {
        assert_eq!(format!("{}", ArithOp::Add), "+");
        assert_eq!(format!("{}", ArithOp::Shl), "<<");
    }

    #[test]
    fn test_if_op_invert() {
        assert_eq!(IfOp::Eq.invert(), IfOp::Ne);
        assert_eq!(IfOp::Lt.invert(), IfOp::Ge);
    }

    #[test]
    fn test_insn_const() {
        let dest = RegisterArg::new(0, ArgType::INT);
        let insn = InsnNode::const_val(dest, 42, ArgType::INT);
        assert!(insn.has_result());
        assert_eq!(insn.result_reg(), Some(0));
        assert_eq!(format!("{}", insn), "v0 = 42");
    }

    #[test]
    fn test_insn_arith() {
        let dest = RegisterArg::new(0, ArgType::INT);
        let src1 = InsnArg::reg(1, ArgType::INT);
        let src2 = InsnArg::reg(2, ArgType::INT);
        let insn = InsnNode::arith(ArithOp::Add, dest, src1, src2, ArgType::INT);
        assert_eq!(format!("{}", insn), "v0 = v1 + v2");
    }

    #[test]
    fn test_insn_return() {
        let ret_void = InsnNode::ret(None);
        assert_eq!(format!("{}", ret_void), "return");

        let ret_val = InsnNode::ret(Some(InsnArg::reg(0, ArgType::INT)));
        assert_eq!(format!("{}", ret_val), "return v0");
    }

    #[test]
    fn check_cast_exposes_its_semantic_conversion_type() {
        let target = ArgType::array(ArgType::string());
        let mut instruction = InsnNode::check_cast(InsnArg::reg(0, ArgType::unknown_object()), 7);
        instruction.payload.class_type = Some(target.clone());

        assert_eq!(instruction.conversion_type(), Some(&target));
    }
}
