//! Method Decoder - Decode DEX bytecode to IR instructions
//!
//! This decoder only decodes raw bytecode to InsnNode list.
//! CFG construction is handled by the Splitter.

use crate::frontend::{MethodCode, TryCatchBlock};
use crate::ir::arg::{InsnArg, RegNum, RegisterArg};
use crate::ir::block::ExceptionHandler;
use crate::ir::insn::{ArithOp, CmpBias, FillArrayData, IfOp, InsnNode, InvokeType, UnaryOp};
use crate::ir::ty::ArgType;

/// Dalvik opcode constants
mod opcode {
    pub const NOP: u8 = 0x00;
    pub const MOVE: u8 = 0x01;
    pub const MOVE_FROM16: u8 = 0x02;
    pub const MOVE_16: u8 = 0x03;
    pub const MOVE_WIDE: u8 = 0x04;
    pub const MOVE_WIDE_FROM16: u8 = 0x05;
    pub const MOVE_WIDE_16: u8 = 0x06;
    pub const MOVE_OBJECT: u8 = 0x07;
    pub const MOVE_OBJECT_FROM16: u8 = 0x08;
    pub const MOVE_OBJECT_16: u8 = 0x09;
    pub const MOVE_RESULT: u8 = 0x0a;
    pub const MOVE_RESULT_WIDE: u8 = 0x0b;
    pub const MOVE_RESULT_OBJECT: u8 = 0x0c;
    pub const MOVE_EXCEPTION: u8 = 0x0d;
    pub const RETURN_VOID: u8 = 0x0e;
    pub const RETURN: u8 = 0x0f;
    pub const RETURN_WIDE: u8 = 0x10;
    pub const RETURN_OBJECT: u8 = 0x11;
    pub const CONST_4: u8 = 0x12;
    pub const CONST_16: u8 = 0x13;
    pub const CONST: u8 = 0x14;
    pub const CONST_HIGH16: u8 = 0x15;
    pub const CONST_WIDE_16: u8 = 0x16;
    pub const CONST_WIDE_32: u8 = 0x17;
    pub const CONST_WIDE: u8 = 0x18;
    pub const CONST_WIDE_HIGH16: u8 = 0x19;
    pub const CONST_STRING: u8 = 0x1a;
    pub const CONST_STRING_JUMBO: u8 = 0x1b;
    pub const CONST_CLASS: u8 = 0x1c;
    pub const MONITOR_ENTER: u8 = 0x1d;
    pub const MONITOR_EXIT: u8 = 0x1e;
    pub const CHECK_CAST: u8 = 0x1f;
    pub const INSTANCE_OF: u8 = 0x20;
    pub const ARRAY_LENGTH: u8 = 0x21;
    pub const NEW_INSTANCE: u8 = 0x22;
    pub const NEW_ARRAY: u8 = 0x23;
    pub const FILLED_NEW_ARRAY: u8 = 0x24;
    pub const FILLED_NEW_ARRAY_RANGE: u8 = 0x25;
    pub const FILL_ARRAY_DATA: u8 = 0x26;
    pub const THROW: u8 = 0x27;
    pub const GOTO: u8 = 0x28;
    pub const GOTO_16: u8 = 0x29;
    pub const GOTO_32: u8 = 0x2a;
    pub const PACKED_SWITCH: u8 = 0x2b;
    pub const SPARSE_SWITCH: u8 = 0x2c;
    pub const CMPL_FLOAT: u8 = 0x2d;
    pub const CMPG_FLOAT: u8 = 0x2e;
    pub const CMPL_DOUBLE: u8 = 0x2f;
    pub const CMPG_DOUBLE: u8 = 0x30;
    pub const CMP_LONG: u8 = 0x31;
    pub const IF_EQ: u8 = 0x32;
    pub const IF_NE: u8 = 0x33;
    pub const IF_LT: u8 = 0x34;
    pub const IF_GE: u8 = 0x35;
    pub const IF_GT: u8 = 0x36;
    pub const IF_LE: u8 = 0x37;
    pub const IF_EQZ: u8 = 0x38;
    pub const IF_NEZ: u8 = 0x39;
    pub const IF_LTZ: u8 = 0x3a;
    pub const IF_GEZ: u8 = 0x3b;
    pub const IF_GTZ: u8 = 0x3c;
    pub const IF_LEZ: u8 = 0x3d;
    pub const AGET: u8 = 0x44;
    pub const AGET_WIDE: u8 = 0x45;
    pub const AGET_OBJECT: u8 = 0x46;
    pub const AGET_BOOLEAN: u8 = 0x47;
    pub const AGET_BYTE: u8 = 0x48;
    pub const AGET_CHAR: u8 = 0x49;
    pub const AGET_SHORT: u8 = 0x4a;
    pub const APUT: u8 = 0x4b;
    pub const APUT_WIDE: u8 = 0x4c;
    pub const APUT_OBJECT: u8 = 0x4d;
    pub const APUT_BOOLEAN: u8 = 0x4e;
    pub const APUT_BYTE: u8 = 0x4f;
    pub const APUT_CHAR: u8 = 0x50;
    pub const APUT_SHORT: u8 = 0x51;
    pub const IGET: u8 = 0x52;
    pub const IGET_WIDE: u8 = 0x53;
    pub const IGET_OBJECT: u8 = 0x54;
    pub const IGET_BOOLEAN: u8 = 0x55;
    pub const IGET_BYTE: u8 = 0x56;
    pub const IGET_CHAR: u8 = 0x57;
    pub const IGET_SHORT: u8 = 0x58;
    pub const IPUT: u8 = 0x59;
    pub const IPUT_WIDE: u8 = 0x5a;
    pub const IPUT_OBJECT: u8 = 0x5b;
    pub const IPUT_BOOLEAN: u8 = 0x5c;
    pub const IPUT_BYTE: u8 = 0x5d;
    pub const IPUT_CHAR: u8 = 0x5e;
    pub const IPUT_SHORT: u8 = 0x5f;
    pub const SGET: u8 = 0x60;
    pub const SGET_WIDE: u8 = 0x61;
    pub const SGET_OBJECT: u8 = 0x62;
    pub const SGET_BOOLEAN: u8 = 0x63;
    pub const SGET_BYTE: u8 = 0x64;
    pub const SGET_CHAR: u8 = 0x65;
    pub const SGET_SHORT: u8 = 0x66;
    pub const SPUT: u8 = 0x67;
    pub const SPUT_WIDE: u8 = 0x68;
    pub const SPUT_OBJECT: u8 = 0x69;
    pub const SPUT_BOOLEAN: u8 = 0x6a;
    pub const SPUT_BYTE: u8 = 0x6b;
    pub const SPUT_CHAR: u8 = 0x6c;
    pub const SPUT_SHORT: u8 = 0x6d;
    pub const INVOKE_VIRTUAL: u8 = 0x6e;
    pub const INVOKE_SUPER: u8 = 0x6f;
    pub const INVOKE_DIRECT: u8 = 0x70;
    pub const INVOKE_STATIC: u8 = 0x71;
    pub const INVOKE_INTERFACE: u8 = 0x72;
    pub const INVOKE_VIRTUAL_RANGE: u8 = 0x74;
    pub const INVOKE_SUPER_RANGE: u8 = 0x75;
    pub const INVOKE_DIRECT_RANGE: u8 = 0x76;
    pub const INVOKE_STATIC_RANGE: u8 = 0x77;
    pub const INVOKE_INTERFACE_RANGE: u8 = 0x78;
    pub const NEG_INT: u8 = 0x7b;
    pub const NOT_INT: u8 = 0x7c;
    pub const NEG_LONG: u8 = 0x7d;
    pub const NOT_LONG: u8 = 0x7e;
    pub const NEG_FLOAT: u8 = 0x7f;
    pub const NEG_DOUBLE: u8 = 0x80;
    pub const INT_TO_LONG: u8 = 0x81;
    pub const INT_TO_FLOAT: u8 = 0x82;
    pub const INT_TO_DOUBLE: u8 = 0x83;
    pub const LONG_TO_INT: u8 = 0x84;
    pub const LONG_TO_FLOAT: u8 = 0x85;
    pub const LONG_TO_DOUBLE: u8 = 0x86;
    pub const FLOAT_TO_INT: u8 = 0x87;
    pub const FLOAT_TO_LONG: u8 = 0x88;
    pub const FLOAT_TO_DOUBLE: u8 = 0x89;
    pub const DOUBLE_TO_INT: u8 = 0x8a;
    pub const DOUBLE_TO_LONG: u8 = 0x8b;
    pub const DOUBLE_TO_FLOAT: u8 = 0x8c;
    pub const INT_TO_BYTE: u8 = 0x8d;
    pub const INT_TO_CHAR: u8 = 0x8e;
    pub const INT_TO_SHORT: u8 = 0x8f;
    pub const ADD_INT: u8 = 0x90;
    pub const SUB_INT: u8 = 0x91;
    pub const MUL_INT: u8 = 0x92;
    pub const DIV_INT: u8 = 0x93;
    pub const REM_INT: u8 = 0x94;
    pub const AND_INT: u8 = 0x95;
    pub const OR_INT: u8 = 0x96;
    pub const XOR_INT: u8 = 0x97;
    pub const SHL_INT: u8 = 0x98;
    pub const SHR_INT: u8 = 0x99;
    pub const USHR_INT: u8 = 0x9a;
    pub const ADD_LONG: u8 = 0x9b;
    pub const SUB_LONG: u8 = 0x9c;
    pub const MUL_LONG: u8 = 0x9d;
    pub const DIV_LONG: u8 = 0x9e;
    pub const REM_LONG: u8 = 0x9f;
    pub const AND_LONG: u8 = 0xa0;
    pub const OR_LONG: u8 = 0xa1;
    pub const XOR_LONG: u8 = 0xa2;
    pub const SHL_LONG: u8 = 0xa3;
    pub const SHR_LONG: u8 = 0xa4;
    pub const USHR_LONG: u8 = 0xa5;
    pub const ADD_FLOAT: u8 = 0xa6;
    pub const SUB_FLOAT: u8 = 0xa7;
    pub const MUL_FLOAT: u8 = 0xa8;
    pub const DIV_FLOAT: u8 = 0xa9;
    pub const REM_FLOAT: u8 = 0xaa;
    pub const ADD_DOUBLE: u8 = 0xab;
    pub const SUB_DOUBLE: u8 = 0xac;
    pub const MUL_DOUBLE: u8 = 0xad;
    pub const DIV_DOUBLE: u8 = 0xae;
    pub const REM_DOUBLE: u8 = 0xaf;
    pub const ADD_INT_2ADDR: u8 = 0xb0;
    pub const SUB_INT_2ADDR: u8 = 0xb1;
    pub const MUL_INT_2ADDR: u8 = 0xb2;
    pub const DIV_INT_2ADDR: u8 = 0xb3;
    pub const REM_INT_2ADDR: u8 = 0xb4;
    pub const AND_INT_2ADDR: u8 = 0xb5;
    pub const OR_INT_2ADDR: u8 = 0xb6;
    pub const XOR_INT_2ADDR: u8 = 0xb7;
    pub const SHL_INT_2ADDR: u8 = 0xb8;
    pub const SHR_INT_2ADDR: u8 = 0xb9;
    pub const USHR_INT_2ADDR: u8 = 0xba;
    pub const ADD_LONG_2ADDR: u8 = 0xbb;
    pub const SUB_LONG_2ADDR: u8 = 0xbc;
    pub const MUL_LONG_2ADDR: u8 = 0xbd;
    pub const DIV_LONG_2ADDR: u8 = 0xbe;
    pub const REM_LONG_2ADDR: u8 = 0xbf;
    pub const AND_LONG_2ADDR: u8 = 0xc0;
    pub const OR_LONG_2ADDR: u8 = 0xc1;
    pub const XOR_LONG_2ADDR: u8 = 0xc2;
    pub const SHL_LONG_2ADDR: u8 = 0xc3;
    pub const SHR_LONG_2ADDR: u8 = 0xc4;
    pub const USHR_LONG_2ADDR: u8 = 0xc5;
    pub const ADD_FLOAT_2ADDR: u8 = 0xc6;
    pub const SUB_FLOAT_2ADDR: u8 = 0xc7;
    pub const MUL_FLOAT_2ADDR: u8 = 0xc8;
    pub const DIV_FLOAT_2ADDR: u8 = 0xc9;
    pub const REM_FLOAT_2ADDR: u8 = 0xca;
    pub const ADD_DOUBLE_2ADDR: u8 = 0xcb;
    pub const SUB_DOUBLE_2ADDR: u8 = 0xcc;
    pub const MUL_DOUBLE_2ADDR: u8 = 0xcd;
    pub const DIV_DOUBLE_2ADDR: u8 = 0xce;
    pub const REM_DOUBLE_2ADDR: u8 = 0xcf;
    pub const ADD_INT_LIT16: u8 = 0xd0;
    pub const RSUB_INT: u8 = 0xd1;
    pub const MUL_INT_LIT16: u8 = 0xd2;
    pub const DIV_INT_LIT16: u8 = 0xd3;
    pub const REM_INT_LIT16: u8 = 0xd4;
    pub const AND_INT_LIT16: u8 = 0xd5;
    pub const OR_INT_LIT16: u8 = 0xd6;
    pub const XOR_INT_LIT16: u8 = 0xd7;
    pub const ADD_INT_LIT8: u8 = 0xd8;
    pub const RSUB_INT_LIT8: u8 = 0xd9;
    pub const MUL_INT_LIT8: u8 = 0xda;
    pub const DIV_INT_LIT8: u8 = 0xdb;
    pub const REM_INT_LIT8: u8 = 0xdc;
    pub const AND_INT_LIT8: u8 = 0xdd;
    pub const OR_INT_LIT8: u8 = 0xde;
    pub const XOR_INT_LIT8: u8 = 0xdf;
    pub const SHL_INT_LIT8: u8 = 0xe0;
    pub const SHR_INT_LIT8: u8 = 0xe1;
    pub const USHR_INT_LIT8: u8 = 0xe2;
}

/// Decode result
#[derive(Debug, Clone)]
pub struct DecodeResult {
    pub insns: Vec<InsnNode>,
    pub handlers: Vec<ExceptionHandler>,
    pub registers: u32,
    pub ins: u32,
}

/// Method decoder - converts bytecode to instruction list
pub struct MethodDecoder<'a> {
    insns: &'a [u16],
    tries: &'a [TryCatchBlock],
    registers_size: u16,
    ins_size: u16,
}

impl<'a> MethodDecoder<'a> {
    /// Create from MethodCode
    pub fn from_code(code: &'a MethodCode) -> Self {
        Self {
            insns: &code.insns,
            tries: &code.tries,
            registers_size: code.registers_size,
            ins_size: code.ins_size,
        }
    }

    /// Decode to instruction list and metadata
    pub fn decode(&self) -> DecodeResult {
        let insns = self.decode_instructions();
        let handlers = self.extract_handlers();

        DecodeResult {
            insns,
            handlers,
            registers: self.registers_size as u32,
            ins: self.ins_size as u32,
        }
    }

    /// Decode all instructions
    fn decode_instructions(&self) -> Vec<InsnNode> {
        let mut result = Vec::new();
        let code_size = self.insns.len();
        let mut pc = 0usize;

        while pc < code_size {
            let word = self.insns[pc];
            let op = (word & 0xff) as u8;
            let length = instruction_length(op, &self.insns[pc..]);

            if let Some(mut insn) = self.decode_instruction(pc, op) {
                insn.set_offset(pc as u32);
                result.push(insn);
            }
            pc += length;
        }

        result
    }

    /// Extract exception handlers
    fn extract_handlers(&self) -> Vec<ExceptionHandler> {
        let mut handlers = Vec::new();
        for try_block in self.tries {
            for handler in &try_block.handlers {
                handlers.push(ExceptionHandler::new(
                    try_block.start_addr,
                    try_block.end_addr,
                    handler.handler_addr,
                    handler.exception_type.clone(),
                ));
            }
        }
        handlers
    }

    /// Decode a single instruction
    fn decode_instruction(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;

        let word = self.insns[pc];
        let a = ((word >> 8) & 0xf) as u16;
        let b = ((word >> 12) & 0xf) as u16;
        let aa = (word >> 8) as u16;

        match op {
            NOP => {
                if word == 0x0100 || word == 0x0200 || word == 0x0300 {
                    return None; // Payload
                }
                Some(InsnNode::nop())
            }

            // Move instructions
            MOVE => {
                let dest = RegisterArg::new(a as RegNum, ArgType::narrow());
                let src = RegisterArg::new(b as RegNum, ArgType::narrow());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_FROM16 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::narrow());
                let src = RegisterArg::new(self.word_at(pc + 1) as RegNum, ArgType::narrow());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_16 => {
                let dest = RegisterArg::new(self.word_at(pc + 1) as RegNum, ArgType::narrow());
                let src = RegisterArg::new(self.word_at(pc + 2) as RegNum, ArgType::narrow());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_WIDE => {
                let dest = RegisterArg::new(a as RegNum, ArgType::wide());
                let src = RegisterArg::new(b as RegNum, ArgType::wide());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_WIDE_FROM16 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::wide());
                let src = RegisterArg::new(self.word_at(pc + 1) as RegNum, ArgType::wide());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_WIDE_16 => {
                let dest = RegisterArg::new(self.word_at(pc + 1) as RegNum, ArgType::wide());
                let src = RegisterArg::new(self.word_at(pc + 2) as RegNum, ArgType::wide());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_OBJECT => {
                let dest = RegisterArg::new(a as RegNum, ArgType::unknown_object());
                let src = RegisterArg::new(b as RegNum, ArgType::unknown_object());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_OBJECT_FROM16 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                let src =
                    RegisterArg::new(self.word_at(pc + 1) as RegNum, ArgType::unknown_object());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_OBJECT_16 => {
                let dest =
                    RegisterArg::new(self.word_at(pc + 1) as RegNum, ArgType::unknown_object());
                let src =
                    RegisterArg::new(self.word_at(pc + 2) as RegNum, ArgType::unknown_object());
                Some(InsnNode::move_insn(dest, InsnArg::Reg(src)))
            }
            MOVE_RESULT => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::narrow());
                Some(InsnNode::move_result(dest))
            }
            MOVE_RESULT_WIDE => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::wide());
                Some(InsnNode::move_result(dest))
            }
            MOVE_RESULT_OBJECT => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                Some(InsnNode::move_result(dest))
            }
            MOVE_EXCEPTION => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                Some(InsnNode::move_exception(dest))
            }

            // Return instructions
            RETURN_VOID => Some(InsnNode::return_void()),
            RETURN => {
                let src = RegisterArg::new(aa as RegNum, ArgType::narrow());
                Some(InsnNode::return_insn(src))
            }
            RETURN_WIDE => {
                let src = RegisterArg::new(aa as RegNum, ArgType::wide());
                Some(InsnNode::return_insn(src))
            }
            RETURN_OBJECT => {
                let src = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                Some(InsnNode::return_insn(src))
            }

            // Const instructions
            CONST_4 => {
                let dest = RegisterArg::new(a as RegNum, ArgType::INT);
                let lit = sign_extend_4(b as i32);
                Some(InsnNode::const_insn(dest, lit as i64))
            }
            CONST_16 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::INT);
                let lit = self.word_at(pc + 1) as i16 as i64;
                Some(InsnNode::const_insn(dest, lit))
            }
            CONST => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::INT);
                let lit = self.dword_at(pc + 1) as i32 as i64;
                Some(InsnNode::const_insn(dest, lit))
            }
            CONST_HIGH16 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::INT);
                let lit = ((self.word_at(pc + 1) as u32) << 16) as i32 as i64;
                Some(InsnNode::const_insn(dest, lit))
            }
            CONST_WIDE_16 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::LONG);
                let lit = self.word_at(pc + 1) as i16 as i64;
                Some(InsnNode::const_wide(dest, lit))
            }
            CONST_WIDE_32 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::LONG);
                let lit = self.dword_at(pc + 1) as i32 as i64;
                Some(InsnNode::const_wide(dest, lit))
            }
            CONST_WIDE => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::LONG);
                let lit = self.qword_at(pc + 1) as i64;
                Some(InsnNode::const_wide(dest, lit))
            }
            CONST_WIDE_HIGH16 => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::LONG);
                let lit = ((self.word_at(pc + 1) as u64) << 48) as i64;
                Some(InsnNode::const_wide(dest, lit))
            }
            CONST_STRING => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                let idx = self.word_at(pc + 1) as u32;
                Some(InsnNode::const_string(dest, idx))
            }
            CONST_STRING_JUMBO => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                let idx = self.dword_at(pc + 1);
                Some(InsnNode::const_string(dest, idx))
            }
            CONST_CLASS => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                let idx = self.word_at(pc + 1) as u32;
                Some(InsnNode::const_class(dest, idx))
            }

            // Monitor
            MONITOR_ENTER => {
                let reg = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                Some(InsnNode::monitor_enter(InsnArg::Reg(reg)))
            }
            MONITOR_EXIT => {
                let reg = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                Some(InsnNode::monitor_exit(InsnArg::Reg(reg)))
            }

            // Type check
            CHECK_CAST => {
                let reg = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                let idx = self.word_at(pc + 1) as u32;
                Some(InsnNode::check_cast(InsnArg::Reg(reg), idx))
            }
            INSTANCE_OF => {
                let dest = RegisterArg::new(a as RegNum, ArgType::BOOLEAN);
                let src = RegisterArg::new(b as RegNum, ArgType::unknown_object());
                let idx = self.word_at(pc + 1) as u32;
                Some(InsnNode::instance_of(dest, InsnArg::Reg(src), idx))
            }

            // Array
            ARRAY_LENGTH => {
                let dest = RegisterArg::new(a as RegNum, ArgType::INT);
                let arr = RegisterArg::new(b as RegNum, ArgType::unknown_object());
                Some(InsnNode::array_length(dest, InsnArg::Reg(arr)))
            }
            NEW_INSTANCE => {
                let dest = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                let idx = self.word_at(pc + 1) as u32;
                Some(InsnNode::new_instance(dest, idx))
            }
            NEW_ARRAY => {
                let dest = RegisterArg::new(a as RegNum, ArgType::unknown_object());
                let size = RegisterArg::new(b as RegNum, ArgType::INT);
                let idx = self.word_at(pc + 1) as u32;
                Some(InsnNode::new_array(dest, InsnArg::Reg(size), idx))
            }

            // Throw
            THROW => {
                let ex = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                Some(InsnNode::throw(InsnArg::Reg(ex)))
            }

            // Goto
            GOTO => {
                let offset = sign_extend_8(aa as i32);
                let target = pc as i32 + offset;
                Some(InsnNode::goto(target))
            }
            GOTO_16 => {
                let offset = self.word_at(pc + 1) as i16 as i32;
                let target = pc as i32 + offset;
                Some(InsnNode::goto(target))
            }
            GOTO_32 => {
                let offset = self.dword_at(pc + 1) as i32;
                let target = pc as i32 + offset;
                Some(InsnNode::goto(target))
            }

            // Switch
            PACKED_SWITCH => {
                let reg = RegisterArg::new(aa as RegNum, ArgType::INT);
                let payload_offset = self.dword_at(pc + 1) as i32;
                let payload_addr = (pc as i32 + payload_offset) as usize;
                let cases = self.decode_packed_switch(pc, payload_addr);
                Some(InsnNode::switch(InsnArg::Reg(reg), cases))
            }
            SPARSE_SWITCH => {
                let reg = RegisterArg::new(aa as RegNum, ArgType::INT);
                let payload_offset = self.dword_at(pc + 1) as i32;
                let payload_addr = (pc as i32 + payload_offset) as usize;
                let cases = self.decode_sparse_switch(pc, payload_addr);
                Some(InsnNode::switch(InsnArg::Reg(reg), cases))
            }

            // Compare
            CMPL_FLOAT => self.decode_cmp(pc, CmpBias::Lt, ArgType::FLOAT),
            CMPG_FLOAT => self.decode_cmp(pc, CmpBias::Gt, ArgType::FLOAT),
            CMPL_DOUBLE => self.decode_cmp(pc, CmpBias::Lt, ArgType::DOUBLE),
            CMPG_DOUBLE => self.decode_cmp(pc, CmpBias::Gt, ArgType::DOUBLE),
            CMP_LONG => self.decode_cmp(pc, CmpBias::None, ArgType::LONG),

            // If
            IF_EQ..=IF_LE => {
                let ifop = match op {
                    IF_EQ => IfOp::Eq,
                    IF_NE => IfOp::Ne,
                    IF_LT => IfOp::Lt,
                    IF_GE => IfOp::Ge,
                    IF_GT => IfOp::Gt,
                    IF_LE => IfOp::Le,
                    _ => IfOp::Eq,
                };
                let operand_type = if matches!(ifop, IfOp::Eq | IfOp::Ne) {
                    ArgType::equality_operand()
                } else {
                    ArgType::INT
                };
                let r1 = RegisterArg::new(a as RegNum, operand_type.clone());
                let r2 = RegisterArg::new(b as RegNum, operand_type);
                let offset = self.word_at(pc + 1) as i16 as i32;
                let target = pc as i32 + offset;
                Some(InsnNode::if_cmp(
                    ifop,
                    InsnArg::Reg(r1),
                    InsnArg::Reg(r2),
                    target,
                ))
            }
            IF_EQZ..=IF_LEZ => {
                let ifop = match op {
                    IF_EQZ => IfOp::Eq,
                    IF_NEZ => IfOp::Ne,
                    IF_LTZ => IfOp::Lt,
                    IF_GEZ => IfOp::Ge,
                    IF_GTZ => IfOp::Gt,
                    IF_LEZ => IfOp::Le,
                    _ => IfOp::Eq,
                };
                let operand_type = if matches!(ifop, IfOp::Eq | IfOp::Ne) {
                    ArgType::equality_operand()
                } else {
                    ArgType::INT
                };
                let r = RegisterArg::new(aa as RegNum, operand_type.clone());
                let offset = self.word_at(pc + 1) as i16 as i32;
                let target = pc as i32 + offset;
                Some(InsnNode::if_cmp(
                    ifop,
                    InsnArg::Reg(r),
                    InsnArg::lit(0, operand_type),
                    target,
                ))
            }

            // Array access
            AGET..=AGET_SHORT => self.decode_aget(pc, op),
            APUT..=APUT_SHORT => self.decode_aput(pc, op),

            // Field access
            IGET..=IGET_SHORT => self.decode_iget(pc, op),
            IPUT..=IPUT_SHORT => self.decode_iput(pc, op),
            SGET..=SGET_SHORT => self.decode_sget(pc, op),
            SPUT..=SPUT_SHORT => self.decode_sput(pc, op),

            // Invoke
            INVOKE_VIRTUAL..=INVOKE_INTERFACE => self.decode_invoke(pc, op, false),
            INVOKE_VIRTUAL_RANGE..=INVOKE_INTERFACE_RANGE => self.decode_invoke(pc, op, true),

            // Unary
            NEG_INT..=INT_TO_SHORT => self.decode_unary(pc, op),

            // Binary
            ADD_INT..=REM_DOUBLE => self.decode_binary(pc, op),
            ADD_INT_2ADDR..=REM_DOUBLE_2ADDR => self.decode_binary_2addr(pc, op),
            ADD_INT_LIT16..=XOR_INT_LIT16 => self.decode_binary_lit16(pc, op),
            ADD_INT_LIT8..=USHR_INT_LIT8 => self.decode_binary_lit8(pc, op),

            // Fill array data
            FILL_ARRAY_DATA => {
                let arr = RegisterArg::new(aa as RegNum, ArgType::unknown_object());
                let offset = self.dword_at(pc + 1) as i32;
                let payload_addr = (pc as i32 + offset) as usize;
                let data = self.decode_fill_array_data(payload_addr);
                Some(InsnNode::fill_array_with_data(
                    InsnArg::Reg(arr),
                    payload_addr as u32,
                    data,
                ))
            }

            // Filled new array
            FILLED_NEW_ARRAY | FILLED_NEW_ARRAY_RANGE => self.decode_filled_new_array(pc, op),

            _ => Some(InsnNode::nop()),
        }
    }

    // Helper: get word at offset
    fn word_at(&self, pc: usize) -> u16 {
        self.insns.get(pc).copied().unwrap_or(0)
    }

    // Helper: get dword at offset
    fn dword_at(&self, pc: usize) -> u32 {
        let lo = self.word_at(pc) as u32;
        let hi = self.word_at(pc + 1) as u32;
        lo | (hi << 16)
    }

    // Helper: get qword at offset
    fn qword_at(&self, pc: usize) -> u64 {
        let lo = self.dword_at(pc) as u64;
        let hi = self.dword_at(pc + 2) as u64;
        lo | (hi << 32)
    }

    // Decode compare instruction
    fn decode_cmp(&self, pc: usize, bias: CmpBias, arg_type: ArgType) -> Option<InsnNode> {
        let word = self.insns[pc];
        let aa = (word >> 8) as u16;
        let word2 = self.word_at(pc + 1);
        let bb = word2 & 0xff;
        let cc = (word2 >> 8) & 0xff;

        let dest = RegisterArg::new(aa as RegNum, ArgType::INT);
        let src1 = RegisterArg::new(bb as RegNum, arg_type.clone());
        let src2 = RegisterArg::new(cc as RegNum, arg_type);
        Some(InsnNode::cmp(
            dest,
            InsnArg::Reg(src1),
            InsnArg::Reg(src2),
            bias,
        ))
    }

    // Decode array get
    fn decode_aget(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;
        let word = self.insns[pc];
        let aa = (word >> 8) as u16;
        let word2 = self.word_at(pc + 1);
        let bb = word2 & 0xff;
        let cc = (word2 >> 8) & 0xff;

        let elem_type = match op {
            AGET => ArgType::INT,
            AGET_WIDE => ArgType::LONG,
            AGET_OBJECT => ArgType::unknown_object(),
            AGET_BOOLEAN => ArgType::BOOLEAN,
            AGET_BYTE => ArgType::BYTE,
            AGET_CHAR => ArgType::CHAR,
            AGET_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        let dest = RegisterArg::new(aa as RegNum, elem_type);
        let arr = RegisterArg::new(bb as RegNum, ArgType::unknown_object());
        let idx = RegisterArg::new(cc as RegNum, ArgType::INT);
        Some(InsnNode::aget(dest, InsnArg::Reg(arr), InsnArg::Reg(idx)))
    }

    // Decode array put
    fn decode_aput(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;
        let word = self.insns[pc];
        let aa = (word >> 8) as u16;
        let word2 = self.word_at(pc + 1);
        let bb = word2 & 0xff;
        let cc = (word2 >> 8) & 0xff;

        let elem_type = match op {
            APUT => ArgType::INT,
            APUT_WIDE => ArgType::LONG,
            APUT_OBJECT => ArgType::unknown_object(),
            APUT_BOOLEAN => ArgType::BOOLEAN,
            APUT_BYTE => ArgType::BYTE,
            APUT_CHAR => ArgType::CHAR,
            APUT_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        let src = RegisterArg::new(aa as RegNum, elem_type);
        let arr = RegisterArg::new(bb as RegNum, ArgType::unknown_object());
        let idx = RegisterArg::new(cc as RegNum, ArgType::INT);
        Some(InsnNode::aput(
            InsnArg::Reg(src),
            InsnArg::Reg(arr),
            InsnArg::Reg(idx),
        ))
    }

    // Decode instance field get
    fn decode_iget(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;
        let word = self.insns[pc];
        let a = ((word >> 8) & 0xf) as u16;
        let b = ((word >> 12) & 0xf) as u16;
        let field_idx = self.word_at(pc + 1) as u32;

        let field_type = match op {
            IGET => ArgType::INT,
            IGET_WIDE => ArgType::LONG,
            IGET_OBJECT => ArgType::unknown_object(),
            IGET_BOOLEAN => ArgType::BOOLEAN,
            IGET_BYTE => ArgType::BYTE,
            IGET_CHAR => ArgType::CHAR,
            IGET_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        let dest = RegisterArg::new(a as RegNum, field_type);
        let obj = RegisterArg::new(b as RegNum, ArgType::unknown_object());
        Some(InsnNode::iget(dest, InsnArg::Reg(obj), field_idx))
    }

    // Decode instance field put
    fn decode_iput(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;
        let word = self.insns[pc];
        let a = ((word >> 8) & 0xf) as u16;
        let b = ((word >> 12) & 0xf) as u16;
        let field_idx = self.word_at(pc + 1) as u32;

        let field_type = match op {
            IPUT => ArgType::INT,
            IPUT_WIDE => ArgType::LONG,
            IPUT_OBJECT => ArgType::unknown_object(),
            IPUT_BOOLEAN => ArgType::BOOLEAN,
            IPUT_BYTE => ArgType::BYTE,
            IPUT_CHAR => ArgType::CHAR,
            IPUT_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        let src = RegisterArg::new(a as RegNum, field_type);
        let obj = RegisterArg::new(b as RegNum, ArgType::unknown_object());
        Some(InsnNode::iput(
            InsnArg::Reg(src),
            InsnArg::Reg(obj),
            field_idx,
        ))
    }

    // Decode static field get
    fn decode_sget(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;
        let word = self.insns[pc];
        let aa = (word >> 8) as u16;
        let field_idx = self.word_at(pc + 1) as u32;

        let field_type = match op {
            SGET => ArgType::INT,
            SGET_WIDE => ArgType::LONG,
            SGET_OBJECT => ArgType::unknown_object(),
            SGET_BOOLEAN => ArgType::BOOLEAN,
            SGET_BYTE => ArgType::BYTE,
            SGET_CHAR => ArgType::CHAR,
            SGET_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        let dest = RegisterArg::new(aa as RegNum, field_type);
        Some(InsnNode::sget(dest, field_idx))
    }

    // Decode static field put
    fn decode_sput(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;
        let word = self.insns[pc];
        let aa = (word >> 8) as u16;
        let field_idx = self.word_at(pc + 1) as u32;

        let field_type = match op {
            SPUT => ArgType::INT,
            SPUT_WIDE => ArgType::LONG,
            SPUT_OBJECT => ArgType::unknown_object(),
            SPUT_BOOLEAN => ArgType::BOOLEAN,
            SPUT_BYTE => ArgType::BYTE,
            SPUT_CHAR => ArgType::CHAR,
            SPUT_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        let src = RegisterArg::new(aa as RegNum, field_type);
        Some(InsnNode::sput(InsnArg::Reg(src), field_idx))
    }

    // Decode invoke instruction
    fn decode_invoke(&self, pc: usize, op: u8, is_range: bool) -> Option<InsnNode> {
        use opcode::*;
        let invoke_type = match op {
            INVOKE_VIRTUAL | INVOKE_VIRTUAL_RANGE => InvokeType::Virtual,
            INVOKE_SUPER | INVOKE_SUPER_RANGE => InvokeType::Super,
            INVOKE_DIRECT | INVOKE_DIRECT_RANGE => InvokeType::Direct,
            INVOKE_STATIC | INVOKE_STATIC_RANGE => InvokeType::Static,
            INVOKE_INTERFACE | INVOKE_INTERFACE_RANGE => InvokeType::Interface,
            _ => InvokeType::Virtual,
        };

        let word = self.insns[pc];
        let method_idx = self.word_at(pc + 1) as u32;
        let word3 = self.word_at(pc + 2);

        let args = if is_range {
            let count = ((word >> 8) & 0xff) as u16;
            let start = word3;
            (0..count)
                .map(|i| InsnArg::Reg(RegisterArg::new((start + i) as RegNum, ArgType::unknown())))
                .collect()
        } else {
            let count = ((word >> 12) & 0xf) as usize;
            let mut regs = Vec::with_capacity(count);
            let c = word3 & 0xf;
            let d = (word3 >> 4) & 0xf;
            let e = (word3 >> 8) & 0xf;
            let f = (word3 >> 12) & 0xf;
            let g = (word >> 8) & 0xf;
            let all = [c, d, e, f, g];
            for &r in &all[..count] {
                regs.push(InsnArg::Reg(RegisterArg::new(
                    r as RegNum,
                    ArgType::unknown(),
                )));
            }
            regs
        };

        Some(InsnNode::invoke(invoke_type, method_idx, args))
    }

    // Decode unary operation
    fn decode_unary(&self, pc: usize, op: u8) -> Option<InsnNode> {
        let word = self.insns[pc];
        let a = ((word >> 8) & 0xf) as u16;
        let b = ((word >> 12) & 0xf) as u16;

        let unary_op = get_unary_op(op);
        let dest_type = get_unary_dest_type(op);
        let src_type = get_unary_src_type(op);

        let dest = RegisterArg::new(a as RegNum, dest_type);
        let src = RegisterArg::new(b as RegNum, src_type);
        Some(InsnNode::unary(unary_op, dest, InsnArg::Reg(src)))
    }

    // Decode binary operation
    fn decode_binary(&self, pc: usize, op: u8) -> Option<InsnNode> {
        let word = self.insns[pc];
        let aa = (word >> 8) as u16;
        let word2 = self.word_at(pc + 1);
        let bb = word2 & 0xff;
        let cc = (word2 >> 8) & 0xff;

        let (arith_op, arg_type) = decode_arith_3addr_op(op);
        let dest = RegisterArg::new(aa as RegNum, arg_type.clone());
        let src1 = RegisterArg::new(bb as RegNum, arg_type.clone());
        let src2 = RegisterArg::new(cc as RegNum, arg_type.clone());
        Some(InsnNode::arith(
            arith_op,
            dest,
            InsnArg::Reg(src1),
            InsnArg::Reg(src2),
            arg_type,
        ))
    }

    // Decode binary 2addr operation
    fn decode_binary_2addr(&self, pc: usize, op: u8) -> Option<InsnNode> {
        let word = self.insns[pc];
        let a = ((word >> 8) & 0xf) as u16;
        let b = ((word >> 12) & 0xf) as u16;

        let (arith_op, arg_type) = decode_arith_2addr_op(op);
        let dest = RegisterArg::new(a as RegNum, arg_type.clone());
        let src = RegisterArg::new(b as RegNum, arg_type.clone());
        Some(InsnNode::arith(
            arith_op,
            dest.clone(),
            InsnArg::Reg(dest),
            InsnArg::Reg(src),
            arg_type,
        ))
    }

    // Decode binary lit16 operation
    fn decode_binary_lit16(&self, pc: usize, op: u8) -> Option<InsnNode> {
        let word = self.insns[pc];
        let a = ((word >> 8) & 0xf) as u16;
        let b = ((word >> 12) & 0xf) as u16;
        let lit = self.word_at(pc + 1) as i16 as i64;

        let (arith_op, _) = decode_arith_lit16_op(op);
        let dest = RegisterArg::new(a as RegNum, ArgType::INT);
        let src = RegisterArg::new(b as RegNum, ArgType::INT);
        Some(InsnNode::arith(
            arith_op,
            dest,
            InsnArg::Reg(src),
            InsnArg::lit(lit, ArgType::INT),
            ArgType::INT,
        ))
    }

    // Decode binary lit8 operation
    fn decode_binary_lit8(&self, pc: usize, op: u8) -> Option<InsnNode> {
        let word = self.insns[pc];
        let aa = (word >> 8) as u16;
        let word2 = self.word_at(pc + 1);
        let bb = word2 & 0xff;
        let cc = (word2 >> 8) as i8 as i64;

        let (arith_op, _) = decode_arith_lit8_op(op);
        let dest = RegisterArg::new(aa as RegNum, ArgType::INT);
        let src = RegisterArg::new(bb as RegNum, ArgType::INT);
        Some(InsnNode::arith(
            arith_op,
            dest,
            InsnArg::Reg(src),
            InsnArg::lit(cc, ArgType::INT),
            ArgType::INT,
        ))
    }

    // Decode packed-switch payload
    fn decode_packed_switch(&self, insn_pc: usize, payload_addr: usize) -> Vec<(i32, i32)> {
        if payload_addr >= self.insns.len() {
            return Vec::new();
        }
        let ident = self.word_at(payload_addr);
        if ident != 0x0100 {
            return Vec::new();
        }
        let size = self.word_at(payload_addr + 1) as usize;
        let first_key = self.dword_at(payload_addr + 2) as i32;

        let mut cases = Vec::with_capacity(size);
        for i in 0..size {
            let target_offset = self.dword_at(payload_addr + 4 + i * 2) as i32;
            let target = insn_pc as i32 + target_offset;
            cases.push((first_key + i as i32, target));
        }
        cases
    }

    // Decode sparse-switch payload
    fn decode_sparse_switch(&self, insn_pc: usize, payload_addr: usize) -> Vec<(i32, i32)> {
        if payload_addr >= self.insns.len() {
            return Vec::new();
        }
        let ident = self.word_at(payload_addr);
        if ident != 0x0200 {
            return Vec::new();
        }
        let size = self.word_at(payload_addr + 1) as usize;

        let mut cases = Vec::with_capacity(size);
        for i in 0..size {
            let key = self.dword_at(payload_addr + 2 + i * 2) as i32;
            let target_offset = self.dword_at(payload_addr + 2 + size * 2 + i * 2) as i32;
            let target = insn_pc as i32 + target_offset;
            cases.push((key, target));
        }
        cases
    }

    // Decode fill-array-data payload
    fn decode_fill_array_data(&self, payload_addr: usize) -> Option<FillArrayData> {
        if payload_addr >= self.insns.len() {
            return None;
        }
        let ident = self.word_at(payload_addr);
        if ident != 0x0300 {
            return None;
        }
        let element_width = self.word_at(payload_addr + 1);
        let size = self.dword_at(payload_addr + 2);
        let element_width_usize = element_width as usize;
        let size_usize = size as usize;
        let data_size = size_usize * element_width_usize;

        let mut data = Vec::with_capacity(data_size);
        let data_start = payload_addr + 4;
        for i in 0..data_size {
            let word_idx = data_start + i / 2;
            let byte_idx = i % 2;
            if word_idx < self.insns.len() {
                let word = self.insns[word_idx];
                let byte = if byte_idx == 0 {
                    word & 0xff
                } else {
                    word >> 8
                };
                data.push(byte as u8);
            }
        }
        Some(FillArrayData::new(element_width, size, data))
    }

    // Decode filled-new-array
    fn decode_filled_new_array(&self, pc: usize, op: u8) -> Option<InsnNode> {
        use opcode::*;
        let word = self.insns[pc];
        let type_idx = self.word_at(pc + 1) as u32;
        let word3 = self.word_at(pc + 2);

        let args: Vec<InsnArg> = if op == FILLED_NEW_ARRAY_RANGE {
            let count = ((word >> 8) & 0xff) as u16;
            let start = word3;
            (0..count)
                .map(|i| InsnArg::Reg(RegisterArg::new((start + i) as RegNum, ArgType::unknown())))
                .collect()
        } else {
            let count = ((word >> 12) & 0xf) as usize;
            let mut regs = Vec::with_capacity(count);
            let c = word3 & 0xf;
            let d = (word3 >> 4) & 0xf;
            let e = (word3 >> 8) & 0xf;
            let f = (word3 >> 12) & 0xf;
            let g = (word >> 8) & 0xf;
            let all = [c, d, e, f, g];
            for &r in &all[..count] {
                regs.push(InsnArg::Reg(RegisterArg::new(
                    r as RegNum,
                    ArgType::unknown(),
                )));
            }
            regs
        };

        // The array is only assigned a register when a following move-result-object
        // consumes it. BindResults attaches that destination later.
        Some(InsnNode::filled_new_array(type_idx, args))
    }
}

// === Helper functions ===

fn instruction_length(op: u8, insns: &[u16]) -> usize {
    use opcode::*;
    if let Some(&word) = insns.first() {
        if word == 0x0100 && insns.len() > 1 {
            let size = insns[1] as usize;
            return 4 + size * 2;
        } else if word == 0x0200 && insns.len() > 1 {
            let size = insns[1] as usize;
            return 2 + size * 4;
        } else if word == 0x0300 && insns.len() > 3 {
            let element_width = insns[1] as usize;
            let size = (insns[2] as usize) | ((insns[3] as usize) << 16);
            let data_size = (size * element_width + 1) / 2;
            return 4 + data_size;
        }
    }

    match op {
        NOP
        | MOVE
        | MOVE_WIDE
        | MOVE_OBJECT
        | RETURN_VOID
        | RETURN
        | RETURN_WIDE
        | RETURN_OBJECT
        | CONST_4
        | MONITOR_ENTER
        | MONITOR_EXIT
        | THROW
        | GOTO
        | MOVE_RESULT
        | MOVE_RESULT_WIDE
        | MOVE_RESULT_OBJECT
        | MOVE_EXCEPTION
        | NEG_INT..=INT_TO_SHORT
        | ADD_INT_2ADDR..=REM_DOUBLE_2ADDR
        | ARRAY_LENGTH => 1,

        MOVE_FROM16
        | MOVE_WIDE_FROM16
        | MOVE_OBJECT_FROM16
        | GOTO_16
        | CONST_16
        | CONST_HIGH16
        | CONST_WIDE_16
        | CONST_WIDE_HIGH16
        | CONST_STRING
        | CONST_CLASS
        | CHECK_CAST
        | INSTANCE_OF
        | NEW_INSTANCE
        | NEW_ARRAY
        | AGET..=APUT_SHORT
        | IGET..=SPUT_SHORT
        | ADD_INT..=REM_DOUBLE
        | IF_EQ..=IF_LEZ
        | ADD_INT_LIT16..=XOR_INT_LIT16
        | ADD_INT_LIT8..=USHR_INT_LIT8
        | CMPL_FLOAT..=CMP_LONG => 2,

        MOVE_16
        | MOVE_WIDE_16
        | MOVE_OBJECT_16
        | GOTO_32
        | CONST
        | CONST_WIDE_32
        | CONST_STRING_JUMBO
        | PACKED_SWITCH
        | SPARSE_SWITCH
        | FILL_ARRAY_DATA
        | FILLED_NEW_ARRAY
        | FILLED_NEW_ARRAY_RANGE
        | INVOKE_VIRTUAL..=INVOKE_INTERFACE
        | INVOKE_VIRTUAL_RANGE..=INVOKE_INTERFACE_RANGE => 3,

        CONST_WIDE => 5,

        _ => 1,
    }
}

fn sign_extend_4(val: i32) -> i32 {
    if val & 0x8 != 0 {
        val | !0xf
    } else {
        val & 0xf
    }
}

fn sign_extend_8(val: i32) -> i32 {
    (val as i8) as i32
}

fn decode_arith_2addr_op(op: u8) -> (ArithOp, ArgType) {
    use opcode::*;
    match op {
        ADD_INT_2ADDR => (ArithOp::Add, ArgType::INT),
        SUB_INT_2ADDR => (ArithOp::Sub, ArgType::INT),
        MUL_INT_2ADDR => (ArithOp::Mul, ArgType::INT),
        DIV_INT_2ADDR => (ArithOp::Div, ArgType::INT),
        REM_INT_2ADDR => (ArithOp::Rem, ArgType::INT),
        AND_INT_2ADDR => (ArithOp::And, ArgType::INT),
        OR_INT_2ADDR => (ArithOp::Or, ArgType::INT),
        XOR_INT_2ADDR => (ArithOp::Xor, ArgType::INT),
        SHL_INT_2ADDR => (ArithOp::Shl, ArgType::INT),
        SHR_INT_2ADDR => (ArithOp::Shr, ArgType::INT),
        USHR_INT_2ADDR => (ArithOp::Ushr, ArgType::INT),
        ADD_LONG_2ADDR => (ArithOp::Add, ArgType::LONG),
        SUB_LONG_2ADDR => (ArithOp::Sub, ArgType::LONG),
        MUL_LONG_2ADDR => (ArithOp::Mul, ArgType::LONG),
        DIV_LONG_2ADDR => (ArithOp::Div, ArgType::LONG),
        REM_LONG_2ADDR => (ArithOp::Rem, ArgType::LONG),
        AND_LONG_2ADDR => (ArithOp::And, ArgType::LONG),
        OR_LONG_2ADDR => (ArithOp::Or, ArgType::LONG),
        XOR_LONG_2ADDR => (ArithOp::Xor, ArgType::LONG),
        SHL_LONG_2ADDR => (ArithOp::Shl, ArgType::LONG),
        SHR_LONG_2ADDR => (ArithOp::Shr, ArgType::LONG),
        USHR_LONG_2ADDR => (ArithOp::Ushr, ArgType::LONG),
        ADD_FLOAT_2ADDR => (ArithOp::Add, ArgType::FLOAT),
        SUB_FLOAT_2ADDR => (ArithOp::Sub, ArgType::FLOAT),
        MUL_FLOAT_2ADDR => (ArithOp::Mul, ArgType::FLOAT),
        DIV_FLOAT_2ADDR => (ArithOp::Div, ArgType::FLOAT),
        REM_FLOAT_2ADDR => (ArithOp::Rem, ArgType::FLOAT),
        ADD_DOUBLE_2ADDR => (ArithOp::Add, ArgType::DOUBLE),
        SUB_DOUBLE_2ADDR => (ArithOp::Sub, ArgType::DOUBLE),
        MUL_DOUBLE_2ADDR => (ArithOp::Mul, ArgType::DOUBLE),
        DIV_DOUBLE_2ADDR => (ArithOp::Div, ArgType::DOUBLE),
        REM_DOUBLE_2ADDR => (ArithOp::Rem, ArgType::DOUBLE),
        _ => (ArithOp::Add, ArgType::INT),
    }
}

fn decode_arith_3addr_op(op: u8) -> (ArithOp, ArgType) {
    use opcode::*;
    match op {
        ADD_INT => (ArithOp::Add, ArgType::INT),
        SUB_INT => (ArithOp::Sub, ArgType::INT),
        MUL_INT => (ArithOp::Mul, ArgType::INT),
        DIV_INT => (ArithOp::Div, ArgType::INT),
        REM_INT => (ArithOp::Rem, ArgType::INT),
        AND_INT => (ArithOp::And, ArgType::INT),
        OR_INT => (ArithOp::Or, ArgType::INT),
        XOR_INT => (ArithOp::Xor, ArgType::INT),
        SHL_INT => (ArithOp::Shl, ArgType::INT),
        SHR_INT => (ArithOp::Shr, ArgType::INT),
        USHR_INT => (ArithOp::Ushr, ArgType::INT),
        ADD_LONG => (ArithOp::Add, ArgType::LONG),
        SUB_LONG => (ArithOp::Sub, ArgType::LONG),
        MUL_LONG => (ArithOp::Mul, ArgType::LONG),
        DIV_LONG => (ArithOp::Div, ArgType::LONG),
        REM_LONG => (ArithOp::Rem, ArgType::LONG),
        AND_LONG => (ArithOp::And, ArgType::LONG),
        OR_LONG => (ArithOp::Or, ArgType::LONG),
        XOR_LONG => (ArithOp::Xor, ArgType::LONG),
        SHL_LONG => (ArithOp::Shl, ArgType::LONG),
        SHR_LONG => (ArithOp::Shr, ArgType::LONG),
        USHR_LONG => (ArithOp::Ushr, ArgType::LONG),
        ADD_FLOAT => (ArithOp::Add, ArgType::FLOAT),
        SUB_FLOAT => (ArithOp::Sub, ArgType::FLOAT),
        MUL_FLOAT => (ArithOp::Mul, ArgType::FLOAT),
        DIV_FLOAT => (ArithOp::Div, ArgType::FLOAT),
        REM_FLOAT => (ArithOp::Rem, ArgType::FLOAT),
        ADD_DOUBLE => (ArithOp::Add, ArgType::DOUBLE),
        SUB_DOUBLE => (ArithOp::Sub, ArgType::DOUBLE),
        MUL_DOUBLE => (ArithOp::Mul, ArgType::DOUBLE),
        DIV_DOUBLE => (ArithOp::Div, ArgType::DOUBLE),
        REM_DOUBLE => (ArithOp::Rem, ArgType::DOUBLE),
        _ => (ArithOp::Add, ArgType::INT),
    }
}

fn decode_arith_lit16_op(op: u8) -> (ArithOp, ArgType) {
    use opcode::*;
    match op {
        ADD_INT_LIT16 => (ArithOp::Add, ArgType::INT),
        RSUB_INT => (ArithOp::Rsub, ArgType::INT),
        MUL_INT_LIT16 => (ArithOp::Mul, ArgType::INT),
        DIV_INT_LIT16 => (ArithOp::Div, ArgType::INT),
        REM_INT_LIT16 => (ArithOp::Rem, ArgType::INT),
        AND_INT_LIT16 => (ArithOp::And, ArgType::INT),
        OR_INT_LIT16 => (ArithOp::Or, ArgType::INT),
        XOR_INT_LIT16 => (ArithOp::Xor, ArgType::INT),
        _ => (ArithOp::Add, ArgType::INT),
    }
}

fn decode_arith_lit8_op(op: u8) -> (ArithOp, ArgType) {
    use opcode::*;
    match op {
        ADD_INT_LIT8 => (ArithOp::Add, ArgType::INT),
        RSUB_INT_LIT8 => (ArithOp::Rsub, ArgType::INT),
        MUL_INT_LIT8 => (ArithOp::Mul, ArgType::INT),
        DIV_INT_LIT8 => (ArithOp::Div, ArgType::INT),
        REM_INT_LIT8 => (ArithOp::Rem, ArgType::INT),
        AND_INT_LIT8 => (ArithOp::And, ArgType::INT),
        OR_INT_LIT8 => (ArithOp::Or, ArgType::INT),
        XOR_INT_LIT8 => (ArithOp::Xor, ArgType::INT),
        SHL_INT_LIT8 => (ArithOp::Shl, ArgType::INT),
        SHR_INT_LIT8 => (ArithOp::Shr, ArgType::INT),
        USHR_INT_LIT8 => (ArithOp::Ushr, ArgType::INT),
        _ => (ArithOp::Add, ArgType::INT),
    }
}

fn get_unary_op(op: u8) -> UnaryOp {
    use opcode::*;
    match op {
        NEG_INT | NEG_LONG | NEG_FLOAT | NEG_DOUBLE => UnaryOp::Neg,
        NOT_INT | NOT_LONG => UnaryOp::Not,
        INT_TO_LONG => UnaryOp::IntToLong,
        INT_TO_FLOAT => UnaryOp::IntToFloat,
        INT_TO_DOUBLE => UnaryOp::IntToDouble,
        LONG_TO_INT => UnaryOp::LongToInt,
        LONG_TO_FLOAT => UnaryOp::LongToFloat,
        LONG_TO_DOUBLE => UnaryOp::LongToDouble,
        FLOAT_TO_INT => UnaryOp::FloatToInt,
        FLOAT_TO_LONG => UnaryOp::FloatToLong,
        FLOAT_TO_DOUBLE => UnaryOp::FloatToDouble,
        DOUBLE_TO_INT => UnaryOp::DoubleToInt,
        DOUBLE_TO_LONG => UnaryOp::DoubleToLong,
        DOUBLE_TO_FLOAT => UnaryOp::DoubleToFloat,
        INT_TO_BYTE => UnaryOp::IntToByte,
        INT_TO_CHAR => UnaryOp::IntToChar,
        INT_TO_SHORT => UnaryOp::IntToShort,
        _ => UnaryOp::Neg,
    }
}

fn get_unary_dest_type(op: u8) -> ArgType {
    use opcode::*;
    match op {
        NEG_INT | NOT_INT | LONG_TO_INT | FLOAT_TO_INT | DOUBLE_TO_INT => ArgType::INT,
        NEG_LONG | NOT_LONG | INT_TO_LONG | FLOAT_TO_LONG | DOUBLE_TO_LONG => ArgType::LONG,
        NEG_FLOAT | INT_TO_FLOAT | LONG_TO_FLOAT | DOUBLE_TO_FLOAT => ArgType::FLOAT,
        NEG_DOUBLE | INT_TO_DOUBLE | LONG_TO_DOUBLE | FLOAT_TO_DOUBLE => ArgType::DOUBLE,
        INT_TO_BYTE => ArgType::BYTE,
        INT_TO_CHAR => ArgType::CHAR,
        INT_TO_SHORT => ArgType::SHORT,
        _ => ArgType::INT,
    }
}

fn get_unary_src_type(op: u8) -> ArgType {
    use opcode::*;
    match op {
        NEG_INT | NOT_INT | INT_TO_LONG | INT_TO_FLOAT | INT_TO_DOUBLE | INT_TO_BYTE
        | INT_TO_CHAR | INT_TO_SHORT => ArgType::INT,
        NEG_LONG | NOT_LONG | LONG_TO_INT | LONG_TO_FLOAT | LONG_TO_DOUBLE => ArgType::LONG,
        NEG_FLOAT | FLOAT_TO_INT | FLOAT_TO_LONG | FLOAT_TO_DOUBLE => ArgType::FLOAT,
        NEG_DOUBLE | DOUBLE_TO_INT | DOUBLE_TO_LONG | DOUBLE_TO_FLOAT => ArgType::DOUBLE,
        _ => ArgType::INT,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::insn::InsnType;

    #[test]
    fn test_decode_simple_return() {
        let code = MethodCode {
            registers_size: 1,
            ins_size: 0,
            outs_size: 0,
            insns: vec![0x000e], // return-void (opcode 0x0e in low byte)
            tries: vec![],
            debug_info: None,
        };

        let decoder = MethodDecoder::from_code(&code);
        let result = decoder.decode();

        assert_eq!(result.insns.len(), 1);
        assert!(matches!(result.insns[0].insn_type, InsnType::Return));
    }

    #[test]
    fn test_decode_const_and_return() {
        let code = MethodCode {
            registers_size: 1,
            ins_size: 0,
            outs_size: 0,
            insns: vec![
                0x0012, // const/4 v0, 0 (opcode 0x12 in low byte)
                0x000f, // return v0 (opcode 0x0f in low byte)
            ],
            tries: vec![],
            debug_info: None,
        };

        let decoder = MethodDecoder::from_code(&code);
        let result = decoder.decode();

        assert_eq!(result.insns.len(), 2);
        assert!(matches!(result.insns[0].insn_type, InsnType::Const));
        assert!(matches!(result.insns[1].insn_type, InsnType::Return));
    }

    #[test]
    fn unconsumed_filled_new_array_has_no_placeholder_result() {
        let code = MethodCode {
            registers_size: 2,
            ins_size: 0,
            outs_size: 0,
            insns: vec![
                0x1024, // filled-new-array {v1}, type@0
                0x0000, 0x0001, 0x1012, // const/4 v0, 1
                0x000e, // return-void
            ],
            tries: vec![],
            debug_info: None,
        };

        let result = MethodDecoder::from_code(&code).decode();

        assert_eq!(result.insns.len(), 3);
        assert_eq!(result.insns[0].insn_type, InsnType::FilledNewArray);
        assert!(result.insns[0].result.is_none());
        assert_eq!(
            result.insns[1].result.as_ref().map(|result| result.reg_num),
            Some(0)
        );
    }
}
