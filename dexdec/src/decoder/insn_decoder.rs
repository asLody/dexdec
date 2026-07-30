//! Instruction Decoder for rusty-dex CodeItem
//!
//! Decodes rusty-dex parsed instructions into IR instructions.
//! CFG construction is handled by the Splitter.

use rusty_dex::dex::code_item::CodeItem;
use rusty_dex::dex::instructions::Instructions;
use rusty_dex::dex::opcodes::OpCode;

use crate::ir::arg::{InsnArg, RegNum, RegisterArg};
use crate::ir::block::ExceptionHandler;
use crate::ir::insn::{ArithOp, IfOp, InsnNode, InvokeType, UnaryOp};
use crate::ir::ty::{ArgType, DescriptorParseError};

/// Decode result from CodeItem
#[derive(Debug, Clone)]
pub struct CodeDecodeResult {
    pub insns: Vec<InsnNode>,
    pub handlers: Vec<ExceptionHandler>,
    pub registers: u32,
    pub ins: u32,
}

/// Instruction decoder for rusty-dex CodeItem
pub struct InsnDecoder<'a> {
    code: &'a CodeItem,
}

impl<'a> InsnDecoder<'a> {
    /// Create a new decoder for the given code item
    pub fn new(code: &'a CodeItem) -> Self {
        Self { code }
    }

    /// Decode the code item to instruction list
    pub fn decode(&self) -> Result<CodeDecodeResult, DescriptorParseError> {
        let insns = self.decode_instructions();
        let handlers = self.extract_handlers()?;

        Ok(CodeDecodeResult {
            insns,
            handlers,
            registers: self.code.registers_size as u32,
            ins: self.code.ins_size as u32,
        })
    }

    /// Decode all instructions
    fn decode_instructions(&self) -> Vec<InsnNode> {
        let Some(code_insns) = &self.code.insns else {
            return Vec::new();
        };

        let mut result = Vec::new();
        let mut offset = 0usize;

        for insn in code_insns {
            if let Some(mut ir_insn) = self.decode_instruction(insn, offset) {
                ir_insn.set_offset(offset as u32);
                result.push(ir_insn);
            }
            offset += insn.length();
        }

        result
    }

    /// Extract exception handlers
    fn extract_handlers(&self) -> Result<Vec<ExceptionHandler>, DescriptorParseError> {
        let mut handlers = Vec::new();

        // From tries
        if let Some(tries) = &self.code.tries {
            if let Some(handler_list) = &self.code.handlers {
                for try_item in tries {
                    if let Some(handler) = handler_list.get(try_item.handler_off as usize) {
                        for pair in &handler.handlers {
                            handlers.push(ExceptionHandler::new(
                                try_item.start_addr,
                                try_item.start_addr + try_item.insn_count as u32,
                                pair.addr,
                                Some(pair.decoded_type.parse::<ArgType>()?),
                            ));
                        }
                        if let Some(catch_all) = handler.catch_all_addr {
                            handlers.push(ExceptionHandler::new(
                                try_item.start_addr,
                                try_item.start_addr + try_item.insn_count as u32,
                                catch_all,
                                None,
                            ));
                        }
                    }
                }
            }
        }

        Ok(handlers)
    }

    fn find_instruction_at_offset(&self, target_offset: usize) -> Option<&Instructions> {
        let Some(code_insns) = &self.code.insns else {
            return None;
        };

        let mut offset = 0usize;
        for insn in code_insns {
            if offset == target_offset {
                return Some(insn);
            }
            offset += insn.length();
        }

        None
    }

    /// Decode a single instruction
    fn decode_instruction(&self, insn: &Instructions, offset: usize) -> Option<InsnNode> {
        let opcode = insn.opcode();
        let bytes = insn.bytes();
        let w0 = bytes.first().copied().unwrap_or(0);
        let w1 = bytes.get(1).copied().unwrap_or(0);
        let w2 = bytes.get(2).copied().unwrap_or(0);
        let w3 = bytes.get(3).copied().unwrap_or(0);
        let w4 = bytes.get(4).copied().unwrap_or(0);

        match opcode {
            // NOP
            OpCode::NOP => Some(InsnNode::nop()),

            // Move
            OpCode::MOVE => {
                let dest = ((w0 >> 8) & 0xF) as RegNum;
                let src = ((w0 >> 12) & 0xF) as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::narrow()),
                    InsnArg::reg(src, ArgType::narrow()),
                ))
            }
            OpCode::MOVE_FROM16 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let src = w1 as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::narrow()),
                    InsnArg::reg(src, ArgType::narrow()),
                ))
            }
            OpCode::MOVE_16 => {
                let dest = w1 as RegNum;
                let src = w2 as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::narrow()),
                    InsnArg::reg(src, ArgType::narrow()),
                ))
            }
            OpCode::MOVE_WIDE => {
                let dest = ((w0 >> 8) & 0xF) as RegNum;
                let src = ((w0 >> 12) & 0xF) as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::wide()),
                    InsnArg::reg(src, ArgType::wide()),
                ))
            }
            OpCode::MOVE_WIDE_FROM16 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let src = w1 as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::wide()),
                    InsnArg::reg(src, ArgType::wide()),
                ))
            }
            OpCode::MOVE_WIDE_16 => {
                let dest = w1 as RegNum;
                let src = w2 as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::wide()),
                    InsnArg::reg(src, ArgType::wide()),
                ))
            }
            OpCode::MOVE_OBJECT => {
                let dest = ((w0 >> 8) & 0xF) as RegNum;
                let src = ((w0 >> 12) & 0xF) as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    InsnArg::reg(src, ArgType::unknown_object()),
                ))
            }
            OpCode::MOVE_OBJECT_FROM16 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let src = w1 as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    InsnArg::reg(src, ArgType::unknown_object()),
                ))
            }
            OpCode::MOVE_OBJECT_16 => {
                let dest = w1 as RegNum;
                let src = w2 as RegNum;
                Some(InsnNode::move_insn(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    InsnArg::reg(src, ArgType::unknown_object()),
                ))
            }

            // Move result
            OpCode::MOVE_RESULT => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::move_result(RegisterArg::new(
                    dest,
                    ArgType::narrow(),
                )))
            }
            OpCode::MOVE_RESULT_WIDE => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::move_result(RegisterArg::new(
                    dest,
                    ArgType::wide(),
                )))
            }
            OpCode::MOVE_RESULT_OBJECT => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::move_result(RegisterArg::new(
                    dest,
                    ArgType::unknown_object(),
                )))
            }
            OpCode::MOVE_EXCEPTION => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::move_exception(RegisterArg::new(
                    dest,
                    ArgType::unknown_object(),
                )))
            }

            // Return
            OpCode::RETURN_VOID => Some(InsnNode::return_void()),
            OpCode::RETURN => {
                let src = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::return_insn(RegisterArg::new(
                    src,
                    ArgType::narrow(),
                )))
            }
            OpCode::RETURN_WIDE => {
                let src = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::return_insn(RegisterArg::new(
                    src,
                    ArgType::wide(),
                )))
            }
            OpCode::RETURN_OBJECT => {
                let src = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::return_insn(RegisterArg::new(
                    src,
                    ArgType::unknown_object(),
                )))
            }

            // Const
            OpCode::CONST_4 => {
                let dest = ((w0 >> 8) & 0xF) as RegNum;
                let value = ((w0 as i16) >> 12) as i64;
                Some(InsnNode::const_insn(
                    RegisterArg::new(dest, ArgType::INT),
                    value,
                ))
            }
            OpCode::CONST_16 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let value = w1 as i16 as i64;
                Some(InsnNode::const_insn(
                    RegisterArg::new(dest, ArgType::INT),
                    value,
                ))
            }
            OpCode::CONST => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let value = (w1 as u32 | ((w2 as u32) << 16)) as i32 as i64;
                Some(InsnNode::const_insn(
                    RegisterArg::new(dest, ArgType::INT),
                    value,
                ))
            }
            OpCode::CONST_HIGH16 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let value = ((w1 as u32) << 16) as i32 as i64;
                Some(InsnNode::const_insn(
                    RegisterArg::new(dest, ArgType::INT),
                    value,
                ))
            }
            OpCode::CONST_WIDE_16 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let value = w1 as i16 as i64;
                Some(InsnNode::const_wide(
                    RegisterArg::new(dest, ArgType::LONG),
                    value,
                ))
            }
            OpCode::CONST_WIDE_32 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let value = (w1 as u32 | ((w2 as u32) << 16)) as i32 as i64;
                Some(InsnNode::const_wide(
                    RegisterArg::new(dest, ArgType::LONG),
                    value,
                ))
            }
            OpCode::CONST_WIDE => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let value =
                    (w1 as u64) | ((w2 as u64) << 16) | ((w3 as u64) << 32) | ((w4 as u64) << 48);
                Some(InsnNode::const_wide(
                    RegisterArg::new(dest, ArgType::LONG),
                    value as i64,
                ))
            }
            OpCode::CONST_WIDE_HIGH16 => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let value = (w1 as u64) << 48;
                Some(InsnNode::const_wide(
                    RegisterArg::new(dest, ArgType::LONG),
                    value as i64,
                ))
            }
            OpCode::CONST_STRING => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let idx = w1 as u32;
                Some(InsnNode::const_string(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    idx,
                ))
            }
            OpCode::CONST_STRING_JUMBO => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let idx = (w1 as u32) | ((w2 as u32) << 16);
                Some(InsnNode::const_string(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    idx,
                ))
            }
            OpCode::CONST_CLASS => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let idx = w1 as u32;
                Some(InsnNode::const_class(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    idx,
                ))
            }

            // Monitor
            OpCode::MONITOR_ENTER => {
                let reg = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::monitor_enter(InsnArg::Reg(RegisterArg::new(
                    reg,
                    ArgType::unknown_object(),
                ))))
            }
            OpCode::MONITOR_EXIT => {
                let reg = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::monitor_exit(InsnArg::Reg(RegisterArg::new(
                    reg,
                    ArgType::unknown_object(),
                ))))
            }

            // Type check
            OpCode::CHECK_CAST => {
                let reg = ((w0 >> 8) & 0xFF) as RegNum;
                let idx = w1 as u32;
                Some(InsnNode::check_cast(
                    InsnArg::Reg(RegisterArg::new(reg, ArgType::unknown_object())),
                    idx,
                ))
            }
            OpCode::INSTANCE_OF => {
                let dest = ((w0 >> 8) & 0xF) as RegNum;
                let src = ((w0 >> 12) & 0xF) as RegNum;
                let idx = w1 as u32;
                Some(InsnNode::instance_of(
                    RegisterArg::new(dest, ArgType::BOOLEAN),
                    InsnArg::Reg(RegisterArg::new(src, ArgType::unknown_object())),
                    idx,
                ))
            }

            // Array
            OpCode::ARRAY_LENGTH => {
                let dest = ((w0 >> 8) & 0xF) as RegNum;
                let arr = ((w0 >> 12) & 0xF) as RegNum;
                Some(InsnNode::array_length(
                    RegisterArg::new(dest, ArgType::INT),
                    InsnArg::Reg(RegisterArg::new(arr, ArgType::unknown_object())),
                ))
            }
            OpCode::NEW_INSTANCE => {
                let dest = ((w0 >> 8) & 0xFF) as RegNum;
                let idx = w1 as u32;
                Some(InsnNode::new_instance(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    idx,
                ))
            }
            OpCode::NEW_ARRAY => {
                let dest = ((w0 >> 8) & 0xF) as RegNum;
                let size = ((w0 >> 12) & 0xF) as RegNum;
                let idx = w1 as u32;
                Some(InsnNode::new_array(
                    RegisterArg::new(dest, ArgType::unknown_object()),
                    InsnArg::Reg(RegisterArg::new(size, ArgType::INT)),
                    idx,
                ))
            }

            // Throw
            OpCode::THROW => {
                let ex = ((w0 >> 8) & 0xFF) as RegNum;
                Some(InsnNode::throw(InsnArg::Reg(RegisterArg::new(
                    ex,
                    ArgType::unknown_object(),
                ))))
            }

            // Goto
            OpCode::GOTO => {
                let off = ((w0 >> 8) as i8) as i32;
                let target = offset as i32 + off;
                Some(InsnNode::goto(target))
            }
            OpCode::GOTO_16 => {
                let off = w1 as i16 as i32;
                let target = offset as i32 + off;
                Some(InsnNode::goto(target))
            }
            OpCode::GOTO_32 => {
                let off = (w1 as u32 | ((w2 as u32) << 16)) as i32;
                let target = offset as i32 + off;
                Some(InsnNode::goto(target))
            }

            // Switch
            OpCode::PACKED_SWITCH => {
                let reg = ((w0 >> 8) & 0xFF) as RegNum;
                let payload_offset = (w1 as u32 | ((w2 as u32) << 16)) as i32;
                let cases = self.decode_packed_switch(offset, payload_offset);
                Some(InsnNode::switch(
                    InsnArg::Reg(RegisterArg::new(reg, ArgType::INT)),
                    cases,
                ))
            }
            OpCode::SPARSE_SWITCH => {
                let reg = ((w0 >> 8) & 0xFF) as RegNum;
                let payload_offset = (w1 as u32 | ((w2 as u32) << 16)) as i32;
                let cases = self.decode_sparse_switch(offset, payload_offset);
                Some(InsnNode::switch(
                    InsnArg::Reg(RegisterArg::new(reg, ArgType::INT)),
                    cases,
                ))
            }

            // Compare
            OpCode::CMPL_FLOAT
            | OpCode::CMPG_FLOAT
            | OpCode::CMPL_DOUBLE
            | OpCode::CMPG_DOUBLE
            | OpCode::CMP_LONG => self.decode_cmp(w0, w1, opcode),

            // If
            OpCode::IF_EQ
            | OpCode::IF_NE
            | OpCode::IF_LT
            | OpCode::IF_GE
            | OpCode::IF_GT
            | OpCode::IF_LE => self.decode_if_cmp(w0, w1, offset, opcode),
            OpCode::IF_EQZ
            | OpCode::IF_NEZ
            | OpCode::IF_LTZ
            | OpCode::IF_GEZ
            | OpCode::IF_GTZ
            | OpCode::IF_LEZ => self.decode_if_zero(w0, w1, offset, opcode),

            // Array access
            OpCode::AGET
            | OpCode::AGET_WIDE
            | OpCode::AGET_OBJECT
            | OpCode::AGET_BOOLEAN
            | OpCode::AGET_BYTE
            | OpCode::AGET_CHAR
            | OpCode::AGET_SHORT => self.decode_aget(w0, w1, opcode),
            OpCode::APUT
            | OpCode::APUT_WIDE
            | OpCode::APUT_OBJECT
            | OpCode::APUT_BOOLEAN
            | OpCode::APUT_BYTE
            | OpCode::APUT_CHAR
            | OpCode::APUT_SHORT => self.decode_aput(w0, w1, opcode),

            // Field access
            OpCode::IGET
            | OpCode::IGET_WIDE
            | OpCode::IGET_OBJECT
            | OpCode::IGET_BOOLEAN
            | OpCode::IGET_BYTE
            | OpCode::IGET_CHAR
            | OpCode::IGET_SHORT => self.decode_iget(w0, w1, opcode),
            OpCode::IPUT
            | OpCode::IPUT_WIDE
            | OpCode::IPUT_OBJECT
            | OpCode::IPUT_BOOLEAN
            | OpCode::IPUT_BYTE
            | OpCode::IPUT_CHAR
            | OpCode::IPUT_SHORT => self.decode_iput(w0, w1, opcode),
            OpCode::SGET
            | OpCode::SGET_WIDE
            | OpCode::SGET_OBJECT
            | OpCode::SGET_BOOLEAN
            | OpCode::SGET_BYTE
            | OpCode::SGET_CHAR
            | OpCode::SGET_SHORT => self.decode_sget(w0, w1, opcode),
            OpCode::SPUT
            | OpCode::SPUT_WIDE
            | OpCode::SPUT_OBJECT
            | OpCode::SPUT_BOOLEAN
            | OpCode::SPUT_BYTE
            | OpCode::SPUT_CHAR
            | OpCode::SPUT_SHORT => self.decode_sput(w0, w1, opcode),

            // Invoke
            OpCode::INVOKE_VIRTUAL
            | OpCode::INVOKE_SUPER
            | OpCode::INVOKE_DIRECT
            | OpCode::INVOKE_STATIC
            | OpCode::INVOKE_INTERFACE => self.decode_invoke(w0, w1, w2, opcode, false),
            OpCode::INVOKE_VIRTUAL_RANGE
            | OpCode::INVOKE_SUPER_RANGE
            | OpCode::INVOKE_DIRECT_RANGE
            | OpCode::INVOKE_STATIC_RANGE
            | OpCode::INVOKE_INTERFACE_RANGE => self.decode_invoke(w0, w1, w2, opcode, true),

            // Unary ops
            OpCode::NEG_INT
            | OpCode::NOT_INT
            | OpCode::NEG_LONG
            | OpCode::NOT_LONG
            | OpCode::NEG_FLOAT
            | OpCode::NEG_DOUBLE
            | OpCode::INT_TO_LONG
            | OpCode::INT_TO_FLOAT
            | OpCode::INT_TO_DOUBLE
            | OpCode::LONG_TO_INT
            | OpCode::LONG_TO_FLOAT
            | OpCode::LONG_TO_DOUBLE
            | OpCode::FLOAT_TO_INT
            | OpCode::FLOAT_TO_LONG
            | OpCode::FLOAT_TO_DOUBLE
            | OpCode::DOUBLE_TO_INT
            | OpCode::DOUBLE_TO_LONG
            | OpCode::DOUBLE_TO_FLOAT
            | OpCode::INT_TO_BYTE
            | OpCode::INT_TO_CHAR
            | OpCode::INT_TO_SHORT => self.decode_unary(w0, opcode),

            // Binary 3addr
            OpCode::ADD_INT
            | OpCode::SUB_INT
            | OpCode::MUL_INT
            | OpCode::DIV_INT
            | OpCode::REM_INT
            | OpCode::AND_INT
            | OpCode::OR_INT
            | OpCode::XOR_INT
            | OpCode::SHL_INT
            | OpCode::SHR_INT
            | OpCode::USHR_INT
            | OpCode::ADD_LONG
            | OpCode::SUB_LONG
            | OpCode::MUL_LONG
            | OpCode::DIV_LONG
            | OpCode::REM_LONG
            | OpCode::AND_LONG
            | OpCode::OR_LONG
            | OpCode::XOR_LONG
            | OpCode::SHL_LONG
            | OpCode::SHR_LONG
            | OpCode::USHR_LONG
            | OpCode::ADD_FLOAT
            | OpCode::SUB_FLOAT
            | OpCode::MUL_FLOAT
            | OpCode::DIV_FLOAT
            | OpCode::REM_FLOAT
            | OpCode::ADD_DOUBLE
            | OpCode::SUB_DOUBLE
            | OpCode::MUL_DOUBLE
            | OpCode::DIV_DOUBLE
            | OpCode::REM_DOUBLE => self.decode_binary_3addr(w0, w1, opcode),

            // Binary 2addr
            OpCode::ADD_INT_2ADDR
            | OpCode::SUB_INT_2ADDR
            | OpCode::MUL_INT_2ADDR
            | OpCode::DIV_INT_2ADDR
            | OpCode::REM_INT_2ADDR
            | OpCode::AND_INT_2ADDR
            | OpCode::OR_INT_2ADDR
            | OpCode::XOR_INT_2ADDR
            | OpCode::SHL_INT_2ADDR
            | OpCode::SHR_INT_2ADDR
            | OpCode::USHR_INT_2ADDR
            | OpCode::ADD_LONG_2ADDR
            | OpCode::SUB_LONG_2ADDR
            | OpCode::MUL_LONG_2ADDR
            | OpCode::DIV_LONG_2ADDR
            | OpCode::REM_LONG_2ADDR
            | OpCode::AND_LONG_2ADDR
            | OpCode::OR_LONG_2ADDR
            | OpCode::XOR_LONG_2ADDR
            | OpCode::SHL_LONG_2ADDR
            | OpCode::SHR_LONG_2ADDR
            | OpCode::USHR_LONG_2ADDR
            | OpCode::ADD_FLOAT_2ADDR
            | OpCode::SUB_FLOAT_2ADDR
            | OpCode::MUL_FLOAT_2ADDR
            | OpCode::DIV_FLOAT_2ADDR
            | OpCode::REM_FLOAT_2ADDR
            | OpCode::ADD_DOUBLE_2ADDR
            | OpCode::SUB_DOUBLE_2ADDR
            | OpCode::MUL_DOUBLE_2ADDR
            | OpCode::DIV_DOUBLE_2ADDR
            | OpCode::REM_DOUBLE_2ADDR => self.decode_binary_2addr(w0, opcode),

            // Binary lit16
            OpCode::ADD_INT_LIT16
            | OpCode::RSUB_INT
            | OpCode::MUL_INT_LIT16
            | OpCode::DIV_INT_LIT16
            | OpCode::REM_INT_LIT16
            | OpCode::AND_INT_LIT16
            | OpCode::OR_INT_LIT16
            | OpCode::XOR_INT_LIT16 => self.decode_binary_lit16(w0, w1, opcode),

            // Binary lit8
            OpCode::ADD_INT_LIT8
            | OpCode::RSUB_INT_LIT8
            | OpCode::MUL_INT_LIT8
            | OpCode::DIV_INT_LIT8
            | OpCode::REM_INT_LIT8
            | OpCode::AND_INT_LIT8
            | OpCode::OR_INT_LIT8
            | OpCode::XOR_INT_LIT8
            | OpCode::SHL_INT_LIT8
            | OpCode::SHR_INT_LIT8
            | OpCode::USHR_INT_LIT8 => self.decode_binary_lit8(w0, w1, opcode),

            _ => Some(InsnNode::nop()),
        }
    }

    // Decode compare
    fn decode_cmp(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        use crate::ir::insn::CmpBias;
        let dest = ((w0 >> 8) & 0xFF) as RegNum;
        let src1 = (w1 & 0xFF) as RegNum;
        let src2 = ((w1 >> 8) & 0xFF) as RegNum;

        let (arg_type, bias) = match opcode {
            OpCode::CMPL_FLOAT => (ArgType::FLOAT, CmpBias::Lt),
            OpCode::CMPG_FLOAT => (ArgType::FLOAT, CmpBias::Gt),
            OpCode::CMPL_DOUBLE => (ArgType::DOUBLE, CmpBias::Lt),
            OpCode::CMPG_DOUBLE => (ArgType::DOUBLE, CmpBias::Gt),
            OpCode::CMP_LONG => (ArgType::LONG, CmpBias::None),
            _ => (ArgType::INT, CmpBias::None),
        };

        Some(InsnNode::cmp(
            RegisterArg::new(dest, ArgType::INT),
            InsnArg::Reg(RegisterArg::new(src1, arg_type.clone())),
            InsnArg::Reg(RegisterArg::new(src2, arg_type)),
            bias,
        ))
    }

    // Decode if comparison
    fn decode_if_cmp(&self, w0: u16, w1: u16, offset: usize, opcode: OpCode) -> Option<InsnNode> {
        let r1 = ((w0 >> 8) & 0xF) as RegNum;
        let r2 = ((w0 >> 12) & 0xF) as RegNum;
        let off = w1 as i16 as i32;
        let target = offset as i32 + off;

        let ifop = match opcode {
            OpCode::IF_EQ => IfOp::Eq,
            OpCode::IF_NE => IfOp::Ne,
            OpCode::IF_LT => IfOp::Lt,
            OpCode::IF_GE => IfOp::Ge,
            OpCode::IF_GT => IfOp::Gt,
            OpCode::IF_LE => IfOp::Le,
            _ => IfOp::Eq,
        };

        let operand_type = if matches!(ifop, IfOp::Eq | IfOp::Ne) {
            ArgType::equality_operand()
        } else {
            ArgType::INT
        };
        Some(InsnNode::if_cmp(
            ifop,
            InsnArg::Reg(RegisterArg::new(r1, operand_type.clone())),
            InsnArg::reg(r2, operand_type),
            target,
        ))
    }

    // Decode if zero
    fn decode_if_zero(&self, w0: u16, w1: u16, offset: usize, opcode: OpCode) -> Option<InsnNode> {
        let r = ((w0 >> 8) & 0xFF) as RegNum;
        let off = w1 as i16 as i32;
        let target = offset as i32 + off;

        let ifop = match opcode {
            OpCode::IF_EQZ => IfOp::Eq,
            OpCode::IF_NEZ => IfOp::Ne,
            OpCode::IF_LTZ => IfOp::Lt,
            OpCode::IF_GEZ => IfOp::Ge,
            OpCode::IF_GTZ => IfOp::Gt,
            OpCode::IF_LEZ => IfOp::Le,
            _ => IfOp::Eq,
        };

        let operand_type = if matches!(ifop, IfOp::Eq | IfOp::Ne) {
            ArgType::equality_operand()
        } else {
            ArgType::INT
        };
        Some(InsnNode::if_cmp(
            ifop,
            InsnArg::Reg(RegisterArg::new(r, operand_type.clone())),
            InsnArg::lit(0, operand_type),
            target,
        ))
    }

    // Decode aget
    fn decode_aget(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xFF) as RegNum;
        let arr = (w1 & 0xFF) as RegNum;
        let idx = ((w1 >> 8) & 0xFF) as RegNum;

        let elem_type = match opcode {
            OpCode::AGET => ArgType::INT,
            OpCode::AGET_WIDE => ArgType::LONG,
            OpCode::AGET_OBJECT => ArgType::unknown_object(),
            OpCode::AGET_BOOLEAN => ArgType::BOOLEAN,
            OpCode::AGET_BYTE => ArgType::BYTE,
            OpCode::AGET_CHAR => ArgType::CHAR,
            OpCode::AGET_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        Some(InsnNode::aget(
            RegisterArg::new(dest, elem_type),
            InsnArg::Reg(RegisterArg::new(arr, ArgType::unknown_object())),
            InsnArg::Reg(RegisterArg::new(idx, ArgType::INT)),
        ))
    }

    // Decode aput
    fn decode_aput(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let src = ((w0 >> 8) & 0xFF) as RegNum;
        let arr = (w1 & 0xFF) as RegNum;
        let idx = ((w1 >> 8) & 0xFF) as RegNum;

        let elem_type = match opcode {
            OpCode::APUT => ArgType::INT,
            OpCode::APUT_WIDE => ArgType::LONG,
            OpCode::APUT_OBJECT => ArgType::unknown_object(),
            OpCode::APUT_BOOLEAN => ArgType::BOOLEAN,
            OpCode::APUT_BYTE => ArgType::BYTE,
            OpCode::APUT_CHAR => ArgType::CHAR,
            OpCode::APUT_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        Some(InsnNode::aput(
            InsnArg::Reg(RegisterArg::new(src, elem_type)),
            InsnArg::Reg(RegisterArg::new(arr, ArgType::unknown_object())),
            InsnArg::Reg(RegisterArg::new(idx, ArgType::INT)),
        ))
    }

    // Decode iget
    fn decode_iget(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xF) as RegNum;
        let obj = ((w0 >> 12) & 0xF) as RegNum;
        let field_idx = w1 as u32;

        let field_type = match opcode {
            OpCode::IGET => ArgType::INT,
            OpCode::IGET_WIDE => ArgType::LONG,
            OpCode::IGET_OBJECT => ArgType::unknown_object(),
            OpCode::IGET_BOOLEAN => ArgType::BOOLEAN,
            OpCode::IGET_BYTE => ArgType::BYTE,
            OpCode::IGET_CHAR => ArgType::CHAR,
            OpCode::IGET_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        Some(InsnNode::iget(
            RegisterArg::new(dest, field_type),
            InsnArg::Reg(RegisterArg::new(obj, ArgType::unknown_object())),
            field_idx,
        ))
    }

    // Decode iput
    fn decode_iput(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let src = ((w0 >> 8) & 0xF) as RegNum;
        let obj = ((w0 >> 12) & 0xF) as RegNum;
        let field_idx = w1 as u32;

        let field_type = match opcode {
            OpCode::IPUT => ArgType::INT,
            OpCode::IPUT_WIDE => ArgType::LONG,
            OpCode::IPUT_OBJECT => ArgType::unknown_object(),
            OpCode::IPUT_BOOLEAN => ArgType::BOOLEAN,
            OpCode::IPUT_BYTE => ArgType::BYTE,
            OpCode::IPUT_CHAR => ArgType::CHAR,
            OpCode::IPUT_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        Some(InsnNode::iput(
            InsnArg::Reg(RegisterArg::new(src, field_type)),
            InsnArg::Reg(RegisterArg::new(obj, ArgType::unknown_object())),
            field_idx,
        ))
    }

    // Decode sget
    fn decode_sget(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xFF) as RegNum;
        let field_idx = w1 as u32;

        let field_type = match opcode {
            OpCode::SGET => ArgType::INT,
            OpCode::SGET_WIDE => ArgType::LONG,
            OpCode::SGET_OBJECT => ArgType::unknown_object(),
            OpCode::SGET_BOOLEAN => ArgType::BOOLEAN,
            OpCode::SGET_BYTE => ArgType::BYTE,
            OpCode::SGET_CHAR => ArgType::CHAR,
            OpCode::SGET_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        Some(InsnNode::sget(
            RegisterArg::new(dest, field_type),
            field_idx,
        ))
    }

    // Decode sput
    fn decode_sput(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let src = ((w0 >> 8) & 0xFF) as RegNum;
        let field_idx = w1 as u32;

        let field_type = match opcode {
            OpCode::SPUT => ArgType::INT,
            OpCode::SPUT_WIDE => ArgType::LONG,
            OpCode::SPUT_OBJECT => ArgType::unknown_object(),
            OpCode::SPUT_BOOLEAN => ArgType::BOOLEAN,
            OpCode::SPUT_BYTE => ArgType::BYTE,
            OpCode::SPUT_CHAR => ArgType::CHAR,
            OpCode::SPUT_SHORT => ArgType::SHORT,
            _ => ArgType::INT,
        };

        Some(InsnNode::sput(
            InsnArg::Reg(RegisterArg::new(src, field_type)),
            field_idx,
        ))
    }

    // Decode invoke
    fn decode_invoke(
        &self,
        w0: u16,
        w1: u16,
        w2: u16,
        opcode: OpCode,
        is_range: bool,
    ) -> Option<InsnNode> {
        let invoke_type = match opcode {
            OpCode::INVOKE_VIRTUAL | OpCode::INVOKE_VIRTUAL_RANGE => InvokeType::Virtual,
            OpCode::INVOKE_SUPER | OpCode::INVOKE_SUPER_RANGE => InvokeType::Super,
            OpCode::INVOKE_DIRECT | OpCode::INVOKE_DIRECT_RANGE => InvokeType::Direct,
            OpCode::INVOKE_STATIC | OpCode::INVOKE_STATIC_RANGE => InvokeType::Static,
            OpCode::INVOKE_INTERFACE | OpCode::INVOKE_INTERFACE_RANGE => InvokeType::Interface,
            _ => InvokeType::Virtual,
        };

        let method_idx = w1 as u32;

        let args: Vec<InsnArg> = if is_range {
            let count = ((w0 >> 8) & 0xFF) as u16;
            let start = w2;
            (0..count)
                .map(|i| InsnArg::Reg(RegisterArg::new((start + i) as RegNum, ArgType::unknown())))
                .collect()
        } else {
            let count = ((w0 >> 12) & 0xF) as usize;
            let c = w2 & 0xF;
            let d = (w2 >> 4) & 0xF;
            let e = (w2 >> 8) & 0xF;
            let f = (w2 >> 12) & 0xF;
            let g = (w0 >> 8) & 0xF;
            let all = [c, d, e, f, g];
            all[..count]
                .iter()
                .map(|&r| InsnArg::Reg(RegisterArg::new(r as RegNum, ArgType::unknown())))
                .collect()
        };

        Some(InsnNode::invoke(invoke_type, method_idx, args))
    }

    // Decode unary
    fn decode_unary(&self, w0: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xF) as RegNum;
        let src = ((w0 >> 12) & 0xF) as RegNum;

        let (unary_op, dest_type, src_type) = match opcode {
            OpCode::NEG_INT => (UnaryOp::Neg, ArgType::INT, ArgType::INT),
            OpCode::NOT_INT => (UnaryOp::Not, ArgType::INT, ArgType::INT),
            OpCode::NEG_LONG => (UnaryOp::Neg, ArgType::LONG, ArgType::LONG),
            OpCode::NOT_LONG => (UnaryOp::Not, ArgType::LONG, ArgType::LONG),
            OpCode::NEG_FLOAT => (UnaryOp::Neg, ArgType::FLOAT, ArgType::FLOAT),
            OpCode::NEG_DOUBLE => (UnaryOp::Neg, ArgType::DOUBLE, ArgType::DOUBLE),
            OpCode::INT_TO_LONG => (UnaryOp::IntToLong, ArgType::LONG, ArgType::INT),
            OpCode::INT_TO_FLOAT => (UnaryOp::IntToFloat, ArgType::FLOAT, ArgType::INT),
            OpCode::INT_TO_DOUBLE => (UnaryOp::IntToDouble, ArgType::DOUBLE, ArgType::INT),
            OpCode::LONG_TO_INT => (UnaryOp::LongToInt, ArgType::INT, ArgType::LONG),
            OpCode::LONG_TO_FLOAT => (UnaryOp::LongToFloat, ArgType::FLOAT, ArgType::LONG),
            OpCode::LONG_TO_DOUBLE => (UnaryOp::LongToDouble, ArgType::DOUBLE, ArgType::LONG),
            OpCode::FLOAT_TO_INT => (UnaryOp::FloatToInt, ArgType::INT, ArgType::FLOAT),
            OpCode::FLOAT_TO_LONG => (UnaryOp::FloatToLong, ArgType::LONG, ArgType::FLOAT),
            OpCode::FLOAT_TO_DOUBLE => (UnaryOp::FloatToDouble, ArgType::DOUBLE, ArgType::FLOAT),
            OpCode::DOUBLE_TO_INT => (UnaryOp::DoubleToInt, ArgType::INT, ArgType::DOUBLE),
            OpCode::DOUBLE_TO_LONG => (UnaryOp::DoubleToLong, ArgType::LONG, ArgType::DOUBLE),
            OpCode::DOUBLE_TO_FLOAT => (UnaryOp::DoubleToFloat, ArgType::FLOAT, ArgType::DOUBLE),
            OpCode::INT_TO_BYTE => (UnaryOp::IntToByte, ArgType::BYTE, ArgType::INT),
            OpCode::INT_TO_CHAR => (UnaryOp::IntToChar, ArgType::CHAR, ArgType::INT),
            OpCode::INT_TO_SHORT => (UnaryOp::IntToShort, ArgType::SHORT, ArgType::INT),
            _ => (UnaryOp::Neg, ArgType::INT, ArgType::INT),
        };

        Some(InsnNode::unary(
            unary_op,
            RegisterArg::new(dest, dest_type),
            InsnArg::Reg(RegisterArg::new(src, src_type)),
        ))
    }

    // Decode binary 3addr
    fn decode_binary_3addr(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xFF) as RegNum;
        let src1 = (w1 & 0xFF) as RegNum;
        let src2 = ((w1 >> 8) & 0xFF) as RegNum;

        let (arith_op, arg_type) = decode_arith_op_3addr(opcode);
        Some(InsnNode::arith(
            arith_op,
            RegisterArg::new(dest, arg_type.clone()),
            InsnArg::Reg(RegisterArg::new(src1, arg_type.clone())),
            InsnArg::reg(src2, arg_type.clone()),
            arg_type,
        ))
    }

    // Decode binary 2addr
    fn decode_binary_2addr(&self, w0: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xF) as RegNum;
        let src = ((w0 >> 12) & 0xF) as RegNum;

        let (arith_op, arg_type) = decode_arith_op_2addr(opcode);
        let dest_reg = RegisterArg::new(dest, arg_type.clone());
        Some(InsnNode::arith(
            arith_op,
            dest_reg.clone(),
            InsnArg::Reg(dest_reg),
            InsnArg::reg(src, arg_type.clone()),
            arg_type,
        ))
    }

    // Decode binary lit16
    fn decode_binary_lit16(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xF) as RegNum;
        let src = ((w0 >> 12) & 0xF) as RegNum;
        let lit = w1 as i16 as i64;

        let arith_op = decode_arith_op_lit16(opcode);
        Some(InsnNode::arith(
            arith_op,
            RegisterArg::new(dest, ArgType::INT),
            InsnArg::Reg(RegisterArg::new(src, ArgType::INT)),
            InsnArg::lit(lit, ArgType::INT),
            ArgType::INT,
        ))
    }

    // Decode binary lit8
    fn decode_binary_lit8(&self, w0: u16, w1: u16, opcode: OpCode) -> Option<InsnNode> {
        let dest = ((w0 >> 8) & 0xFF) as RegNum;
        let src = (w1 & 0xFF) as RegNum;
        let lit = ((w1 >> 8) & 0xFF) as i8 as i64;

        let arith_op = decode_arith_op_lit8(opcode);
        Some(InsnNode::arith(
            arith_op,
            RegisterArg::new(dest, ArgType::INT),
            InsnArg::Reg(RegisterArg::new(src, ArgType::INT)),
            InsnArg::lit(lit, ArgType::INT),
            ArgType::INT,
        ))
    }

    // Decode packed-switch payload
    fn decode_packed_switch(&self, insn_offset: usize, payload_offset: i32) -> Vec<(i32, i32)> {
        let payload_addr = (insn_offset as i32 + payload_offset) as usize;
        let Some(payload_insn) = self.find_instruction_at_offset(payload_addr) else {
            return Vec::new();
        };

        let Instructions::PackedSwitchPayload(payload) = payload_insn else {
            return Vec::new();
        };

        let first_key = payload.get_first_key();
        let mut cases = Vec::with_capacity(payload.get_size());
        for (i, target_offset) in payload.get_targets().iter().enumerate() {
            let key = first_key + i as i32;
            let target = insn_offset as i32 + *target_offset;
            cases.push((key, target));
        }

        cases
    }

    // Decode sparse-switch payload
    fn decode_sparse_switch(&self, insn_offset: usize, payload_offset: i32) -> Vec<(i32, i32)> {
        let payload_addr = (insn_offset as i32 + payload_offset) as usize;
        let Some(payload_insn) = self.find_instruction_at_offset(payload_addr) else {
            return Vec::new();
        };

        let Instructions::SparseSwitchPayload(payload) = payload_insn else {
            return Vec::new();
        };

        let mut cases = Vec::with_capacity(payload.get_size());
        for (key, target_offset) in payload.get_keys().iter().zip(payload.get_targets().iter()) {
            let target = insn_offset as i32 + *target_offset;
            cases.push((*key, target));
        }

        cases
    }
}

// Helper functions
fn decode_arith_op_3addr(opcode: OpCode) -> (ArithOp, ArgType) {
    match opcode {
        OpCode::ADD_INT => (ArithOp::Add, ArgType::INT),
        OpCode::SUB_INT => (ArithOp::Sub, ArgType::INT),
        OpCode::MUL_INT => (ArithOp::Mul, ArgType::INT),
        OpCode::DIV_INT => (ArithOp::Div, ArgType::INT),
        OpCode::REM_INT => (ArithOp::Rem, ArgType::INT),
        OpCode::AND_INT => (ArithOp::And, ArgType::INT),
        OpCode::OR_INT => (ArithOp::Or, ArgType::INT),
        OpCode::XOR_INT => (ArithOp::Xor, ArgType::INT),
        OpCode::SHL_INT => (ArithOp::Shl, ArgType::INT),
        OpCode::SHR_INT => (ArithOp::Shr, ArgType::INT),
        OpCode::USHR_INT => (ArithOp::Ushr, ArgType::INT),
        OpCode::ADD_LONG => (ArithOp::Add, ArgType::LONG),
        OpCode::SUB_LONG => (ArithOp::Sub, ArgType::LONG),
        OpCode::MUL_LONG => (ArithOp::Mul, ArgType::LONG),
        OpCode::DIV_LONG => (ArithOp::Div, ArgType::LONG),
        OpCode::REM_LONG => (ArithOp::Rem, ArgType::LONG),
        OpCode::AND_LONG => (ArithOp::And, ArgType::LONG),
        OpCode::OR_LONG => (ArithOp::Or, ArgType::LONG),
        OpCode::XOR_LONG => (ArithOp::Xor, ArgType::LONG),
        OpCode::SHL_LONG => (ArithOp::Shl, ArgType::LONG),
        OpCode::SHR_LONG => (ArithOp::Shr, ArgType::LONG),
        OpCode::USHR_LONG => (ArithOp::Ushr, ArgType::LONG),
        OpCode::ADD_FLOAT => (ArithOp::Add, ArgType::FLOAT),
        OpCode::SUB_FLOAT => (ArithOp::Sub, ArgType::FLOAT),
        OpCode::MUL_FLOAT => (ArithOp::Mul, ArgType::FLOAT),
        OpCode::DIV_FLOAT => (ArithOp::Div, ArgType::FLOAT),
        OpCode::REM_FLOAT => (ArithOp::Rem, ArgType::FLOAT),
        OpCode::ADD_DOUBLE => (ArithOp::Add, ArgType::DOUBLE),
        OpCode::SUB_DOUBLE => (ArithOp::Sub, ArgType::DOUBLE),
        OpCode::MUL_DOUBLE => (ArithOp::Mul, ArgType::DOUBLE),
        OpCode::DIV_DOUBLE => (ArithOp::Div, ArgType::DOUBLE),
        OpCode::REM_DOUBLE => (ArithOp::Rem, ArgType::DOUBLE),
        _ => (ArithOp::Add, ArgType::INT),
    }
}

fn decode_arith_op_2addr(opcode: OpCode) -> (ArithOp, ArgType) {
    match opcode {
        OpCode::ADD_INT_2ADDR => (ArithOp::Add, ArgType::INT),
        OpCode::SUB_INT_2ADDR => (ArithOp::Sub, ArgType::INT),
        OpCode::MUL_INT_2ADDR => (ArithOp::Mul, ArgType::INT),
        OpCode::DIV_INT_2ADDR => (ArithOp::Div, ArgType::INT),
        OpCode::REM_INT_2ADDR => (ArithOp::Rem, ArgType::INT),
        OpCode::AND_INT_2ADDR => (ArithOp::And, ArgType::INT),
        OpCode::OR_INT_2ADDR => (ArithOp::Or, ArgType::INT),
        OpCode::XOR_INT_2ADDR => (ArithOp::Xor, ArgType::INT),
        OpCode::SHL_INT_2ADDR => (ArithOp::Shl, ArgType::INT),
        OpCode::SHR_INT_2ADDR => (ArithOp::Shr, ArgType::INT),
        OpCode::USHR_INT_2ADDR => (ArithOp::Ushr, ArgType::INT),
        OpCode::ADD_LONG_2ADDR => (ArithOp::Add, ArgType::LONG),
        OpCode::SUB_LONG_2ADDR => (ArithOp::Sub, ArgType::LONG),
        OpCode::MUL_LONG_2ADDR => (ArithOp::Mul, ArgType::LONG),
        OpCode::DIV_LONG_2ADDR => (ArithOp::Div, ArgType::LONG),
        OpCode::REM_LONG_2ADDR => (ArithOp::Rem, ArgType::LONG),
        OpCode::AND_LONG_2ADDR => (ArithOp::And, ArgType::LONG),
        OpCode::OR_LONG_2ADDR => (ArithOp::Or, ArgType::LONG),
        OpCode::XOR_LONG_2ADDR => (ArithOp::Xor, ArgType::LONG),
        OpCode::SHL_LONG_2ADDR => (ArithOp::Shl, ArgType::LONG),
        OpCode::SHR_LONG_2ADDR => (ArithOp::Shr, ArgType::LONG),
        OpCode::USHR_LONG_2ADDR => (ArithOp::Ushr, ArgType::LONG),
        OpCode::ADD_FLOAT_2ADDR => (ArithOp::Add, ArgType::FLOAT),
        OpCode::SUB_FLOAT_2ADDR => (ArithOp::Sub, ArgType::FLOAT),
        OpCode::MUL_FLOAT_2ADDR => (ArithOp::Mul, ArgType::FLOAT),
        OpCode::DIV_FLOAT_2ADDR => (ArithOp::Div, ArgType::FLOAT),
        OpCode::REM_FLOAT_2ADDR => (ArithOp::Rem, ArgType::FLOAT),
        OpCode::ADD_DOUBLE_2ADDR => (ArithOp::Add, ArgType::DOUBLE),
        OpCode::SUB_DOUBLE_2ADDR => (ArithOp::Sub, ArgType::DOUBLE),
        OpCode::MUL_DOUBLE_2ADDR => (ArithOp::Mul, ArgType::DOUBLE),
        OpCode::DIV_DOUBLE_2ADDR => (ArithOp::Div, ArgType::DOUBLE),
        OpCode::REM_DOUBLE_2ADDR => (ArithOp::Rem, ArgType::DOUBLE),
        _ => (ArithOp::Add, ArgType::INT),
    }
}

fn decode_arith_op_lit16(opcode: OpCode) -> ArithOp {
    match opcode {
        OpCode::ADD_INT_LIT16 => ArithOp::Add,
        OpCode::RSUB_INT => ArithOp::Rsub,
        OpCode::MUL_INT_LIT16 => ArithOp::Mul,
        OpCode::DIV_INT_LIT16 => ArithOp::Div,
        OpCode::REM_INT_LIT16 => ArithOp::Rem,
        OpCode::AND_INT_LIT16 => ArithOp::And,
        OpCode::OR_INT_LIT16 => ArithOp::Or,
        OpCode::XOR_INT_LIT16 => ArithOp::Xor,
        _ => ArithOp::Add,
    }
}

fn decode_arith_op_lit8(opcode: OpCode) -> ArithOp {
    match opcode {
        OpCode::ADD_INT_LIT8 => ArithOp::Add,
        OpCode::RSUB_INT_LIT8 => ArithOp::Rsub,
        OpCode::MUL_INT_LIT8 => ArithOp::Mul,
        OpCode::DIV_INT_LIT8 => ArithOp::Div,
        OpCode::REM_INT_LIT8 => ArithOp::Rem,
        OpCode::AND_INT_LIT8 => ArithOp::And,
        OpCode::OR_INT_LIT8 => ArithOp::Or,
        OpCode::XOR_INT_LIT8 => ArithOp::Xor,
        OpCode::SHL_INT_LIT8 => ArithOp::Shl,
        OpCode::SHR_INT_LIT8 => ArithOp::Shr,
        OpCode::USHR_INT_LIT8 => ArithOp::Ushr,
        _ => ArithOp::Add,
    }
}
