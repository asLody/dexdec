//! Dalvik instructions
//!
//! This module contains the definition of all instructions types, including
//! special instructions such as `PackedSwitch` which have their payload
//! at the end of the `CodeItem` of a method.

use crate::dex::opcodes::OpCode;
use crate::dex::reader::DexReader;
use crate::error::DexError;

/// `Instruction10t` instruction type
#[derive(Debug, Clone)]
pub struct Instruction10t {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 1],
}
/// `Instruction10x` instruction type
#[derive(Debug, Clone)]
pub struct Instruction10x {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 1],
}
/// `Instruction11n` instruction type
#[derive(Debug, Clone)]
pub struct Instruction11n {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 1],
}
/// `Instruction11x` instruction type
#[derive(Debug, Clone)]
pub struct Instruction11x {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 1],
}
/// `Instruction12x` instruction type
#[derive(Debug, Clone)]
pub struct Instruction12x {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 1],
}
/// `Instruction20t` instruction type
#[derive(Debug, Clone)]
pub struct Instruction20t {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction21c` instruction type
#[derive(Debug, Clone)]
pub struct Instruction21c {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction21h` instruction type
#[derive(Debug, Clone)]
pub struct Instruction21h {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction21s` instruction type
#[derive(Debug, Clone)]
pub struct Instruction21s {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction21t` instruction type
#[derive(Debug, Clone)]
pub struct Instruction21t {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction22b` instruction type
#[derive(Debug, Clone)]
pub struct Instruction22b {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction22c` instruction type
#[derive(Debug, Clone)]
pub struct Instruction22c {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction22s` instruction type
#[derive(Debug, Clone)]
pub struct Instruction22s {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction22t` instruction type
#[derive(Debug, Clone)]
pub struct Instruction22t {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction22x` instruction type
#[derive(Debug, Clone)]
pub struct Instruction22x {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction23x` instruction type
#[derive(Debug, Clone)]
pub struct Instruction23x {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 2],
}
/// `Instruction30t` instruction type
#[derive(Debug, Clone)]
pub struct Instruction30t {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 3],
}
/// `Instruction31c` instruction type
#[derive(Debug, Clone)]
pub struct Instruction31c {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 3],
}
/// `Instruction31i` instruction type
#[derive(Debug, Clone)]
pub struct Instruction31i {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 3],
}
/// `Instruction31t` instruction type
#[derive(Debug, Clone)]
pub struct Instruction31t {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 3],
}
/// `Instruction32x` instruction type
#[derive(Debug, Clone)]
pub struct Instruction32x {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 3],
}
/// `Instruction35c` instruction type
#[derive(Debug, Clone)]
pub struct Instruction35c {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 3],
}
/// `Instruction3rc` instruction type
#[derive(Debug, Clone)]
pub struct Instruction3rc {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 3],
}
/// `Instruction45cc` instruction type
#[derive(Debug, Clone)]
pub struct Instruction45cc {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 4],
}
/// `Instruction4rcc` instruction type
#[derive(Debug, Clone)]
pub struct Instruction4rcc {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 4],
}
/// `Instruction51l` instruction type
#[derive(Debug, Clone)]
pub struct Instruction51l {
    opcode: OpCode,
    length: usize,
    pub bytes: [u16; 5],
}
/// `PackedSwitchPayload` instruction type
#[derive(Debug, Clone)]
pub struct PackedSwitchPayload {
    opcode: OpCode,
    size: u16,
    first_key: i32,
    targets: Vec<i32>,
}
/// `SparseSwitchPayload` instruction type
#[derive(Debug, Clone)]
pub struct SparseSwitchPayload {
    opcode: OpCode,
    size: u16,
    keys: Vec<i32>,
    targets: Vec<i32>,
}
/// `FillArrayDataPayload` instruction type
#[derive(Debug, Clone)]
pub struct FillArrayDataPayload {
    opcode: OpCode,
    element_width: u16,
    size: u32,
    data: Vec<u8>,
}

impl PackedSwitchPayload {
    /// Create a `PackedSwitchPayload` instruction from the reader
    fn build(reader: &mut DexReader) -> Result<Self, DexError> {
        let size = reader.read_u16()?;
        let first_key = reader.read_i32()?;

        let mut targets = Vec::with_capacity(size.into());
        for _ in 0..size {
            targets.push(reader.read_i32()?);
        }

        Ok(PackedSwitchPayload {
            opcode: OpCode::PACKED_SWITCH_PAYLOAD,
            size,
            first_key,
            targets,
        })
    }

    pub fn get_size(&self) -> usize {
        self.size as usize
    }

    pub fn get_first_key(&self) -> i32 {
        self.first_key
    }

    pub fn get_targets(&self) -> &[i32] {
        &self.targets
    }

    fn length(&self) -> usize {
        // nb of entries in bytes + size of (opcode and size)
        ((self.size * 2) + 4).into()
    }

    fn opcode(&self) -> OpCode {
        OpCode::PACKED_SWITCH_PAYLOAD
    }

    // TODO: find a better fallback. This instruction
    // does not have "bytes" like the others but we
    // need to implement this function as part of the
    // trait implementation.
    fn bytes(&self) -> &[u16] {
        &[]
    }

    fn inst_format(&self) -> &str {
        "PackedSwitchPayload"
    }
}

impl SparseSwitchPayload {
    /// Create a `SparseSwitchPayload` instruction from the reader
    fn build(reader: &mut DexReader) -> Result<Self, DexError> {
        let size = reader.read_u16()?;

        let mut keys = Vec::with_capacity(size.into());
        for _ in 0..size {
            keys.push(reader.read_i32()?);
        }

        let mut targets = Vec::with_capacity(size.into());
        for _ in 0..size {
            targets.push(reader.read_i32()?);
        }

        Ok(SparseSwitchPayload {
            opcode: OpCode::SPARSE_SWITCH_PAYLOAD,
            size,
            keys,
            targets,
        })
    }

    pub fn get_size(&self) -> usize {
        self.size as usize
    }

    pub fn get_keys(&self) -> &[i32] {
        &self.keys
    }

    pub fn get_targets(&self) -> &[i32] {
        &self.targets
    }

    fn length(&self) -> usize {
        ((self.size * 4) + 2).into()
    }

    fn opcode(&self) -> OpCode {
        OpCode::SPARSE_SWITCH_PAYLOAD
    }

    // TODO: find a better fallback. This instruction
    // does not have "bytes" like the others but we
    // need to implement this function as part of the
    // trait implementation.
    fn bytes(&self) -> &[u16] {
        &[]
    }

    fn inst_format(&self) -> &str {
        "SparseSwitchPayload"
    }
}

impl FillArrayDataPayload {
    /// Create a `FillArrayDataPayload` instruction from the reader
    fn build(reader: &mut DexReader) -> Result<Self, DexError> {
        // FIXME the bytes come up empty, check the bounds of the for loop
        let element_width = reader.read_u16()?;
        let size = reader.read_u32()?;

        let mut data = Vec::with_capacity((size * element_width as u32) as usize);
        for _ in 0..size {
            for _ in 0..element_width {
                data.push(reader.read_u8()?);
            }
        }

        Ok(FillArrayDataPayload {
            opcode: OpCode::FILL_ARRAY_DATA_PAYLOAD,
            element_width,
            size,
            data,
        })
    }

    pub fn get_element_width(&self) -> u16 {
        self.element_width
    }

    pub fn get_size(&self) -> u32 {
        self.size
    }

    pub fn get_data(&self) -> &[u8] {
        &self.data
    }

    fn length(&self) -> usize {
        ((self.size * self.element_width as u32).div_ceil(2) + 4) as usize
    }

    fn opcode(&self) -> OpCode {
        OpCode::FILL_ARRAY_DATA_PAYLOAD
    }

    // TODO: find a better fallback. This instruction
    // does not have "bytes" like the others but we
    // need to implement this function as part of the
    // trait implementation.
    fn bytes(&self) -> &[u16] {
        &[]
    }

    fn inst_format(&self) -> &str {
        "FillArrayDataPayload"
    }
}

/// Enumeration of all possible instruction types
#[derive(Debug, Clone)]
pub enum Instructions {
    Instruction10t(Instruction10t),
    Instruction10x(Instruction10x),
    Instruction11n(Instruction11n),
    Instruction11x(Instruction11x),
    Instruction12x(Instruction12x),
    Instruction20t(Instruction20t),
    Instruction21c(Instruction21c),
    Instruction21h(Instruction21h),
    Instruction21s(Instruction21s),
    Instruction21t(Instruction21t),
    Instruction22b(Instruction22b),
    Instruction22c(Instruction22c),
    Instruction22s(Instruction22s),
    Instruction22t(Instruction22t),
    Instruction22x(Instruction22x),
    Instruction23x(Instruction23x),
    Instruction30t(Instruction30t),
    Instruction31c(Instruction31c),
    Instruction31i(Instruction31i),
    Instruction31t(Instruction31t),
    Instruction32x(Instruction32x),
    Instruction35c(Instruction35c),
    Instruction3rc(Instruction3rc),
    Instruction45cc(Instruction45cc),
    Instruction4rcc(Instruction4rcc),
    Instruction51l(Instruction51l),
    PackedSwitchPayload(PackedSwitchPayload),
    SparseSwitchPayload(SparseSwitchPayload),
    FillArrayDataPayload(FillArrayDataPayload),
}

impl Instructions {
    /// Get the length of a given instruction
    pub fn length(&self) -> usize {
        match self {
            Instructions::Instruction10t(inst) => inst.length,
            Instructions::Instruction10x(inst) => inst.length,
            Instructions::Instruction11n(inst) => inst.length,
            Instructions::Instruction11x(inst) => inst.length,
            Instructions::Instruction12x(inst) => inst.length,
            Instructions::Instruction20t(inst) => inst.length,
            Instructions::Instruction21c(inst) => inst.length,
            Instructions::Instruction21h(inst) => inst.length,
            Instructions::Instruction21s(inst) => inst.length,
            Instructions::Instruction21t(inst) => inst.length,
            Instructions::Instruction22b(inst) => inst.length,
            Instructions::Instruction22c(inst) => inst.length,
            Instructions::Instruction22s(inst) => inst.length,
            Instructions::Instruction22t(inst) => inst.length,
            Instructions::Instruction22x(inst) => inst.length,
            Instructions::Instruction23x(inst) => inst.length,
            Instructions::Instruction30t(inst) => inst.length,
            Instructions::Instruction31c(inst) => inst.length,
            Instructions::Instruction31i(inst) => inst.length,
            Instructions::Instruction31t(inst) => inst.length,
            Instructions::Instruction32x(inst) => inst.length,
            Instructions::Instruction35c(inst) => inst.length,
            Instructions::Instruction3rc(inst) => inst.length,
            Instructions::Instruction45cc(inst) => inst.length,
            Instructions::Instruction4rcc(inst) => inst.length,
            Instructions::Instruction51l(inst) => inst.length,
            Instructions::PackedSwitchPayload(inst) => inst.length(),
            Instructions::SparseSwitchPayload(inst) => inst.length(),
            Instructions::FillArrayDataPayload(inst) => inst.length(),
        }
    }

    /// Get the opcode of a given instruction
    pub fn opcode(&self) -> OpCode {
        match self {
            Instructions::Instruction10t(inst) => inst.opcode,
            Instructions::Instruction10x(inst) => inst.opcode,
            Instructions::Instruction11n(inst) => inst.opcode,
            Instructions::Instruction11x(inst) => inst.opcode,
            Instructions::Instruction12x(inst) => inst.opcode,
            Instructions::Instruction20t(inst) => inst.opcode,
            Instructions::Instruction21c(inst) => inst.opcode,
            Instructions::Instruction21h(inst) => inst.opcode,
            Instructions::Instruction21s(inst) => inst.opcode,
            Instructions::Instruction21t(inst) => inst.opcode,
            Instructions::Instruction22b(inst) => inst.opcode,
            Instructions::Instruction22c(inst) => inst.opcode,
            Instructions::Instruction22s(inst) => inst.opcode,
            Instructions::Instruction22t(inst) => inst.opcode,
            Instructions::Instruction22x(inst) => inst.opcode,
            Instructions::Instruction23x(inst) => inst.opcode,
            Instructions::Instruction30t(inst) => inst.opcode,
            Instructions::Instruction31c(inst) => inst.opcode,
            Instructions::Instruction31i(inst) => inst.opcode,
            Instructions::Instruction31t(inst) => inst.opcode,
            Instructions::Instruction32x(inst) => inst.opcode,
            Instructions::Instruction35c(inst) => inst.opcode,
            Instructions::Instruction3rc(inst) => inst.opcode,
            Instructions::Instruction45cc(inst) => inst.opcode,
            Instructions::Instruction4rcc(inst) => inst.opcode,
            Instructions::Instruction51l(inst) => inst.opcode,
            Instructions::PackedSwitchPayload(inst) => inst.opcode,
            Instructions::SparseSwitchPayload(inst) => inst.opcode,
            Instructions::FillArrayDataPayload(inst) => inst.opcode,
        }
    }

    /// Get the bytes of a given instruction
    pub fn bytes(&self) -> &[u16] {
        match self {
            Instructions::Instruction10t(inst) => &inst.bytes,
            Instructions::Instruction10x(inst) => &inst.bytes,
            Instructions::Instruction11n(inst) => &inst.bytes,
            Instructions::Instruction11x(inst) => &inst.bytes,
            Instructions::Instruction12x(inst) => &inst.bytes,
            Instructions::Instruction20t(inst) => &inst.bytes,
            Instructions::Instruction21c(inst) => &inst.bytes,
            Instructions::Instruction21h(inst) => &inst.bytes,
            Instructions::Instruction21s(inst) => &inst.bytes,
            Instructions::Instruction21t(inst) => &inst.bytes,
            Instructions::Instruction22b(inst) => &inst.bytes,
            Instructions::Instruction22c(inst) => &inst.bytes,
            Instructions::Instruction22s(inst) => &inst.bytes,
            Instructions::Instruction22t(inst) => &inst.bytes,
            Instructions::Instruction22x(inst) => &inst.bytes,
            Instructions::Instruction23x(inst) => &inst.bytes,
            Instructions::Instruction30t(inst) => &inst.bytes,
            Instructions::Instruction31c(inst) => &inst.bytes,
            Instructions::Instruction31i(inst) => &inst.bytes,
            Instructions::Instruction31t(inst) => &inst.bytes,
            Instructions::Instruction32x(inst) => &inst.bytes,
            Instructions::Instruction35c(inst) => &inst.bytes,
            Instructions::Instruction3rc(inst) => &inst.bytes,
            Instructions::Instruction45cc(inst) => &inst.bytes,
            Instructions::Instruction4rcc(inst) => &inst.bytes,
            Instructions::Instruction51l(inst) => &inst.bytes,
            Instructions::PackedSwitchPayload(_) => &[], // FIXME
            Instructions::SparseSwitchPayload(_) => &[], // FIXME
            Instructions::FillArrayDataPayload(_) => &[], // FIXME
        }
    }
}

/////////////////////////////////////////////////////////////////

/// Parse an instruction from the reader
pub fn parse_instruction(
    reader: &mut DexReader,
    container: &mut Vec<Instructions>,
) -> Result<usize, DexError> {
    let raw_opcode = reader.read_u16()?;

    let opcode = match OpCode::parse((raw_opcode & 0xff).try_into().unwrap()) {
        // Deal with the special cases of fill-array-data-payload,
        // packed-switch-payload, and sparse-switch-payload
        Some(OpCode::NOP) => match raw_opcode >> 8 {
            0x01 => OpCode::PACKED_SWITCH_PAYLOAD,
            0x02 => OpCode::SPARSE_SWITCH_PAYLOAD,
            0x03 => OpCode::FILL_ARRAY_DATA_PAYLOAD,
            _ => OpCode::NOP,
        },
        Some(code) => code,
        None => return Err(DexError::InvalidOpCode),
    };

    match opcode {
        OpCode::GOTO => {
            let mut bytes = [0u16; 1];
            bytes[0] = raw_opcode;
            container.push(Instructions::Instruction10t(Instruction10t {
                opcode,
                bytes,
                length: 1,
            }));
            Ok(1)
        }

        OpCode::NOP | OpCode::RETURN_VOID => {
            let mut bytes = [0u16; 1];
            bytes[0] = raw_opcode;
            container.push(Instructions::Instruction10x(Instruction10x {
                opcode,
                bytes,
                length: 1,
            }));
            Ok(1)
        }

        OpCode::CONST_4 => {
            let mut bytes = [0u16; 1];
            bytes[0] = raw_opcode;
            container.push(Instructions::Instruction11n(Instruction11n {
                opcode,
                bytes,
                length: 1,
            }));
            Ok(1)
        }

        OpCode::MONITOR_ENTER
        | OpCode::MONITOR_EXIT
        | OpCode::MOVE_EXCEPTION
        | OpCode::MOVE_RESULT
        | OpCode::MOVE_RESULT_OBJECT
        | OpCode::MOVE_RESULT_WIDE
        | OpCode::RETURN
        | OpCode::RETURN_OBJECT
        | OpCode::RETURN_WIDE
        | OpCode::THROW => {
            let mut bytes = [0u16; 1];
            bytes[0] = raw_opcode;
            container.push(Instructions::Instruction11x(Instruction11x {
                opcode,
                bytes,
                length: 1,
            }));
            Ok(1)
        }

        OpCode::ADD_DOUBLE_2ADDR
        | OpCode::ADD_FLOAT_2ADDR
        | OpCode::ADD_INT_2ADDR
        | OpCode::ADD_LONG_2ADDR
        | OpCode::AND_INT_2ADDR
        | OpCode::AND_LONG_2ADDR
        | OpCode::ARRAY_LENGTH
        | OpCode::DIV_DOUBLE_2ADDR
        | OpCode::DIV_FLOAT_2ADDR
        | OpCode::DIV_INT_2ADDR
        | OpCode::DIV_LONG_2ADDR
        | OpCode::DOUBLE_TO_FLOAT
        | OpCode::DOUBLE_TO_INT
        | OpCode::DOUBLE_TO_LONG
        | OpCode::FLOAT_TO_DOUBLE
        | OpCode::FLOAT_TO_INT
        | OpCode::FLOAT_TO_LONG
        | OpCode::INT_TO_BYTE
        | OpCode::INT_TO_CHAR
        | OpCode::INT_TO_DOUBLE
        | OpCode::INT_TO_FLOAT
        | OpCode::INT_TO_LONG
        | OpCode::INT_TO_SHORT
        | OpCode::LONG_TO_DOUBLE
        | OpCode::LONG_TO_FLOAT
        | OpCode::LONG_TO_INT
        | OpCode::MOVE
        | OpCode::MOVE_OBJECT
        | OpCode::MOVE_WIDE
        | OpCode::MUL_DOUBLE_2ADDR
        | OpCode::MUL_FLOAT_2ADDR
        | OpCode::MUL_INT_2ADDR
        | OpCode::MUL_LONG_2ADDR
        | OpCode::NEG_DOUBLE
        | OpCode::NEG_FLOAT
        | OpCode::NEG_INT
        | OpCode::NEG_LONG
        | OpCode::NOT_INT
        | OpCode::NOT_LONG
        | OpCode::OR_INT_2ADDR
        | OpCode::OR_LONG_2ADDR
        | OpCode::REM_DOUBLE_2ADDR
        | OpCode::REM_FLOAT_2ADDR
        | OpCode::REM_INT_2ADDR
        | OpCode::REM_LONG_2ADDR
        | OpCode::SHL_INT_2ADDR
        | OpCode::SHL_LONG_2ADDR
        | OpCode::SHR_INT_2ADDR
        | OpCode::SHR_LONG_2ADDR
        | OpCode::SUB_DOUBLE_2ADDR
        | OpCode::SUB_FLOAT_2ADDR
        | OpCode::SUB_INT_2ADDR
        | OpCode::SUB_LONG_2ADDR
        | OpCode::USHR_INT_2ADDR
        | OpCode::USHR_LONG_2ADDR
        | OpCode::XOR_INT_2ADDR
        | OpCode::XOR_LONG_2ADDR => {
            let mut bytes = [0u16; 1];
            bytes[0] = raw_opcode;
            container.push(Instructions::Instruction12x(Instruction12x {
                opcode,
                bytes,
                length: 1,
            }));
            Ok(1)
        }

        OpCode::GOTO_16 => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction20t(Instruction20t {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::CHECK_CAST
        | OpCode::CONST_CLASS
        | OpCode::CONST_METHOD_HANDLE
        | OpCode::CONST_METHOD_TYPE
        | OpCode::CONST_STRING
        | OpCode::NEW_INSTANCE
        | OpCode::SGET_BOOLEAN
        | OpCode::SGET_BYTE
        | OpCode::SGET_CHAR
        | OpCode::SGET
        | OpCode::SGET_OBJECT
        | OpCode::SGET_SHORT
        | OpCode::SGET_WIDE
        | OpCode::SPUT_BOOLEAN
        | OpCode::SPUT_BYTE
        | OpCode::SPUT_CHAR
        | OpCode::SPUT
        | OpCode::SPUT_OBJECT
        | OpCode::SPUT_SHORT
        | OpCode::SPUT_WIDE => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction21c(Instruction21c {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::CONST_HIGH16 | OpCode::CONST_WIDE_HIGH16 => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction21h(Instruction21h {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::CONST_16 | OpCode::CONST_WIDE_16 => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction21s(Instruction21s {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::IF_EQZ
        | OpCode::IF_GEZ
        | OpCode::IF_GTZ
        | OpCode::IF_LEZ
        | OpCode::IF_LTZ
        | OpCode::IF_NEZ => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction21t(Instruction21t {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::ADD_INT_LIT8
        | OpCode::AND_INT_LIT8
        | OpCode::DIV_INT_LIT8
        | OpCode::MUL_INT_LIT8
        | OpCode::OR_INT_LIT8
        | OpCode::REM_INT_LIT8
        | OpCode::RSUB_INT_LIT8
        | OpCode::SHL_INT_LIT8
        | OpCode::SHR_INT_LIT8
        | OpCode::USHR_INT_LIT8
        | OpCode::XOR_INT_LIT8 => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction22b(Instruction22b {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::IGET_BOOLEAN
        | OpCode::IGET_BYTE
        | OpCode::IGET_CHAR
        | OpCode::IGET
        | OpCode::IGET_OBJECT
        | OpCode::IGET_SHORT
        | OpCode::IGET_WIDE
        | OpCode::INSTANCE_OF
        | OpCode::IPUT_BOOLEAN
        | OpCode::IPUT_BYTE
        | OpCode::IPUT_CHAR
        | OpCode::IPUT
        | OpCode::IPUT_OBJECT
        | OpCode::IPUT_SHORT
        | OpCode::IPUT_WIDE
        | OpCode::NEW_ARRAY => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction22c(Instruction22c {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::ADD_INT_LIT16
        | OpCode::AND_INT_LIT16
        | OpCode::DIV_INT_LIT16
        | OpCode::MUL_INT_LIT16
        | OpCode::OR_INT_LIT16
        | OpCode::REM_INT_LIT16
        | OpCode::RSUB_INT
        | OpCode::XOR_INT_LIT16 => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction22s(Instruction22s {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::IF_EQ
        | OpCode::IF_GE
        | OpCode::IF_GT
        | OpCode::IF_LE
        | OpCode::IF_LT
        | OpCode::IF_NE => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction22t(Instruction22t {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::MOVE_FROM16 | OpCode::MOVE_OBJECT_FROM16 | OpCode::MOVE_WIDE_FROM16 => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction22x(Instruction22x {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::ADD_DOUBLE
        | OpCode::ADD_FLOAT
        | OpCode::ADD_INT
        | OpCode::ADD_LONG
        | OpCode::AGET_BOOLEAN
        | OpCode::AGET_BYTE
        | OpCode::AGET_CHAR
        | OpCode::AGET
        | OpCode::AGET_OBJECT
        | OpCode::AGET_SHORT
        | OpCode::AGET_WIDE
        | OpCode::AND_INT
        | OpCode::AND_LONG
        | OpCode::APUT_BOOLEAN
        | OpCode::APUT_BYTE
        | OpCode::APUT_CHAR
        | OpCode::APUT
        | OpCode::APUT_OBJECT
        | OpCode::APUT_SHORT
        | OpCode::APUT_WIDE
        | OpCode::CMPG_DOUBLE
        | OpCode::CMPG_FLOAT
        | OpCode::CMPL_DOUBLE
        | OpCode::CMPL_FLOAT
        | OpCode::CMP_LONG
        | OpCode::DIV_DOUBLE
        | OpCode::DIV_FLOAT
        | OpCode::DIV_INT
        | OpCode::DIV_LONG
        | OpCode::MUL_DOUBLE
        | OpCode::MUL_FLOAT
        | OpCode::MUL_INT
        | OpCode::MUL_LONG
        | OpCode::OR_INT
        | OpCode::OR_LONG
        | OpCode::REM_DOUBLE
        | OpCode::REM_FLOAT
        | OpCode::REM_INT
        | OpCode::REM_LONG
        | OpCode::SHL_INT
        | OpCode::SHL_LONG
        | OpCode::SHR_INT
        | OpCode::SHR_LONG
        | OpCode::SUB_DOUBLE
        | OpCode::SUB_FLOAT
        | OpCode::SUB_INT
        | OpCode::SUB_LONG
        | OpCode::USHR_INT
        | OpCode::USHR_LONG
        | OpCode::XOR_INT
        | OpCode::XOR_LONG => {
            let mut bytes = [0u16; 2];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            container.push(Instructions::Instruction23x(Instruction23x {
                opcode,
                bytes,
                length: 2,
            }));
            Ok(2)
        }

        OpCode::GOTO_32 => {
            let mut bytes = [0u16; 3];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            container.push(Instructions::Instruction30t(Instruction30t {
                opcode,
                bytes,
                length: 3,
            }));
            Ok(3)
        }

        OpCode::CONST_STRING_JUMBO => {
            let mut bytes = [0u16; 3];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            container.push(Instructions::Instruction31c(Instruction31c {
                opcode,
                bytes,
                length: 3,
            }));
            Ok(3)
        }

        OpCode::CONST | OpCode::CONST_WIDE_32 => {
            let mut bytes = [0u16; 3];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            container.push(Instructions::Instruction31i(Instruction31i {
                opcode,
                bytes,
                length: 3,
            }));
            Ok(3)
        }

        OpCode::FILL_ARRAY_DATA | OpCode::PACKED_SWITCH | OpCode::SPARSE_SWITCH => {
            let mut bytes = [0u16; 3];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            container.push(Instructions::Instruction31t(Instruction31t {
                opcode,
                bytes,
                length: 3,
            }));
            Ok(3)
        }

        OpCode::MOVE_16 | OpCode::MOVE_OBJECT_16 | OpCode::MOVE_WIDE_16 => {
            let mut bytes = [0u16; 3];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            container.push(Instructions::Instruction32x(Instruction32x {
                opcode,
                bytes,
                length: 3,
            }));
            Ok(3)
        }

        OpCode::FILLED_NEW_ARRAY
        | OpCode::INVOKE_CUSTOM
        | OpCode::INVOKE_DIRECT
        | OpCode::INVOKE_INTERFACE
        | OpCode::INVOKE_STATIC
        | OpCode::INVOKE_SUPER
        | OpCode::INVOKE_VIRTUAL => {
            let mut bytes = [0u16; 3];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            container.push(Instructions::Instruction35c(Instruction35c {
                opcode,
                bytes,
                length: 3,
            }));
            Ok(3)
        }

        OpCode::FILLED_NEW_ARRAY_RANGE
        | OpCode::INVOKE_CUSTOM_RANGE
        | OpCode::INVOKE_DIRECT_RANGE
        | OpCode::INVOKE_INTERFACE_RANGE
        | OpCode::INVOKE_STATIC_RANGE
        | OpCode::INVOKE_SUPER_RANGE
        | OpCode::INVOKE_VIRTUAL_RANGE => {
            let mut bytes = [0u16; 3];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            container.push(Instructions::Instruction3rc(Instruction3rc {
                opcode,
                bytes,
                length: 3,
            }));
            Ok(3)
        }

        OpCode::INVOKE_POLYMORPHIC => {
            let mut bytes = [0u16; 4];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            bytes[3] = reader.read_u16()?;
            container.push(Instructions::Instruction45cc(Instruction45cc {
                opcode,
                bytes,
                length: 4,
            }));
            Ok(4)
        }

        OpCode::INVOKE_POLYMORPHIC_RANGE => {
            let mut bytes = [0u16; 4];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            bytes[3] = reader.read_u16()?;
            container.push(Instructions::Instruction4rcc(Instruction4rcc {
                opcode,
                bytes,
                length: 4,
            }));
            Ok(4)
        }

        OpCode::CONST_WIDE => {
            let mut bytes = [0u16; 5];
            bytes[0] = raw_opcode;
            bytes[1] = reader.read_u16()?;
            bytes[2] = reader.read_u16()?;
            bytes[3] = reader.read_u16()?;
            bytes[4] = reader.read_u16()?;
            container.push(Instructions::Instruction51l(Instruction51l {
                opcode,
                bytes,
                length: 5,
            }));
            Ok(5)
        }

        OpCode::PACKED_SWITCH_PAYLOAD => {
            let inst = PackedSwitchPayload::build(reader)?;
            let len = inst.length();
            container.push(Instructions::PackedSwitchPayload(inst));
            reader.align_cursor()?;
            Ok(len)
        }

        OpCode::SPARSE_SWITCH_PAYLOAD => {
            let inst = SparseSwitchPayload::build(reader)?;
            let len = inst.length();
            container.push(Instructions::SparseSwitchPayload(inst));
            reader.align_cursor()?;
            Ok(len)
        }

        OpCode::FILL_ARRAY_DATA_PAYLOAD => {
            let inst = FillArrayDataPayload::build(reader)?;
            let len = inst.length();
            container.push(Instructions::FillArrayDataPayload(inst));
            reader.align_cursor()?;
            Ok(len)
        }
    }
}
