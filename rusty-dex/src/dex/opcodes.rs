//! Opcodes module
//!
//! This modules defines the list of all possible opcodes in Dalvik, and a
//! method to convert an `u8` value into an `OpCode` object.

use log::warn;

/// All existing Dalvik opcodes
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum OpCode {
    NOP,
    MOVE,
    MOVE_FROM16,
    MOVE_16,
    MOVE_WIDE,
    MOVE_WIDE_FROM16,
    MOVE_WIDE_16,
    MOVE_OBJECT,
    MOVE_OBJECT_FROM16,
    MOVE_OBJECT_16,
    MOVE_RESULT,
    MOVE_RESULT_WIDE,
    MOVE_RESULT_OBJECT,
    MOVE_EXCEPTION,
    RETURN_VOID,
    RETURN,
    RETURN_WIDE,
    RETURN_OBJECT,
    CONST_4,
    CONST_16,
    CONST,
    CONST_HIGH16,
    CONST_WIDE_16,
    CONST_WIDE_32,
    CONST_WIDE,
    CONST_WIDE_HIGH16,
    CONST_STRING,
    CONST_STRING_JUMBO,
    CONST_CLASS,
    MONITOR_ENTER,
    MONITOR_EXIT,
    CHECK_CAST,
    INSTANCE_OF,
    ARRAY_LENGTH,
    NEW_INSTANCE,
    NEW_ARRAY,
    FILLED_NEW_ARRAY,
    FILLED_NEW_ARRAY_RANGE,
    FILL_ARRAY_DATA,
    THROW,
    GOTO,
    GOTO_16,
    GOTO_32,
    PACKED_SWITCH,
    SPARSE_SWITCH,
    CMPL_FLOAT,
    CMPG_FLOAT,
    CMPL_DOUBLE,
    CMPG_DOUBLE,
    CMP_LONG,
    IF_EQ,
    IF_NE,
    IF_LT,
    IF_GE,
    IF_GT,
    IF_LE,
    IF_EQZ,
    IF_NEZ,
    IF_LTZ,
    IF_GEZ,
    IF_GTZ,
    IF_LEZ,
    AGET,
    AGET_WIDE,
    AGET_OBJECT,
    AGET_BOOLEAN,
    AGET_BYTE,
    AGET_CHAR,
    AGET_SHORT,
    APUT,
    APUT_WIDE,
    APUT_OBJECT,
    APUT_BOOLEAN,
    APUT_BYTE,
    APUT_CHAR,
    APUT_SHORT,
    IGET,
    IGET_WIDE,
    IGET_OBJECT,
    IGET_BOOLEAN,
    IGET_BYTE,
    IGET_CHAR,
    IGET_SHORT,
    IPUT,
    IPUT_WIDE,
    IPUT_OBJECT,
    IPUT_BOOLEAN,
    IPUT_BYTE,
    IPUT_CHAR,
    IPUT_SHORT,
    SGET,
    SGET_WIDE,
    SGET_OBJECT,
    SGET_BOOLEAN,
    SGET_BYTE,
    SGET_CHAR,
    SGET_SHORT,
    SPUT,
    SPUT_WIDE,
    SPUT_OBJECT,
    SPUT_BOOLEAN,
    SPUT_BYTE,
    SPUT_CHAR,
    SPUT_SHORT,
    INVOKE_VIRTUAL,
    INVOKE_SUPER,
    INVOKE_DIRECT,
    INVOKE_STATIC,
    INVOKE_INTERFACE,
    INVOKE_VIRTUAL_RANGE,
    INVOKE_SUPER_RANGE,
    INVOKE_DIRECT_RANGE,
    INVOKE_STATIC_RANGE,
    INVOKE_INTERFACE_RANGE,
    NEG_INT,
    NOT_INT,
    NEG_LONG,
    NOT_LONG,
    NEG_FLOAT,
    NEG_DOUBLE,
    INT_TO_LONG,
    INT_TO_FLOAT,
    INT_TO_DOUBLE,
    LONG_TO_INT,
    LONG_TO_FLOAT,
    LONG_TO_DOUBLE,
    FLOAT_TO_INT,
    FLOAT_TO_LONG,
    FLOAT_TO_DOUBLE,
    DOUBLE_TO_INT,
    DOUBLE_TO_LONG,
    DOUBLE_TO_FLOAT,
    INT_TO_BYTE,
    INT_TO_CHAR,
    INT_TO_SHORT,
    ADD_INT,
    SUB_INT,
    MUL_INT,
    DIV_INT,
    REM_INT,
    AND_INT,
    OR_INT,
    XOR_INT,
    SHL_INT,
    SHR_INT,
    USHR_INT,
    ADD_LONG,
    SUB_LONG,
    MUL_LONG,
    DIV_LONG,
    REM_LONG,
    AND_LONG,
    OR_LONG,
    XOR_LONG,
    SHL_LONG,
    SHR_LONG,
    USHR_LONG,
    ADD_FLOAT,
    SUB_FLOAT,
    MUL_FLOAT,
    DIV_FLOAT,
    REM_FLOAT,
    ADD_DOUBLE,
    SUB_DOUBLE,
    MUL_DOUBLE,
    DIV_DOUBLE,
    REM_DOUBLE,
    ADD_INT_2ADDR,
    SUB_INT_2ADDR,
    MUL_INT_2ADDR,
    DIV_INT_2ADDR,
    REM_INT_2ADDR,
    AND_INT_2ADDR,
    OR_INT_2ADDR,
    XOR_INT_2ADDR,
    SHL_INT_2ADDR,
    SHR_INT_2ADDR,
    USHR_INT_2ADDR,
    ADD_LONG_2ADDR,
    SUB_LONG_2ADDR,
    MUL_LONG_2ADDR,
    DIV_LONG_2ADDR,
    REM_LONG_2ADDR,
    AND_LONG_2ADDR,
    OR_LONG_2ADDR,
    XOR_LONG_2ADDR,
    SHL_LONG_2ADDR,
    SHR_LONG_2ADDR,
    USHR_LONG_2ADDR,
    ADD_FLOAT_2ADDR,
    SUB_FLOAT_2ADDR,
    MUL_FLOAT_2ADDR,
    DIV_FLOAT_2ADDR,
    REM_FLOAT_2ADDR,
    ADD_DOUBLE_2ADDR,
    SUB_DOUBLE_2ADDR,
    MUL_DOUBLE_2ADDR,
    DIV_DOUBLE_2ADDR,
    REM_DOUBLE_2ADDR,
    ADD_INT_LIT16,
    RSUB_INT,
    MUL_INT_LIT16,
    DIV_INT_LIT16,
    REM_INT_LIT16,
    AND_INT_LIT16,
    OR_INT_LIT16,
    XOR_INT_LIT16,
    ADD_INT_LIT8,
    RSUB_INT_LIT8,
    MUL_INT_LIT8,
    DIV_INT_LIT8,
    REM_INT_LIT8,
    AND_INT_LIT8,
    OR_INT_LIT8,
    XOR_INT_LIT8,
    SHL_INT_LIT8,
    SHR_INT_LIT8,
    USHR_INT_LIT8,
    INVOKE_POLYMORPHIC,
    INVOKE_POLYMORPHIC_RANGE,
    INVOKE_CUSTOM,
    INVOKE_CUSTOM_RANGE,
    CONST_METHOD_HANDLE,
    CONST_METHOD_TYPE,
    PACKED_SWITCH_PAYLOAD,
    SPARSE_SWITCH_PAYLOAD,
    FILL_ARRAY_DATA_PAYLOAD,
}

impl OpCode {
    /// Converts an `u8` into an `OpCode`
    pub fn parse(value: u8) -> Option<Self> {
        match value {
            0x00 => Some(OpCode::NOP),                    // Instruction 10x
            0x01 => Some(OpCode::MOVE),                   // Instruction 12x
            0x02 => Some(OpCode::MOVE_FROM16),            // Instruction 22x
            0x03 => Some(OpCode::MOVE_16),                // Instruction 32x
            0x04 => Some(OpCode::MOVE_WIDE),              // Instruction 12x
            0x05 => Some(OpCode::MOVE_WIDE_FROM16),       // Instruction 22x
            0x06 => Some(OpCode::MOVE_WIDE_16),           // Instruction 32x
            0x07 => Some(OpCode::MOVE_OBJECT),            // Instruction 12x
            0x08 => Some(OpCode::MOVE_OBJECT_FROM16),     // Instruction 22x
            0x09 => Some(OpCode::MOVE_OBJECT_16),         // Instruction 32x
            0x0a => Some(OpCode::MOVE_RESULT),            // Instruction 11x
            0x0b => Some(OpCode::MOVE_RESULT_WIDE),       // Instruction 11x
            0x0c => Some(OpCode::MOVE_RESULT_OBJECT),     // Instruction 11x
            0x0d => Some(OpCode::MOVE_EXCEPTION),         // Instruction 11x
            0x0e => Some(OpCode::RETURN_VOID),            // Instruction 10x
            0x0f => Some(OpCode::RETURN),                 // Instruction 11x
            0x10 => Some(OpCode::RETURN_WIDE),            // Instruction 11x
            0x11 => Some(OpCode::RETURN_OBJECT),          // Instruction 11x
            0x12 => Some(OpCode::CONST_4),                // Instruction 11n
            0x13 => Some(OpCode::CONST_16),               // Instruction 21s
            0x14 => Some(OpCode::CONST),                  // Instruction 31i
            0x15 => Some(OpCode::CONST_HIGH16),           // Instruction 21h
            0x16 => Some(OpCode::CONST_WIDE_16),          // Instruction 21s
            0x17 => Some(OpCode::CONST_WIDE_32),          // Instruction 31i
            0x18 => Some(OpCode::CONST_WIDE),             // Instruction 51l
            0x19 => Some(OpCode::CONST_WIDE_HIGH16),      // Instruction 21h
            0x1a => Some(OpCode::CONST_STRING),           // Instruction 21c
            0x1b => Some(OpCode::CONST_STRING_JUMBO),     // Instruction 31c
            0x1c => Some(OpCode::CONST_CLASS),            // Instruction 21c
            0x1d => Some(OpCode::MONITOR_ENTER),          // Instruction 11x
            0x1e => Some(OpCode::MONITOR_EXIT),           // Instruction 11x
            0x1f => Some(OpCode::CHECK_CAST),             // Instruction 21c
            0x20 => Some(OpCode::INSTANCE_OF),            // Instruction 22c
            0x21 => Some(OpCode::ARRAY_LENGTH),           // Instruction 12x
            0x22 => Some(OpCode::NEW_INSTANCE),           // Instruction 21c
            0x23 => Some(OpCode::NEW_ARRAY),              // Instruction 22c
            0x24 => Some(OpCode::FILLED_NEW_ARRAY),       // Instruction 35c
            0x25 => Some(OpCode::FILLED_NEW_ARRAY_RANGE), // Instruction 3rc
            0x26 => Some(OpCode::FILL_ARRAY_DATA),        // Instruction 31t
            0x27 => Some(OpCode::THROW),                  // Instruction 11x
            0x28 => Some(OpCode::GOTO),                   // Instruction 10t
            0x29 => Some(OpCode::GOTO_16),                // Instruction 20t
            0x2a => Some(OpCode::GOTO_32),                // Instruction 30t
            0x2b => Some(OpCode::PACKED_SWITCH),          // Instruction 31t
            0x2c => Some(OpCode::SPARSE_SWITCH),          // Instruction 31t
            0x2d => Some(OpCode::CMPL_FLOAT),             // Instruction 23x
            0x2e => Some(OpCode::CMPG_FLOAT),             // Instruction 23x
            0x2f => Some(OpCode::CMPL_DOUBLE),            // Instruction 23x
            0x30 => Some(OpCode::CMPG_DOUBLE),            // Instruction 23x
            0x31 => Some(OpCode::CMP_LONG),               // Instruction 23x
            0x32 => Some(OpCode::IF_EQ),                  // Instruction 22t
            0x33 => Some(OpCode::IF_NE),                  // Instruction 22t
            0x34 => Some(OpCode::IF_LT),                  // Instruction 22t
            0x35 => Some(OpCode::IF_GE),                  // Instruction 22t
            0x36 => Some(OpCode::IF_GT),                  // Instruction 22t
            0x37 => Some(OpCode::IF_LE),                  // Instruction 22t
            0x38 => Some(OpCode::IF_EQZ),                 // Instruction 21t
            0x39 => Some(OpCode::IF_NEZ),                 // Instruction 21t
            0x3a => Some(OpCode::IF_LTZ),                 // Instruction 21t
            0x3b => Some(OpCode::IF_GEZ),                 // Instruction 21t
            0x3c => Some(OpCode::IF_GTZ),                 // Instruction 21t
            0x3d => Some(OpCode::IF_LEZ),                 // Instruction 21t

            // Unused
            0x3e..=0x43 => {
                warn!("use of unused opcode {}", value);
                None
            }

            0x44 => Some(OpCode::AGET),             // Instruction 23x
            0x45 => Some(OpCode::AGET_WIDE),        // Instruction 23x
            0x46 => Some(OpCode::AGET_OBJECT),      // Instruction 23x
            0x47 => Some(OpCode::AGET_BOOLEAN),     // Instruction 23x
            0x48 => Some(OpCode::AGET_BYTE),        // Instruction 23x
            0x49 => Some(OpCode::AGET_CHAR),        // Instruction 23x
            0x4a => Some(OpCode::AGET_SHORT),       // Instruction 23x
            0x4b => Some(OpCode::APUT),             // Instruction 23x
            0x4c => Some(OpCode::APUT_WIDE),        // Instruction 23x
            0x4d => Some(OpCode::APUT_OBJECT),      // Instruction 23x
            0x4e => Some(OpCode::APUT_BOOLEAN),     // Instruction 23x
            0x4f => Some(OpCode::APUT_BYTE),        // Instruction 23x
            0x50 => Some(OpCode::APUT_CHAR),        // Instruction 23x
            0x51 => Some(OpCode::APUT_SHORT),       // Instruction 23x
            0x52 => Some(OpCode::IGET),             // Instruction 22c
            0x53 => Some(OpCode::IGET_WIDE),        // Instruction 22c
            0x54 => Some(OpCode::IGET_OBJECT),      // Instruction 22c
            0x55 => Some(OpCode::IGET_BOOLEAN),     // Instruction 22c
            0x56 => Some(OpCode::IGET_BYTE),        // Instruction 22c
            0x57 => Some(OpCode::IGET_CHAR),        // Instruction 22c
            0x58 => Some(OpCode::IGET_SHORT),       // Instruction 22c
            0x59 => Some(OpCode::IPUT),             // Instruction 22c
            0x5a => Some(OpCode::IPUT_WIDE),        // Instruction 22c
            0x5b => Some(OpCode::IPUT_OBJECT),      // Instruction 22c
            0x5c => Some(OpCode::IPUT_BOOLEAN),     // Instruction 22c
            0x5d => Some(OpCode::IPUT_BYTE),        // Instruction 22c
            0x5e => Some(OpCode::IPUT_CHAR),        // Instruction 22c
            0x5f => Some(OpCode::IPUT_SHORT),       // Instruction 22c
            0x60 => Some(OpCode::SGET),             // Instruction 21c
            0x61 => Some(OpCode::SGET_WIDE),        // Instruction 21c
            0x62 => Some(OpCode::SGET_OBJECT),      // Instruction 21c
            0x63 => Some(OpCode::SGET_BOOLEAN),     // Instruction 21c
            0x64 => Some(OpCode::SGET_BYTE),        // Instruction 21c
            0x65 => Some(OpCode::SGET_CHAR),        // Instruction 21c
            0x66 => Some(OpCode::SGET_SHORT),       // Instruction 21c
            0x67 => Some(OpCode::SPUT),             // Instruction 21c
            0x68 => Some(OpCode::SPUT_WIDE),        // Instruction 21c
            0x69 => Some(OpCode::SPUT_OBJECT),      // Instruction 21c
            0x6a => Some(OpCode::SPUT_BOOLEAN),     // Instruction 21c
            0x6b => Some(OpCode::SPUT_BYTE),        // Instruction 21c
            0x6c => Some(OpCode::SPUT_CHAR),        // Instruction 21c
            0x6d => Some(OpCode::SPUT_SHORT),       // Instruction 21c
            0x6e => Some(OpCode::INVOKE_VIRTUAL),   // Instruction 35c
            0x6f => Some(OpCode::INVOKE_SUPER),     // Instruction 35c
            0x70 => Some(OpCode::INVOKE_DIRECT),    // Instruction 35c
            0x71 => Some(OpCode::INVOKE_STATIC),    // Instruction 35c
            0x72 => Some(OpCode::INVOKE_INTERFACE), // Instruction 35c

            // Unused
            0x73 => {
                warn!("use of unused opcode {}", value);
                None
            }

            0x74 => Some(OpCode::INVOKE_VIRTUAL_RANGE), // Instruction 3rc
            0x75 => Some(OpCode::INVOKE_SUPER_RANGE),   // Instruction 3rc
            0x76 => Some(OpCode::INVOKE_DIRECT_RANGE),  // Instruction 3rc
            0x77 => Some(OpCode::INVOKE_STATIC_RANGE),  // Instruction 3rc
            0x78 => Some(OpCode::INVOKE_INTERFACE_RANGE), // Instruction 3rc

            // Unused
            0x79 | 0x7a => {
                warn!("use of unused opcode {}", value);
                None
            }

            0x7b => Some(OpCode::NEG_INT),          // Instruction 12x
            0x7c => Some(OpCode::NOT_INT),          // Instruction 12x
            0x7d => Some(OpCode::NEG_LONG),         // Instruction 12x
            0x7e => Some(OpCode::NOT_LONG),         // Instruction 12x
            0x7f => Some(OpCode::NEG_FLOAT),        // Instruction 12x
            0x80 => Some(OpCode::NEG_DOUBLE),       // Instruction 12x
            0x81 => Some(OpCode::INT_TO_LONG),      // Instruction 12x
            0x82 => Some(OpCode::INT_TO_FLOAT),     // Instruction 12x
            0x83 => Some(OpCode::INT_TO_DOUBLE),    // Instruction 12x
            0x84 => Some(OpCode::LONG_TO_INT),      // Instruction 12x
            0x85 => Some(OpCode::LONG_TO_FLOAT),    // Instruction 12x
            0x86 => Some(OpCode::LONG_TO_DOUBLE),   // Instruction 12x
            0x87 => Some(OpCode::FLOAT_TO_INT),     // Instruction 12x
            0x88 => Some(OpCode::FLOAT_TO_LONG),    // Instruction 12x
            0x89 => Some(OpCode::FLOAT_TO_DOUBLE),  // Instruction 12x
            0x8a => Some(OpCode::DOUBLE_TO_INT),    // Instruction 12x
            0x8b => Some(OpCode::DOUBLE_TO_LONG),   // Instruction 12x
            0x8c => Some(OpCode::DOUBLE_TO_FLOAT),  // Instruction 12x
            0x8d => Some(OpCode::INT_TO_BYTE),      // Instruction 12x
            0x8e => Some(OpCode::INT_TO_CHAR),      // Instruction 12x
            0x8f => Some(OpCode::INT_TO_SHORT),     // Instruction 12x
            0x90 => Some(OpCode::ADD_INT),          // Instruction 23x
            0x91 => Some(OpCode::SUB_INT),          // Instruction 23x
            0x92 => Some(OpCode::MUL_INT),          // Instruction 23x
            0x93 => Some(OpCode::DIV_INT),          // Instruction 23x
            0x94 => Some(OpCode::REM_INT),          // Instruction 23x
            0x95 => Some(OpCode::AND_INT),          // Instruction 23x
            0x96 => Some(OpCode::OR_INT),           // Instruction 23x
            0x97 => Some(OpCode::XOR_INT),          // Instruction 23x
            0x98 => Some(OpCode::SHL_INT),          // Instruction 23x
            0x99 => Some(OpCode::SHR_INT),          // Instruction 23x
            0x9a => Some(OpCode::USHR_INT),         // Instruction 23x
            0x9b => Some(OpCode::ADD_LONG),         // Instruction 23x
            0x9c => Some(OpCode::SUB_LONG),         // Instruction 23x
            0x9d => Some(OpCode::MUL_LONG),         // Instruction 23x
            0x9e => Some(OpCode::DIV_LONG),         // Instruction 23x
            0x9f => Some(OpCode::REM_LONG),         // Instruction 23x
            0xa0 => Some(OpCode::AND_LONG),         // Instruction 23x
            0xa1 => Some(OpCode::OR_LONG),          // Instruction 23x
            0xa2 => Some(OpCode::XOR_LONG),         // Instruction 23x
            0xa3 => Some(OpCode::SHL_LONG),         // Instruction 23x
            0xa4 => Some(OpCode::SHR_LONG),         // Instruction 23x
            0xa5 => Some(OpCode::USHR_LONG),        // Instruction 23x
            0xa6 => Some(OpCode::ADD_FLOAT),        // Instruction 23x
            0xa7 => Some(OpCode::SUB_FLOAT),        // Instruction 23x
            0xa8 => Some(OpCode::MUL_FLOAT),        // Instruction 23x
            0xa9 => Some(OpCode::DIV_FLOAT),        // Instruction 23x
            0xaa => Some(OpCode::REM_FLOAT),        // Instruction 23x
            0xab => Some(OpCode::ADD_DOUBLE),       // Instruction 23x
            0xac => Some(OpCode::SUB_DOUBLE),       // Instruction 23x
            0xad => Some(OpCode::MUL_DOUBLE),       // Instruction 23x
            0xae => Some(OpCode::DIV_DOUBLE),       // Instruction 23x
            0xaf => Some(OpCode::REM_DOUBLE),       // Instruction 23x
            0xb0 => Some(OpCode::ADD_INT_2ADDR),    // Instruction 12x
            0xb1 => Some(OpCode::SUB_INT_2ADDR),    // Instruction 12x
            0xb2 => Some(OpCode::MUL_INT_2ADDR),    // Instruction 12x
            0xb3 => Some(OpCode::DIV_INT_2ADDR),    // Instruction 12x
            0xb4 => Some(OpCode::REM_INT_2ADDR),    // Instruction 12x
            0xb5 => Some(OpCode::AND_INT_2ADDR),    // Instruction 12x
            0xb6 => Some(OpCode::OR_INT_2ADDR),     // Instruction 12x
            0xb7 => Some(OpCode::XOR_INT_2ADDR),    // Instruction 12x
            0xb8 => Some(OpCode::SHL_INT_2ADDR),    // Instruction 12x
            0xb9 => Some(OpCode::SHR_INT_2ADDR),    // Instruction 12x
            0xba => Some(OpCode::USHR_INT_2ADDR),   // Instruction 12x
            0xbb => Some(OpCode::ADD_LONG_2ADDR),   // Instruction 12x
            0xbc => Some(OpCode::SUB_LONG_2ADDR),   // Instruction 12x
            0xbd => Some(OpCode::MUL_LONG_2ADDR),   // Instruction 12x
            0xbe => Some(OpCode::DIV_LONG_2ADDR),   // Instruction 12x
            0xbf => Some(OpCode::REM_LONG_2ADDR),   // Instruction 12x
            0xc0 => Some(OpCode::AND_LONG_2ADDR),   // Instruction 12x
            0xc1 => Some(OpCode::OR_LONG_2ADDR),    // Instruction 12x
            0xc2 => Some(OpCode::XOR_LONG_2ADDR),   // Instruction 12x
            0xc3 => Some(OpCode::SHL_LONG_2ADDR),   // Instruction 12x
            0xc4 => Some(OpCode::SHR_LONG_2ADDR),   // Instruction 12x
            0xc5 => Some(OpCode::USHR_LONG_2ADDR),  // Instruction 12x
            0xc6 => Some(OpCode::ADD_FLOAT_2ADDR),  // Instruction 12x
            0xc7 => Some(OpCode::SUB_FLOAT_2ADDR),  // Instruction 12x
            0xc8 => Some(OpCode::MUL_FLOAT_2ADDR),  // Instruction 12x
            0xc9 => Some(OpCode::DIV_FLOAT_2ADDR),  // Instruction 12x
            0xca => Some(OpCode::REM_FLOAT_2ADDR),  // Instruction 12x
            0xcb => Some(OpCode::ADD_DOUBLE_2ADDR), // Instruction 12x
            0xcc => Some(OpCode::SUB_DOUBLE_2ADDR), // Instruction 12x
            0xcd => Some(OpCode::MUL_DOUBLE_2ADDR), // Instruction 12x
            0xce => Some(OpCode::DIV_DOUBLE_2ADDR), // Instruction 12x
            0xcf => Some(OpCode::REM_DOUBLE_2ADDR), // Instruction 12x
            0xd0 => Some(OpCode::ADD_INT_LIT16),    // Instruction 22s
            0xd1 => Some(OpCode::RSUB_INT),         // Instruction 22s
            0xd2 => Some(OpCode::MUL_INT_LIT16),    // Instruction 22s
            0xd3 => Some(OpCode::DIV_INT_LIT16),    // Instruction 22s
            0xd4 => Some(OpCode::REM_INT_LIT16),    // Instruction 22s
            0xd5 => Some(OpCode::AND_INT_LIT16),    // Instruction 22s
            0xd6 => Some(OpCode::OR_INT_LIT16),     // Instruction 22s
            0xd7 => Some(OpCode::XOR_INT_LIT16),    // Instruction 22s
            0xd8 => Some(OpCode::ADD_INT_LIT8),     // Instruction 22b
            0xd9 => Some(OpCode::RSUB_INT_LIT8),    // Instruction 22b
            0xda => Some(OpCode::MUL_INT_LIT8),     // Instruction 22b
            0xdb => Some(OpCode::DIV_INT_LIT8),     // Instruction 22b
            0xdc => Some(OpCode::REM_INT_LIT8),     // Instruction 22b
            0xdd => Some(OpCode::AND_INT_LIT8),     // Instruction 22b
            0xde => Some(OpCode::OR_INT_LIT8),      // Instruction 22b
            0xdf => Some(OpCode::XOR_INT_LIT8),     // Instruction 22b
            0xe0 => Some(OpCode::SHL_INT_LIT8),     // Instruction 22b
            0xe1 => Some(OpCode::SHR_INT_LIT8),     // Instruction 22b
            0xe2 => Some(OpCode::USHR_INT_LIT8),    // Instruction 22b

            // Unused
            0xe3..=0xf9 => {
                warn!("use of unused opcode {}", value);
                None
            }

            0xfa => Some(OpCode::INVOKE_POLYMORPHIC), // Instruction 45cc,
            0xfb => Some(OpCode::INVOKE_POLYMORPHIC_RANGE), // Instruction 4rcc,
            0xfc => Some(OpCode::INVOKE_CUSTOM),      // Instruction 35c,
            0xfd => Some(OpCode::INVOKE_CUSTOM_RANGE), // Instruction 3rc,
            0xfe => Some(OpCode::CONST_METHOD_HANDLE), // Instruction 21c,
            0xff => Some(OpCode::CONST_METHOD_TYPE),  // Instruction 21c,
        }
    }
}
