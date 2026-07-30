//! Allocation-light traversal of symbolic references in DEX code items.

use std::io::{Seek, SeekFrom};

use crate::dex::file::DexFile;
use crate::dex::instructions::{self, Instructions};
use crate::dex::opcodes::OpCode;
use crate::dex::reader::DexReader;
use crate::error::DexError;

/// The DEX table addressed by a bytecode reference operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DexReferenceKind {
    Type,
    Field,
    Method,
}

/// One symbolic operand and the method containing it.
#[derive(Debug, Clone, Copy)]
pub struct DexCodeReference<'a> {
    pub kind: DexReferenceKind,
    pub target: &'a str,
    pub caller: &'a str,
    pub offset: u32,
}

/// Streaming consumer used to avoid retaining an archive-wide reference list.
pub trait DexReferenceVisitor {
    fn visit(&mut self, reference: DexCodeReference<'_>);
}

impl<F> DexReferenceVisitor for F
where
    F: FnMut(DexCodeReference<'_>),
{
    fn visit(&mut self, reference: DexCodeReference<'_>) {
        self(reference);
    }
}

/// Traverses encoded class data and code items without materializing classes,
/// debug streams, exception tables, or decompiler IR.
pub struct DexReferenceScanner<'dex> {
    dex: &'dex DexFile,
}

impl<'dex> DexReferenceScanner<'dex> {
    pub fn new(dex: &'dex DexFile) -> Self {
        Self { dex }
    }

    pub fn scan(&self, visitor: &mut impl DexReferenceVisitor) -> Result<(), DexError> {
        let mut reader = self.dex.source_reader()?;
        for class in &self.dex.classes.items {
            let class_data_offset = class.class_data_offset();
            if class_data_offset == 0 {
                continue;
            }
            reader
                .bytes
                .seek(SeekFrom::Start(class_data_offset.into()))?;
            self.scan_class_data(&mut reader, visitor)?;
        }
        Ok(())
    }

    fn scan_class_data(
        &self,
        reader: &mut DexReader,
        visitor: &mut impl DexReferenceVisitor,
    ) -> Result<(), DexError> {
        let (static_fields, _) = reader.read_uleb128()?;
        let (instance_fields, _) = reader.read_uleb128()?;
        let (direct_methods, _) = reader.read_uleb128()?;
        let (virtual_methods, _) = reader.read_uleb128()?;

        Self::skip_fields(reader, static_fields)?;
        Self::skip_fields(reader, instance_fields)?;
        self.scan_methods(reader, direct_methods, visitor)?;
        self.scan_methods(reader, virtual_methods, visitor)
    }

    fn skip_fields(reader: &mut DexReader, count: u32) -> Result<(), DexError> {
        for _ in 0..count {
            let _ = reader.read_uleb128()?;
            let _ = reader.read_uleb128()?;
        }
        Ok(())
    }

    fn scan_methods(
        &self,
        reader: &mut DexReader,
        count: u32,
        visitor: &mut impl DexReferenceVisitor,
    ) -> Result<(), DexError> {
        let mut method_index = 0u32;
        for _ in 0..count {
            let (index_delta, _) = reader.read_uleb128()?;
            let _ = reader.read_uleb128()?;
            let (code_offset, _) = reader.read_uleb128()?;
            method_index = method_index
                .checked_add(index_delta)
                .ok_or(DexError::InvalidMethodIdx)?;
            if code_offset == 0 {
                continue;
            }
            let caller = self
                .dex
                .methods
                .items
                .get(method_index as usize)
                .ok_or(DexError::InvalidMethodIdx)?;
            let class_data_position = reader.bytes.position();
            self.scan_code_item(reader, code_offset, caller, visitor)?;
            reader.bytes.seek(SeekFrom::Start(class_data_position))?;
        }
        Ok(())
    }

    fn scan_code_item(
        &self,
        reader: &mut DexReader,
        code_offset: u32,
        caller: &str,
        visitor: &mut impl DexReferenceVisitor,
    ) -> Result<(), DexError> {
        reader.bytes.seek(SeekFrom::Start(code_offset.into()))?;
        for _ in 0..4 {
            let _ = reader.read_u16()?;
        }
        let _ = reader.read_u32()?;
        let insns_size = reader.read_u32()?;

        let mut offset = 0u32;
        let mut decoded = Vec::<Instructions>::with_capacity(1);
        while offset < insns_size {
            decoded.clear();
            let length = instructions::parse_instruction(reader, &mut decoded)?;
            let length = u32::try_from(length).map_err(|_| DexError::InvalidOpCode)?;
            if length == 0 || offset.saturating_add(length) > insns_size {
                return Err(DexError::InvalidOpCode);
            }
            let instruction = decoded.pop().ok_or(DexError::InvalidOpCode)?;
            if let Some((kind, index)) = Self::reference_operand(&instruction) {
                let target = match kind {
                    DexReferenceKind::Type => self.dex.types.items.get(index),
                    DexReferenceKind::Field => self.dex.fields.items.get(index),
                    DexReferenceKind::Method => self.dex.methods.items.get(index),
                }
                .ok_or(match kind {
                    DexReferenceKind::Type => DexError::InvalidTypeIdx,
                    DexReferenceKind::Field => DexError::InvalidFieldIdx,
                    DexReferenceKind::Method => DexError::InvalidMethodIdx,
                })?;
                visitor.visit(DexCodeReference {
                    kind,
                    target,
                    caller,
                    offset,
                });
            }
            offset += length;
        }
        Ok(())
    }

    fn reference_operand(instruction: &Instructions) -> Option<(DexReferenceKind, usize)> {
        let kind = Self::reference_kind(instruction.opcode())?;
        Some((kind, *instruction.bytes().get(1)? as usize))
    }

    fn reference_kind(opcode: OpCode) -> Option<DexReferenceKind> {
        match opcode {
            OpCode::CONST_CLASS
            | OpCode::CHECK_CAST
            | OpCode::INSTANCE_OF
            | OpCode::NEW_INSTANCE
            | OpCode::NEW_ARRAY
            | OpCode::FILLED_NEW_ARRAY
            | OpCode::FILLED_NEW_ARRAY_RANGE => Some(DexReferenceKind::Type),

            OpCode::IGET
            | OpCode::IGET_WIDE
            | OpCode::IGET_OBJECT
            | OpCode::IGET_BOOLEAN
            | OpCode::IGET_BYTE
            | OpCode::IGET_CHAR
            | OpCode::IGET_SHORT
            | OpCode::IPUT
            | OpCode::IPUT_WIDE
            | OpCode::IPUT_OBJECT
            | OpCode::IPUT_BOOLEAN
            | OpCode::IPUT_BYTE
            | OpCode::IPUT_CHAR
            | OpCode::IPUT_SHORT
            | OpCode::SGET
            | OpCode::SGET_WIDE
            | OpCode::SGET_OBJECT
            | OpCode::SGET_BOOLEAN
            | OpCode::SGET_BYTE
            | OpCode::SGET_CHAR
            | OpCode::SGET_SHORT
            | OpCode::SPUT
            | OpCode::SPUT_WIDE
            | OpCode::SPUT_OBJECT
            | OpCode::SPUT_BOOLEAN
            | OpCode::SPUT_BYTE
            | OpCode::SPUT_CHAR
            | OpCode::SPUT_SHORT => Some(DexReferenceKind::Field),

            OpCode::INVOKE_VIRTUAL
            | OpCode::INVOKE_SUPER
            | OpCode::INVOKE_DIRECT
            | OpCode::INVOKE_STATIC
            | OpCode::INVOKE_INTERFACE
            | OpCode::INVOKE_VIRTUAL_RANGE
            | OpCode::INVOKE_SUPER_RANGE
            | OpCode::INVOKE_DIRECT_RANGE
            | OpCode::INVOKE_STATIC_RANGE
            | OpCode::INVOKE_INTERFACE_RANGE
            | OpCode::INVOKE_POLYMORPHIC
            | OpCode::INVOKE_POLYMORPHIC_RANGE => Some(DexReferenceKind::Method),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_reference_opcodes() {
        assert_eq!(
            DexReferenceScanner::reference_kind(OpCode::NEW_INSTANCE),
            Some(DexReferenceKind::Type)
        );
        assert_eq!(
            DexReferenceScanner::reference_kind(OpCode::IGET),
            Some(DexReferenceKind::Field)
        );
        assert_eq!(
            DexReferenceScanner::reference_kind(OpCode::INVOKE_STATIC),
            Some(DexReferenceKind::Method)
        );
        assert_eq!(
            DexReferenceScanner::reference_kind(OpCode::RETURN_VOID),
            None
        );
    }
}
