use std::io::{Seek, SeekFrom};

use crate::dex::file::DexFile;
use crate::dex::reader::DexReader;
use crate::error::DexError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DexMemberKind {
    Field,
    Method,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DexMemberDeclaration<'dex> {
    pub owner: &'dex str,
    pub reference: &'dex str,
    pub kind: DexMemberKind,
    pub has_code: bool,
}

pub trait DexMemberVisitor {
    fn visit(&mut self, declaration: DexMemberDeclaration<'_>);
}

impl<F> DexMemberVisitor for F
where
    F: FnMut(DexMemberDeclaration<'_>),
{
    fn visit(&mut self, declaration: DexMemberDeclaration<'_>) {
        self(declaration);
    }
}

/// Traverses encoded class data without retaining decoded class members.
pub struct DexMemberScanner<'dex> {
    dex: &'dex DexFile,
}

impl<'dex> DexMemberScanner<'dex> {
    pub fn new(dex: &'dex DexFile) -> Self {
        Self { dex }
    }

    pub fn scan(&self, visitor: &mut impl DexMemberVisitor) -> Result<(), DexError> {
        let mut reader = self.dex.source_reader()?;
        for class in &self.dex.classes.items {
            let class_data_offset = class.class_data_offset();
            if class_data_offset == 0 {
                continue;
            }
            reader
                .bytes
                .seek(SeekFrom::Start(class_data_offset.into()))?;
            self.scan_class_data(&mut reader, class.get_class_name(), visitor)?;
        }
        Ok(())
    }

    fn scan_class_data(
        &self,
        reader: &mut DexReader,
        owner: &'dex str,
        visitor: &mut impl DexMemberVisitor,
    ) -> Result<(), DexError> {
        let (static_fields, _) = reader.read_uleb128()?;
        let (instance_fields, _) = reader.read_uleb128()?;
        let (direct_methods, _) = reader.read_uleb128()?;
        let (virtual_methods, _) = reader.read_uleb128()?;

        self.scan_fields(reader, owner, static_fields, visitor)?;
        self.scan_fields(reader, owner, instance_fields, visitor)?;
        self.scan_methods(reader, owner, direct_methods, visitor)?;
        self.scan_methods(reader, owner, virtual_methods, visitor)
    }

    fn scan_fields(
        &self,
        reader: &mut DexReader,
        owner: &'dex str,
        count: u32,
        visitor: &mut impl DexMemberVisitor,
    ) -> Result<(), DexError> {
        let mut field_index = 0u32;
        for _ in 0..count {
            let (index_delta, _) = reader.read_uleb128()?;
            let _ = reader.read_uleb128()?;
            field_index = field_index
                .checked_add(index_delta)
                .ok_or(DexError::InvalidFieldIdx)?;
            let reference = self
                .dex
                .fields
                .items
                .get(field_index as usize)
                .ok_or(DexError::InvalidFieldIdx)?;
            visitor.visit(DexMemberDeclaration {
                owner,
                reference,
                kind: DexMemberKind::Field,
                has_code: false,
            });
        }
        Ok(())
    }

    fn scan_methods(
        &self,
        reader: &mut DexReader,
        owner: &'dex str,
        count: u32,
        visitor: &mut impl DexMemberVisitor,
    ) -> Result<(), DexError> {
        let mut method_index = 0u32;
        for _ in 0..count {
            let (index_delta, _) = reader.read_uleb128()?;
            let _ = reader.read_uleb128()?;
            let (code_offset, _) = reader.read_uleb128()?;
            method_index = method_index
                .checked_add(index_delta)
                .ok_or(DexError::InvalidMethodIdx)?;
            let reference = self
                .dex
                .methods
                .items
                .get(method_index as usize)
                .ok_or(DexError::InvalidMethodIdx)?;
            visitor.visit(DexMemberDeclaration {
                owner,
                reference,
                kind: DexMemberKind::Method,
                has_code: code_offset != 0,
            });
        }
        Ok(())
    }
}
