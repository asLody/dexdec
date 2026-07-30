//! Methods identifiers
//!
//! This module deals with method identifiers. Each DEX file contains a list
//! of identifiers for all methods reffered to in the code. The list is sorted
//! by the defining type (by `type_id` index), method name (by `string_id`
//! index), and method prototype (by `proto_id` index), and cannot contain
//! duplicates.

use std::io::{Seek, SeekFrom};

use crate::dex::protos::DexProtos;
use crate::dex::reader::DexReader;
use crate::dex::strings::DexStrings;
use crate::dex::types::DexTypes;
use crate::error::DexError;

/// Sorted list of method IDs
#[derive(Debug)]
pub struct DexMethods {
    pub items: Vec<String>,
}

impl DexMethods {
    /// Build the list of method identifiers from a file
    pub fn build(
        dex_reader: &mut DexReader,
        offset: u32,
        size: u32,
        types_list: &DexTypes,
        protos_list: &DexProtos,
        strings_list: &DexStrings,
    ) -> Result<Self, DexError> {
        dex_reader.bytes.seek(SeekFrom::Start(offset.into()))?;

        let mut items = Vec::with_capacity(size as usize);

        for _ in 0..size {
            let class_idx = dex_reader.read_u16()?;
            let proto_idx = dex_reader.read_u16()?;
            let name_idx = dex_reader.read_u32()?;

            let mut decoded = String::new();
            decoded.push_str(
                types_list
                    .items
                    .get(class_idx as usize)
                    .ok_or(DexError::InvalidTypeIdx)?,
            );
            decoded.push_str("->");
            decoded.push_str(
                strings_list
                    .strings
                    .get(name_idx as usize)
                    .ok_or(DexError::InvalidStringIdx)?
                    .as_str(),
            );
            decoded.push_str(
                protos_list
                    .items
                    .get(proto_idx as usize)
                    .ok_or(DexError::InvalidTypeIdx)?,
            );

            items.push(decoded);
        }

        Ok(DexMethods { items })
    }
}
