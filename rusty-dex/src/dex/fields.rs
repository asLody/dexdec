//! Representation of class fields
//!
//! This module decodes fields from a DEX file and returns them in the correct order. Fields must
//! be ordered by the class they belong to, then their name, and finally their type.
//! Each field can represent a static field initialized in the `<cinit>` pseudo-method or a class
//! field that is initialized when the class is instantiated.

use std::io::{Seek, SeekFrom};

use crate::dex::reader::DexReader;
use crate::dex::strings::DexStrings;
use crate::dex::types::DexTypes;
use crate::error::DexError;

/// Representation of the fields in a DEX file. Only the decoded fields are present in the correct
/// order.
#[derive(Debug)]
pub struct DexFields {
    /// Vector of decoded field names
    pub items: Vec<String>,
}

impl DexFields {
    /// Parse the fields from the DEX file
    ///
    /// This function returns a vector of decoded field names in the correct order
    pub fn build(
        dex_reader: &mut DexReader,
        offset: u32,
        size: u32,
        types_list: &DexTypes,
        strings_list: &DexStrings,
    ) -> Result<Self, DexError> {
        dex_reader.bytes.seek(SeekFrom::Start(offset.into()))?;

        let mut items = Vec::with_capacity(size as usize);

        for _ in 0..size {
            let class_idx = dex_reader.read_u16()?;
            let type_idx = dex_reader.read_u16()?;
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
            decoded.push(':');
            decoded.push_str(
                types_list
                    .items
                    .get(type_idx as usize)
                    .ok_or(DexError::InvalidTypeIdx)?,
            );

            items.push(decoded);
        }

        Ok(DexFields { items })
    }
}
