//! Representation of method prototypes
//!
//! This module contains the logic to decode method prototypes from a DEX file.

use std::io::{Seek, SeekFrom};

use crate::dex::reader::DexReader;
use crate::dex::types::DexTypes;
use crate::error::DexError;

#[derive(Debug)]
struct PrototypeDescriptor {
    text: String,
}

impl PrototypeDescriptor {
    fn new() -> Self {
        Self {
            text: "(".to_string(),
        }
    }

    fn parameter(&mut self, descriptor: &str) {
        self.text.push_str(descriptor);
    }

    fn finish(mut self, return_type: &str) -> String {
        self.text.push(')');
        self.text.push_str(return_type);
        self.text
    }
}

/// List of decoded prototypes in the DEX files
#[derive(Debug)]
pub struct DexProtos {
    pub items: Vec<String>,
}

impl DexProtos {
    /// Parse the prototypes from the reader
    pub fn build(
        dex_reader: &mut DexReader,
        offset: u32,
        size: u32,
        types_list: &DexTypes,
    ) -> Result<Self, DexError> {
        dex_reader.bytes.seek(SeekFrom::Start(offset.into()))?;

        let mut items = Vec::with_capacity(size as usize);

        for _ in 0..size {
            let _shorty_idx = dex_reader.read_u32()?;
            let return_type_idx = dex_reader.read_u32()?;
            let parameters_off = dex_reader.read_u32()?;

            // Decode the prototype
            let mut descriptor = PrototypeDescriptor::new();
            if parameters_off != 0 {
                // Save current stream position
                let current_pos = dex_reader.bytes.position();

                // Decode the parameters
                dex_reader
                    .bytes
                    .seek(SeekFrom::Start(parameters_off.into()))?;

                let params_size = dex_reader.read_u32()?;
                for _ in 0..params_size {
                    let type_index = dex_reader.read_u16()?;

                    descriptor.parameter(
                        types_list
                            .items
                            .get(type_index as usize)
                            .ok_or(DexError::InvalidTypeIdx)?,
                    );
                }

                // Go back to the previous position
                dex_reader.bytes.seek(SeekFrom::Start(current_pos))?;
            }
            let return_type = types_list
                .items
                .get(return_type_idx as usize)
                .ok_or(DexError::InvalidTypeIdx)?;
            items.push(descriptor.finish(return_type));
        }

        Ok(DexProtos { items })
    }
}

#[cfg(test)]
mod tests {
    use super::PrototypeDescriptor;

    #[test]
    fn descriptor_parameters_are_contiguous() {
        let mut descriptor = PrototypeDescriptor::new();
        descriptor.parameter("Ljava/lang/Class;");
        descriptor.parameter("Ljava/lang/reflect/Field;");

        assert_eq!(
            descriptor.finish("V"),
            "(Ljava/lang/Class;Ljava/lang/reflect/Field;)V"
        );
    }
}
