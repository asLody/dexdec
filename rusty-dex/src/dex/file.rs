//! Representation of a DEX file
//!
//! This is the main class of the parser. When creating `DexFile` object, the builder will parse
//! the header and from there decode the contents of the file (strings, methods, etc). Some apps
//! will have multiple DEX files. In this case, the builder will initially create a `DexFile`
//! object per DEX file and then merge them into one. This extra step is needed as the contents of
//! the final `DexFile` object must contain all the contents of the intermediary DEX files but
//! sorted (the actual sorting method depends on the type of content being sorted -- see the
//! classes documentations for details).

use log::info;

use crate::dex::classes::{ClassDecodeLevel, ClassDefItem, DexClasses, EncodedMethod};
use crate::dex::code_item::CodeItem;
use crate::dex::fields::DexFields;
use crate::dex::header::DexHeader;
use crate::dex::methods::DexMethods;
use crate::dex::protos::DexProtos;
use crate::dex::reader::DexReader;
use crate::dex::strings::DexStrings;
use crate::dex::types::DexTypes;
use crate::error::DexError;

/// Representation of a DEX file
#[derive(Debug)]
pub struct DexFile {
    source: Option<DexReader>,
    /// Header of the file
    pub header: DexHeader,
    /// List of strings defined in the DEX file
    pub strings: DexStrings,
    /// List of types defined in the DEX file
    pub types: DexTypes,
    /// List of prototypes defined in the DEX file
    pub protos: DexProtos,
    /// List of class fields defined in the DEX file
    pub fields: DexFields,
    /// List of methods defined in the DEX file
    pub methods: DexMethods,
    /// List of classes defined in the DEX file
    pub classes: DexClasses,
}

impl DexFile {
    pub(crate) fn source_reader(&self) -> Result<DexReader, DexError> {
        self.source
            .as_ref()
            .map(DexReader::fork)
            .ok_or(DexError::NoDataLeftError)
    }

    /// Parse a DEX file from the reader and create a `DexFile` object
    pub fn build(dex_reader: DexReader) -> Result<Self, DexError> {
        Self::build_with_level(dex_reader, ClassDecodeLevel::Bytecode)
    }

    /// Parse the class directory while deferring members, bytecode, and debug streams.
    pub fn build_metadata(dex_reader: DexReader) -> Result<Self, DexError> {
        Self::build_with_level(dex_reader, ClassDecodeLevel::Declaration)
    }

    fn build_with_level(
        mut dex_reader: DexReader,
        level: ClassDecodeLevel,
    ) -> Result<Self, DexError> {
        let source = dex_reader.fork();
        let dex_header = DexHeader::new(&mut dex_reader)?;

        let strings_list = DexStrings::build(
            &mut dex_reader,
            dex_header.string_ids_off,
            dex_header.string_ids_size,
        )?;

        let type_ids_list = DexTypes::build(
            &mut dex_reader,
            dex_header.type_ids_off,
            dex_header.type_ids_size,
            &strings_list,
        )?;

        let proto_ids_list = DexProtos::build(
            &mut dex_reader,
            dex_header.proto_ids_off,
            dex_header.proto_ids_size,
            &type_ids_list,
        )?;

        let field_ids_list = DexFields::build(
            &mut dex_reader,
            dex_header.fields_ids_off,
            dex_header.fields_ids_size,
            &type_ids_list,
            &strings_list,
        )?;

        let method_ids_list = DexMethods::build(
            &mut dex_reader,
            dex_header.method_ids_off,
            dex_header.method_ids_size,
            &type_ids_list,
            &proto_ids_list,
            &strings_list,
        )?;

        let class_defs_list = DexClasses::build_with_level(
            &mut dex_reader,
            dex_header.class_defs_off,
            dex_header.class_defs_size,
            &field_ids_list,
            &type_ids_list,
            &proto_ids_list,
            &strings_list,
            &method_ids_list,
            level,
        )?;

        Ok(DexFile {
            source: Some(source),
            header: dex_header,
            strings: strings_list,
            types: type_ids_list,
            protos: proto_ids_list,
            fields: field_ids_list,
            methods: method_ids_list,
            classes: class_defs_list,
        })
    }

    /// Create a `DexFile` from a collection of `DexReader`.
    ///
    /// This function will create an intermediary `DexFile` object for each reader and then merge
    /// them into the final `DexFile`.
    pub fn merge(readers: Vec<DexReader>) -> Result<Self, DexError> {
        let mut strings_list = Vec::new();
        let mut type_ids_list = Vec::new();
        let mut proto_ids_list = Vec::new();
        let mut field_ids_list = Vec::new();
        let mut method_ids_list = Vec::new();
        let mut class_defs_list = Vec::new();

        info!("start merging DEX files");
        for reader in readers.into_iter() {
            let current_dex_file = DexFile::build(reader)?;

            info!("  merging strings");
            for string in current_dex_file.strings.strings.into_iter() {
                strings_list.push(string);
            }

            info!("  merging types");
            for type_id in current_dex_file.types.items.into_iter() {
                type_ids_list.push(type_id);
            }

            info!("  merging protos");
            for proto_id in current_dex_file.protos.items.into_iter() {
                proto_ids_list.push(proto_id);
            }

            info!("  merging fields");
            for field_id in current_dex_file.fields.items.into_iter() {
                field_ids_list.push(field_id);
            }

            info!("  merging methods");
            for method_id in current_dex_file.methods.items.into_iter() {
                method_ids_list.push(method_id);
            }

            info!("  merging classes");
            for class_def_id in current_dex_file.classes.items.into_iter() {
                class_defs_list.push(class_def_id);
            }
        }

        info!("removing strings duplicates and storing strings");
        strings_list.dedup();
        strings_list.sort();
        info!("removing strings duplicates and storing types");
        type_ids_list.dedup();
        type_ids_list.sort();
        info!("removing strings duplicates and storing protos");
        proto_ids_list.dedup();
        proto_ids_list.sort();
        info!("removing strings duplicates and storing fields");
        field_ids_list.dedup();
        field_ids_list.sort();
        info!("removing strings duplicates and storing methods");
        method_ids_list.dedup();
        method_ids_list.sort();
        // class_defs_list.dedup();
        // class_defs_list.sort();

        info!("done merging");

        let header = DexHeader {
            version: [0x00; 3],
            checksum: 0x0,
            signature: [0x00; 20],
            file_size: 0x00,
            header_size: 0x00,
            endian_tag: 0x00,
            link_size: 0x00,
            link_off: 0x00,
            map_off: 0x00,
            string_ids_size: strings_list.len() as u32,
            string_ids_off: 0x00,
            type_ids_size: type_ids_list.len() as u32,
            type_ids_off: 0x00,
            proto_ids_size: proto_ids_list.len() as u32,
            proto_ids_off: 0x00,
            fields_ids_size: field_ids_list.len() as u32,
            fields_ids_off: 0x00,
            method_ids_size: method_ids_list.len() as u32,
            method_ids_off: 0x00,
            class_defs_size: class_defs_list.len() as u32,
            class_defs_off: 0x00,
            data_size: 0x00,
            data_off: 0x00,
        };

        Ok(DexFile {
            source: None,
            header,
            strings: DexStrings {
                strings: strings_list,
            },
            types: DexTypes {
                items: type_ids_list,
            },
            protos: DexProtos {
                items: proto_ids_list,
            },
            fields: DexFields {
                items: field_ids_list,
            },
            methods: DexMethods {
                items: method_ids_list,
            },
            classes: DexClasses {
                items: class_defs_list,
            },
        })
    }

    pub fn decode_code_item(&self, method: &EncodedMethod) -> Result<Option<CodeItem>, DexError> {
        let Some(offset) = method.code_offset else {
            return Ok(None);
        };
        let source = self.source.as_ref().ok_or(DexError::NoDataLeftError)?;
        let mut reader = source.fork();
        CodeItem::build(&mut reader, offset, &self.types, &self.strings).map(Some)
    }

    /// Decode a class's fields, methods, and member annotations on first use.
    pub fn materialize_class(&mut self, class_index: usize) -> Result<(), DexError> {
        let class = self
            .classes
            .items
            .get(class_index)
            .ok_or(DexError::InvalidClassIdx)?;
        if class.members_loaded() {
            return Ok(());
        }
        let class_index = u32::try_from(class_index).map_err(|_| DexError::InvalidClassIdx)?;
        let offset = class_index
            .checked_mul(32)
            .and_then(|relative| self.header.class_defs_off.checked_add(relative))
            .ok_or(DexError::InvalidClassIdx)?;
        let source = self.source.as_ref().ok_or(DexError::NoDataLeftError)?;
        let mut reader = source.fork();
        let mut decoded = DexClasses::build_with_level(
            &mut reader,
            offset,
            1,
            &self.fields,
            &self.types,
            &self.protos,
            &self.strings,
            &self.methods,
            ClassDecodeLevel::Members,
        )?;
        let class = decoded.items.pop().ok_or(DexError::InvalidClassIdx)?;
        self.classes.items[class_index as usize] = class;
        Ok(())
    }

    /// Returns a vector containing the names of all the classes defined in the DEX file
    pub fn get_classes_names(&self) -> Vec<&String> {
        let mut class_names = Vec::new();

        for class in &self.classes.items {
            class_names.push(class.get_class_name());
        }

        class_names
    }

    /// Get the `ClassDefItem` object for a given class name
    pub fn get_class_def(&self, class_name: &String) -> Option<&ClassDefItem> {
        self.classes.get_class_def(class_name)
    }

    /// Get the method of a given class as a vector of `EncodedMethod` objects
    pub fn get_methods_for_class(&self, class_name: &String) -> Vec<&EncodedMethod> {
        if let Some(class_def) = self.get_class_def(class_name) {
            return class_def.get_methods();
        }

        Vec::new()
    }
}
