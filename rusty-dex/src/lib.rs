#![allow(dead_code)]

use error::DexError;

use crate::dex::file::DexFile;
use crate::dex::instructions::Instructions;
use crate::dex::reader::DexReader;

pub mod adler32;
pub mod dex;
pub mod error;
mod mutf8;

/// Parse an APK and create a `DexFile` object from the embedded class(es) files
pub fn parse(filepath: &str) -> Result<DexFile, DexError> {
    let readers = DexReader::build_from_file(filepath)?;
    DexFile::merge(readers)
}

/// Return the list of qualified method names from a `DexFile` object
pub fn get_qualified_method_names(dex: &DexFile) -> Vec<String> {
    let mut methods = Vec::new();

    let class_names = dex.get_classes_names();
    for class in class_names.iter() {
        if let Some(class_def) = dex.classes.get_class_def(class) {
            for method in class_def.get_methods() {
                let name = method.get_method_name();
                methods.push(format!("{class}->{name}"));
            }
        }
    }

    methods
}

/// Get the list of instructions for the given method
pub fn get_bytecode_for_method(
    dex: &DexFile,
    class_name: &String,
    method_name: &String,
) -> Option<Vec<Instructions>> {
    if let Some(class_def) = dex.get_class_def(class_name) {
        if let Some(encoded_method) = class_def.get_encoded_method(method_name) {
            if let Some(code_item) = &encoded_method.code_item {
                return code_item.insns.clone();
            }
        }
    }

    None
}
