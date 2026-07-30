//! Representation of a class and encoded methods

use lazy_static::lazy_static;
use log::{debug, warn};
use regex::Regex;
use std::collections::HashMap;
use std::io::{Seek, SeekFrom};

use crate::dex::access_flags::{AccessFlag, AccessFlagType};
use crate::dex::code_item::CodeItem;
use crate::dex::encoded_value::{
    AnnotationElement, EncodedAnnotation, EncodedValue, read_encoded_annotation, read_encoded_array,
};
use crate::dex::reader::DexReader;

use crate::dex::fields::DexFields;
use crate::dex::methods::DexMethods;
use crate::dex::protos::DexProtos;
use crate::dex::strings::DexStrings;
use crate::dex::types::DexTypes;
use crate::error::DexError;

/// Constant to represent the absence of index
const NO_INDEX: u32 = 0xffffffff;

lazy_static! {
    /// Regex for method prototypes
    static ref METHOD_REGEX: Regex = Regex::new(r"(?x)
        (?P<class>L[a-zA-Z/$0-9]+;)
        (->)
        (?P<method><?[a-zA-Z0-9]+>?[\$\d+]*)
        (?P<args>\(.*\).*)
    ").unwrap();
}

/// Class definition item
///
/// This struct contains all the metadata of a class. The optional `class_data` item then contains
/// the list of fields and methods (with bytecode) in this class. Note that it is possible that a
/// class contains not fields or methods, in which case `class_data` will be `None`.
#[derive(Debug)]
pub struct ClassDefItem {
    class_str: String,
    access_flags_raw: u32,
    access_flags: Vec<AccessFlag>,
    superclass_str: Option<String>,
    interfaces_off: u32,
    /// Resolved interface type descriptors (`Ljava/io/Serializable;`, etc.).
    /// Populated from the `type_list` at `interfaces_off`.
    interface_descriptors: Vec<String>,
    source_file_str: Option<String>,
    annotations_off: u32,
    class_data_off: u32,
    static_value_off: u32,
    static_values: Vec<EncodedValue>,
    class_data: Option<ClassDataItem>,
    members_loaded: bool,
    /// JVM generic class signature recovered from the
    /// `Ldalvik/annotation/Signature;` class-level annotation, when present.
    pub signature: Option<String>,
    /// Inner / enclosing-class metadata recovered from Dalvik system
    /// annotations when present.
    pub inner_class: Option<InnerClassAnnotation>,
    pub member_classes: Vec<String>,
    pub enclosing_class: Option<String>,
    pub enclosing_method: Option<String>,
    pub annotations: Vec<DexAnnotation>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InnerClassAnnotation {
    pub name: Option<String>,
    pub access_flags: u32,
}

/// Representation of an encoded field
#[derive(Debug)]
pub struct EncodedField {
    field: String,
    access_flags_raw: u32,
    access_flags: Vec<AccessFlag>,
    initial_value: Option<EncodedValue>,
    /// JVM generic field signature recovered from the
    /// `Ldalvik/annotation/Signature;` field annotation, when present.
    pub signature: Option<String>,
    pub annotations: Vec<DexAnnotation>,
}

/// Representation of an encoded method
#[derive(Debug)]
pub struct EncodedMethod {
    pub method_idx: u32,
    pub proto: String,
    pub access_flags_raw: u32,
    pub access_flags: Vec<AccessFlag>,
    pub code_offset: Option<u32>,
    pub code_item: Option<CodeItem>,
    pub throws: Vec<String>,
    /// JVM generic method signature recovered from the
    /// `Ldalvik/annotation/Signature;` method annotation, when present.
    pub signature: Option<String>,
    pub annotations: Vec<DexAnnotation>,
    pub parameter_annotations: Vec<Vec<DexAnnotation>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DexAnnotation {
    pub visibility: AnnotationVisibility,
    pub annotation: EncodedAnnotation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationVisibility {
    Build,
    Runtime,
    System,
    Unknown(u8),
}

impl AnnotationVisibility {
    fn from_raw(value: u8) -> Self {
        match value {
            0 => Self::Build,
            1 => Self::Runtime,
            2 => Self::System,
            value => Self::Unknown(value),
        }
    }
}

/// Class data item which contains all fields and methods of a class
#[derive(Debug)]
pub struct ClassDataItem {
    static_fields: Vec<EncodedField>,
    instance_fields: Vec<EncodedField>,
    direct_methods: Vec<EncodedMethod>,
    virtual_methods: Vec<EncodedMethod>,
}

/// List of all classes of a DEX file
#[derive(Debug)]
pub struct DexClasses {
    pub items: Vec<ClassDefItem>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassDecodeLevel {
    Bytecode,
    Members,
    Declaration,
}

impl DexClasses {
    /// Parse the DEX file to extract the classes and their content
    pub fn build(
        dex_reader: &mut DexReader,
        offset: u32,
        size: u32,
        fields_list: &DexFields,
        types_list: &DexTypes,
        protos_list: &DexProtos,
        strings_list: &DexStrings,
        methods_list: &DexMethods,
    ) -> Result<Self, DexError> {
        Self::build_with_level(
            dex_reader,
            offset,
            size,
            fields_list,
            types_list,
            protos_list,
            strings_list,
            methods_list,
            ClassDecodeLevel::Bytecode,
        )
    }

    pub fn build_with_level(
        dex_reader: &mut DexReader,
        offset: u32,
        size: u32,
        fields_list: &DexFields,
        types_list: &DexTypes,
        protos_list: &DexProtos,
        strings_list: &DexStrings,
        methods_list: &DexMethods,
        level: ClassDecodeLevel,
    ) -> Result<Self, DexError> {
        dex_reader.bytes.seek(SeekFrom::Start(offset.into()))?;

        let mut methods = Vec::new();

        for _ in 0..size {
            let class_idx = dex_reader.read_u32()?;
            let access_flags = dex_reader.read_u32()?;
            let access_flags_decoded = AccessFlag::parse(access_flags, AccessFlagType::Class);

            let superclass_idx = dex_reader.read_u32()?;
            let interfaces_off = dex_reader.read_u32()?;
            let source_file_idx = dex_reader.read_u32()?;
            let annotations_off = dex_reader.read_u32()?;
            let class_data_off = dex_reader.read_u32()?;
            let static_value_off = dex_reader.read_u32()?;

            // Convert indexs into human-readable strings
            let class_str = types_list
                .items
                .get(class_idx as usize)
                .ok_or(DexError::InvalidTypeIdx)?;

            // Read the interface type list. The `type_list` at
            // `interfaces_off` is `count: u32` followed by `count` ×
            // `type_idx: u16`.
            let interface_descriptors =
                read_interface_list(dex_reader, interfaces_off, types_list)?;

            let mut superclass_str = None;
            if superclass_idx != NO_INDEX {
                superclass_str = Some(
                    types_list
                        .items
                        .get(superclass_idx as usize)
                        .ok_or(DexError::InvalidTypeIdx)?,
                );
            }

            let mut source_file_str = None;
            if source_file_idx != NO_INDEX {
                source_file_str = Some(
                    strings_list
                        .strings
                        .get(source_file_idx as usize)
                        .ok_or(DexError::InvalidStringIdx)?,
                );
            }

            let static_values = if level != ClassDecodeLevel::Declaration && static_value_off != 0 {
                read_encoded_array(
                    dex_reader,
                    static_value_off,
                    strings_list,
                    types_list,
                    Some(protos_list),
                    Some(fields_list),
                    Some(methods_list),
                )?
            } else {
                Vec::new()
            };
            let annotations = if annotations_off != 0 {
                if level == ClassDecodeLevel::Declaration {
                    read_class_annotations_directory(
                        dex_reader,
                        annotations_off,
                        strings_list,
                        types_list,
                        protos_list,
                        fields_list,
                        methods_list,
                    )?
                } else {
                    read_annotations_directory(
                        dex_reader,
                        annotations_off,
                        strings_list,
                        types_list,
                        protos_list,
                        fields_list,
                        methods_list,
                    )?
                }
            } else {
                AnnotationsDirectory::default()
            };

            // If class_data_off == 0 then we have no class data
            let mut class_data = None;
            if level != ClassDecodeLevel::Declaration && class_data_off != 0 {
                // Start parse class data

                // Keep track of current stream position
                let current_offset = dex_reader.bytes.position();

                // Go to class data offset
                dex_reader
                    .bytes
                    .seek(SeekFrom::Start(class_data_off.into()))?;

                let (static_fields_size, _) = dex_reader.read_uleb128()?;
                let (instance_fields_size, _) = dex_reader.read_uleb128()?;
                let (direct_methods_size, _) = dex_reader.read_uleb128()?;
                let (virtual_methods_size, _) = dex_reader.read_uleb128()?;

                let mut static_fields =
                    Vec::<EncodedField>::with_capacity(static_fields_size as usize);
                let mut instance_fields =
                    Vec::<EncodedField>::with_capacity(instance_fields_size as usize);
                let mut direct_methods =
                    Vec::<EncodedMethod>::with_capacity(direct_methods_size as usize);
                let mut virtual_methods =
                    Vec::<EncodedMethod>::with_capacity(virtual_methods_size as usize);

                // Encoded fields
                let mut field_idx = 0u32;
                for i in 0..static_fields_size {
                    let (idx, _) = dex_reader.read_uleb128()?;
                    let (access_flags, _) = dex_reader.read_uleb128()?;

                    field_idx += idx;

                    let decoded_field = fields_list
                        .items
                        .get(field_idx as usize)
                        .ok_or(DexError::InvalidFieldIdx)?;
                    let decoded_flags = AccessFlag::parse(access_flags, AccessFlagType::Field);

                    static_fields.push(EncodedField {
                        field: decoded_field.to_string(),
                        access_flags_raw: access_flags,
                        access_flags: decoded_flags,
                        initial_value: static_values.get(i as usize).cloned(),
                        signature: annotations.field_signatures.get(&field_idx).cloned(),
                        annotations: annotations
                            .field_annotations
                            .get(&field_idx)
                            .cloned()
                            .unwrap_or_default(),
                    });
                }

                let mut field_idx = 0u32;
                for _ in 0..instance_fields_size {
                    let (idx, _) = dex_reader.read_uleb128()?;
                    let (access_flags, _) = dex_reader.read_uleb128()?;

                    field_idx += idx;

                    let decoded_field = fields_list
                        .items
                        .get(field_idx as usize)
                        .ok_or(DexError::InvalidFieldIdx)?;
                    let decoded_flags = AccessFlag::parse(access_flags, AccessFlagType::Field);

                    instance_fields.push(EncodedField {
                        field: decoded_field.to_string(),
                        access_flags_raw: access_flags,
                        access_flags: decoded_flags,
                        initial_value: None,
                        signature: annotations.field_signatures.get(&field_idx).cloned(),
                        annotations: annotations
                            .field_annotations
                            .get(&field_idx)
                            .cloned()
                            .unwrap_or_default(),
                    });
                }

                // Encoded methods
                let mut method_idx = 0;
                for _ in 0..direct_methods_size {
                    let (idx, _) = dex_reader.read_uleb128()?;
                    let (access_flags, _) = dex_reader.read_uleb128()?;
                    let (code_offset, _) = dex_reader.read_uleb128()?;

                    method_idx += idx;

                    let proto = methods_list
                        .items
                        .get(method_idx as usize)
                        .ok_or(DexError::InvalidMethodIdx)?;
                    let decoded_flags = AccessFlag::parse(access_flags, AccessFlagType::Method);

                    if code_offset == 0 {
                        // Abstract or native methods have no code
                        direct_methods.push(EncodedMethod {
                            method_idx,
                            proto: proto.to_string(),
                            access_flags_raw: access_flags,
                            access_flags: decoded_flags,
                            code_offset: None,
                            code_item: None,
                            throws: annotations
                                .method_throws
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            signature: annotations.method_signatures.get(&method_idx).cloned(),
                            annotations: annotations
                                .method_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            parameter_annotations: annotations
                                .parameter_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                        });
                    } else {
                        let code_item = if level == ClassDecodeLevel::Bytecode {
                            let current_offset = dex_reader.bytes.position();
                            let code_item =
                                CodeItem::build(dex_reader, code_offset, types_list, strings_list)?;
                            dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
                            Some(code_item)
                        } else {
                            None
                        };

                        direct_methods.push(EncodedMethod {
                            method_idx,
                            proto: proto.to_string(),
                            access_flags_raw: access_flags,
                            access_flags: decoded_flags,
                            code_offset: Some(code_offset),
                            code_item,
                            throws: annotations
                                .method_throws
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            signature: annotations.method_signatures.get(&method_idx).cloned(),
                            annotations: annotations
                                .method_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            parameter_annotations: annotations
                                .parameter_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                        });
                    }
                }

                let mut method_idx = 0;
                for _ in 0..virtual_methods_size {
                    let (idx, _) = dex_reader.read_uleb128()?;
                    let (access_flags, _) = dex_reader.read_uleb128()?;
                    let (code_offset, _) = dex_reader.read_uleb128()?;

                    method_idx += idx;

                    let proto = methods_list
                        .items
                        .get(method_idx as usize)
                        .ok_or(DexError::InvalidMethodIdx)?;
                    let decoded_flags = AccessFlag::parse(access_flags, AccessFlagType::Method);

                    if code_offset == 0 {
                        // Abstract or native methods have no code
                        virtual_methods.push(EncodedMethod {
                            method_idx,
                            proto: proto.to_string(),
                            access_flags_raw: access_flags,
                            access_flags: decoded_flags,
                            code_offset: None,
                            code_item: None,
                            throws: annotations
                                .method_throws
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            signature: annotations.method_signatures.get(&method_idx).cloned(),
                            annotations: annotations
                                .method_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            parameter_annotations: annotations
                                .parameter_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                        });
                    } else {
                        let code_item = if level == ClassDecodeLevel::Bytecode {
                            let current_offset = dex_reader.bytes.position();
                            let code_item =
                                CodeItem::build(dex_reader, code_offset, types_list, strings_list)?;
                            dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
                            Some(code_item)
                        } else {
                            None
                        };

                        virtual_methods.push(EncodedMethod {
                            method_idx,
                            proto: proto.to_string(),
                            access_flags_raw: access_flags,
                            access_flags: decoded_flags,
                            code_offset: Some(code_offset),
                            code_item,
                            throws: annotations
                                .method_throws
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            signature: annotations.method_signatures.get(&method_idx).cloned(),
                            annotations: annotations
                                .method_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                            parameter_annotations: annotations
                                .parameter_annotations
                                .get(&method_idx)
                                .cloned()
                                .unwrap_or_default(),
                        });
                    }
                }

                // Go back to the previous offset
                dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;

                class_data = Some(ClassDataItem {
                    static_fields,
                    instance_fields,
                    direct_methods,
                    virtual_methods,
                });
            }

            methods.push(ClassDefItem {
                class_str: class_str.to_string(),
                access_flags_raw: access_flags,
                access_flags: access_flags_decoded,
                superclass_str: superclass_str.cloned(),
                interfaces_off,
                interface_descriptors,
                source_file_str: source_file_str.map(ToString::to_string),
                annotations_off,
                class_data_off,
                static_value_off,
                static_values,
                class_data,
                members_loaded: level != ClassDecodeLevel::Declaration,
                signature: annotations.class_signature,
                inner_class: annotations.inner_class,
                member_classes: annotations.member_classes,
                enclosing_class: annotations.enclosing_class,
                enclosing_method: annotations.enclosing_method,
                annotations: annotations.class_annotations,
            });
        }

        Ok(DexClasses { items: methods })
    }

    /// Get a class definition from the class name, if it exists
    pub fn get_class_def(&self, class_name: &String) -> Option<&ClassDefItem> {
        self.items
            .iter()
            .find(|&item| &item.class_str == class_name)
    }
}

/// Annotations directory parsed into per-target annotations plus the
/// Dalvik-system annotations that carry JVM source semantics.
#[derive(Default)]
pub(crate) struct AnnotationsDirectory {
    pub class_annotations: Vec<DexAnnotation>,
    pub field_annotations: HashMap<u32, Vec<DexAnnotation>>,
    pub method_annotations: HashMap<u32, Vec<DexAnnotation>>,
    pub parameter_annotations: HashMap<u32, Vec<Vec<DexAnnotation>>>,
    pub class_signature: Option<String>,
    pub field_signatures: HashMap<u32, String>,
    pub method_signatures: HashMap<u32, String>,
    pub method_throws: HashMap<u32, Vec<String>>,
    pub inner_class: Option<InnerClassAnnotation>,
    pub member_classes: Vec<String>,
    pub enclosing_class: Option<String>,
    pub enclosing_method: Option<String>,
}

/// Read a DEX `type_list` at `interfaces_off` and resolve each type index to
/// its descriptor string. Returns an empty vector when `interfaces_off == 0`.
fn read_interface_list(
    dex_reader: &mut DexReader,
    interfaces_off: u32,
    types_list: &DexTypes,
) -> Result<Vec<String>, DexError> {
    if interfaces_off == 0 {
        return Ok(Vec::new());
    }
    let return_offset = dex_reader.bytes.position();
    dex_reader
        .bytes
        .seek(SeekFrom::Start(interfaces_off.into()))?;
    let size = dex_reader.read_u32()?;
    let mut descriptors = Vec::with_capacity(size as usize);
    for _ in 0..size {
        let type_idx = dex_reader.read_u16()? as u32;
        let descriptor = types_list
            .items
            .get(type_idx as usize)
            .ok_or(DexError::InvalidTypeIdx)?;
        descriptors.push(descriptor.clone());
    }
    dex_reader.bytes.seek(SeekFrom::Start(return_offset))?;
    Ok(descriptors)
}

fn read_annotations_directory(
    dex_reader: &mut DexReader,
    annotations_off: u32,
    strings: &DexStrings,
    types: &DexTypes,
    protos: &DexProtos,
    fields: &DexFields,
    methods: &DexMethods,
) -> Result<AnnotationsDirectory, DexError> {
    let current_offset = dex_reader.bytes.position();
    dex_reader
        .bytes
        .seek(SeekFrom::Start(annotations_off.into()))?;

    let class_annotations_off = dex_reader.read_u32()?;
    let fields_size = dex_reader.read_u32()?;
    let methods_size = dex_reader.read_u32()?;
    let parameters_size = dex_reader.read_u32()?;

    let mut field_pairs = Vec::with_capacity(fields_size as usize);
    for _ in 0..fields_size {
        field_pairs.push((dex_reader.read_u32()?, dex_reader.read_u32()?));
    }
    let mut method_pairs = Vec::with_capacity(methods_size as usize);
    for _ in 0..methods_size {
        method_pairs.push((dex_reader.read_u32()?, dex_reader.read_u32()?));
    }
    let mut parameter_pairs = Vec::with_capacity(parameters_size as usize);
    for _ in 0..parameters_size {
        parameter_pairs.push((dex_reader.read_u32()?, dex_reader.read_u32()?));
    }

    let class_annotations = read_annotation_set(
        dex_reader,
        class_annotations_off,
        strings,
        types,
        protos,
        fields,
        methods,
    )?;
    let class_metadata = ClassAnnotationMetadata::from_annotations(&class_annotations);

    let mut field_annotations = HashMap::new();
    let mut field_signatures = HashMap::new();
    for (field_idx, set_off) in field_pairs {
        let annotations =
            read_annotation_set(dex_reader, set_off, strings, types, protos, fields, methods)?;
        if let Some(sig) = first_signature(&annotations) {
            field_signatures.insert(field_idx, sig);
        }
        if !annotations.is_empty() {
            field_annotations.insert(field_idx, annotations);
        }
    }
    let mut method_annotations = HashMap::new();
    let mut method_signatures = HashMap::new();
    let mut method_throws = HashMap::new();
    for (method_idx, set_off) in method_pairs {
        let annotations =
            read_annotation_set(dex_reader, set_off, strings, types, protos, fields, methods)?;
        if let Some(sig) = first_signature(&annotations) {
            method_signatures.insert(method_idx, sig);
        }
        if let Some(throws) = first_throws(&annotations) {
            method_throws.insert(method_idx, throws);
        }
        if !annotations.is_empty() {
            method_annotations.insert(method_idx, annotations);
        }
    }
    let mut parameter_annotations = HashMap::new();
    for (method_idx, list_off) in parameter_pairs {
        let annotations = read_parameter_annotation_list(
            dex_reader, list_off, strings, types, protos, fields, methods,
        )?;
        if !annotations.is_empty() {
            parameter_annotations.insert(method_idx, annotations);
        }
    }

    dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
    Ok(AnnotationsDirectory {
        class_signature: class_metadata.signature,
        class_annotations,
        field_annotations,
        field_signatures,
        method_annotations,
        parameter_annotations,
        method_signatures,
        method_throws,
        inner_class: class_metadata.inner_class,
        member_classes: class_metadata.member_classes,
        enclosing_class: class_metadata.enclosing_class,
        enclosing_method: class_metadata.enclosing_method,
    })
}

fn read_class_annotations_directory(
    dex_reader: &mut DexReader,
    annotations_off: u32,
    strings: &DexStrings,
    types: &DexTypes,
    protos: &DexProtos,
    fields: &DexFields,
    methods: &DexMethods,
) -> Result<AnnotationsDirectory, DexError> {
    let current_offset = dex_reader.bytes.position();
    dex_reader
        .bytes
        .seek(SeekFrom::Start(annotations_off.into()))?;
    let class_annotations_off = dex_reader.read_u32()?;
    let class_annotations = read_annotation_set(
        dex_reader,
        class_annotations_off,
        strings,
        types,
        protos,
        fields,
        methods,
    )?;
    dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
    let metadata = ClassAnnotationMetadata::from_annotations(&class_annotations);
    Ok(AnnotationsDirectory {
        class_annotations,
        class_signature: metadata.signature,
        inner_class: metadata.inner_class,
        member_classes: metadata.member_classes,
        enclosing_class: metadata.enclosing_class,
        enclosing_method: metadata.enclosing_method,
        ..AnnotationsDirectory::default()
    })
}

fn read_annotation_set(
    dex_reader: &mut DexReader,
    annotations_off: u32,
    strings: &DexStrings,
    types: &DexTypes,
    protos: &DexProtos,
    fields: &DexFields,
    methods: &DexMethods,
) -> Result<Vec<DexAnnotation>, DexError> {
    if annotations_off == 0 {
        return Ok(Vec::new());
    }

    let current_offset = dex_reader.bytes.position();
    dex_reader
        .bytes
        .seek(SeekFrom::Start(annotations_off.into()))?;
    let size = dex_reader.read_u32()?;
    let mut annotation_offsets = Vec::with_capacity(size as usize);
    for _ in 0..size {
        annotation_offsets.push(dex_reader.read_u32()?);
    }

    let mut annotations = Vec::with_capacity(annotation_offsets.len());
    for annotation_off in annotation_offsets {
        annotations.push(read_annotation_item(
            dex_reader,
            annotation_off,
            strings,
            types,
            protos,
            fields,
            methods,
        )?);
    }

    dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
    Ok(annotations)
}

fn read_parameter_annotation_list(
    dex_reader: &mut DexReader,
    annotation_list_off: u32,
    strings: &DexStrings,
    types: &DexTypes,
    protos: &DexProtos,
    fields: &DexFields,
    methods: &DexMethods,
) -> Result<Vec<Vec<DexAnnotation>>, DexError> {
    if annotation_list_off == 0 {
        return Ok(Vec::new());
    }

    let current_offset = dex_reader.bytes.position();
    dex_reader
        .bytes
        .seek(SeekFrom::Start(annotation_list_off.into()))?;
    let size = dex_reader.read_u32()?;
    let mut annotation_set_offsets = Vec::with_capacity(size as usize);
    for _ in 0..size {
        annotation_set_offsets.push(dex_reader.read_u32()?);
    }

    let mut parameter_annotations = Vec::with_capacity(annotation_set_offsets.len());
    for annotation_set_off in annotation_set_offsets {
        parameter_annotations.push(read_annotation_set(
            dex_reader,
            annotation_set_off,
            strings,
            types,
            protos,
            fields,
            methods,
        )?);
    }

    dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
    Ok(parameter_annotations)
}

fn read_annotation_item(
    dex_reader: &mut DexReader,
    annotation_off: u32,
    strings: &DexStrings,
    types: &DexTypes,
    protos: &DexProtos,
    fields: &DexFields,
    methods: &DexMethods,
) -> Result<DexAnnotation, DexError> {
    let current_offset = dex_reader.bytes.position();
    dex_reader
        .bytes
        .seek(SeekFrom::Start(annotation_off.into()))?;
    let visibility = AnnotationVisibility::from_raw(dex_reader.read_u8()?);
    let annotation = read_encoded_annotation(
        dex_reader,
        strings,
        types,
        Some(protos),
        Some(fields),
        Some(methods),
    )?;
    dex_reader.bytes.seek(SeekFrom::Start(current_offset))?;
    Ok(DexAnnotation {
        visibility,
        annotation,
    })
}

#[derive(Default)]
struct ClassAnnotationMetadata {
    signature: Option<String>,
    inner_class: Option<InnerClassAnnotation>,
    member_classes: Vec<String>,
    enclosing_class: Option<String>,
    enclosing_method: Option<String>,
}

impl ClassAnnotationMetadata {
    fn from_annotations(annotations: &[DexAnnotation]) -> Self {
        let mut metadata = Self::default();
        for annotation in annotations {
            metadata.absorb(&annotation.annotation);
        }
        metadata
    }

    fn absorb(&mut self, annotation: &EncodedAnnotation) {
        match annotation.annotation_type.as_str() {
            "Ldalvik/annotation/Signature;" => {
                if self.signature.is_none() {
                    self.signature = extract_signature_string(annotation);
                }
            }
            "Ldalvik/annotation/InnerClass;" => {
                if self.inner_class.is_none() {
                    self.inner_class = extract_inner_class_annotation(annotation);
                }
            }
            "Ldalvik/annotation/MemberClasses;" => {
                self.member_classes.extend(extract_type_array(annotation));
            }
            "Ldalvik/annotation/EnclosingClass;" => {
                if self.enclosing_class.is_none() {
                    self.enclosing_class = extract_single_type_value(annotation);
                }
            }
            "Ldalvik/annotation/EnclosingMethod;" => {
                if self.enclosing_method.is_none() {
                    self.enclosing_method = extract_single_method_value(annotation);
                }
            }
            _ => {}
        }
    }
}

fn first_signature(annotations: &[DexAnnotation]) -> Option<String> {
    annotations
        .iter()
        .find(|annotation| annotation.annotation.annotation_type == "Ldalvik/annotation/Signature;")
        .and_then(|annotation| extract_signature_string(&annotation.annotation))
}

fn first_throws(annotations: &[DexAnnotation]) -> Option<Vec<String>> {
    annotations
        .iter()
        .find(|annotation| annotation.annotation.annotation_type == "Ldalvik/annotation/Throws;")
        .and_then(|annotation| extract_throws_types(&annotation.annotation))
}

fn extract_inner_class_annotation(annotation: &EncodedAnnotation) -> Option<InnerClassAnnotation> {
    let name = annotation
        .elements
        .iter()
        .find(|element| element.name == "name")
        .and_then(|element| match &element.value {
            EncodedValue::String(value) => Some(value.to_string()),
            EncodedValue::Null => None,
            _ => None,
        });
    let access_flags = annotation
        .elements
        .iter()
        .find(|element| element.name == "accessFlags")
        .and_then(encoded_value_as_u32)
        .unwrap_or(0);
    Some(InnerClassAnnotation { name, access_flags })
}

fn extract_single_type_value(annotation: &EncodedAnnotation) -> Option<String> {
    annotation
        .elements
        .iter()
        .find(|element| element.name == "value")
        .and_then(|element| match &element.value {
            EncodedValue::Type(value) => Some(value.clone()),
            _ => None,
        })
}

fn extract_type_array(annotation: &EncodedAnnotation) -> Vec<String> {
    annotation
        .elements
        .iter()
        .find(|element| element.name == "value")
        .and_then(|element| match &element.value {
            EncodedValue::Array(values) => Some(
                values
                    .iter()
                    .filter_map(|value| match value {
                        EncodedValue::Type(value) => Some(value.clone()),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default()
}

fn extract_single_method_value(annotation: &EncodedAnnotation) -> Option<String> {
    annotation
        .elements
        .iter()
        .find(|element| element.name == "value")
        .and_then(|element| match &element.value {
            EncodedValue::Method(value) => Some(value.clone()),
            _ => None,
        })
}

fn encoded_value_as_u32(element: &AnnotationElement) -> Option<u32> {
    match element.value.clone() {
        EncodedValue::Byte(value) => Some(value as i32 as u32),
        EncodedValue::Short(value) => Some(value as i32 as u32),
        EncodedValue::Char(value) => Some(value as u32),
        EncodedValue::Int(value) => Some(value as u32),
        EncodedValue::Long(value) => u32::try_from(value).ok(),
        _ => None,
    }
}

fn extract_signature_string(annotation: &EncodedAnnotation) -> Option<String> {
    annotation
        .elements
        .iter()
        .find(|element| element.name == "value")
        .and_then(|element| match &element.value {
            EncodedValue::Array(values) => {
                let mut signature = String::new();
                for value in values {
                    if let EncodedValue::String(s) = value {
                        signature.push_str(s.as_str());
                    }
                }
                if signature.is_empty() {
                    None
                } else {
                    Some(signature)
                }
            }
            _ => None,
        })
}

fn extract_throws_types(annotation: &EncodedAnnotation) -> Option<Vec<String>> {
    annotation
        .elements
        .iter()
        .find(|element| element.name == "value")
        .and_then(|element| match &element.value {
            EncodedValue::Array(values) => Some(
                values
                    .iter()
                    .filter_map(|value| match value {
                        EncodedValue::Type(ty) => Some(ty.clone()),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        })
}

impl ClassDefItem {
    pub(crate) fn members_loaded(&self) -> bool {
        self.members_loaded
    }

    pub(crate) fn class_data_offset(&self) -> u32 {
        self.class_data_off
    }

    /// Get the name from a class definition
    pub fn get_class_name(&self) -> &String {
        &self.class_str
    }

    /// Get the raw access flags bitfield for this class definition.
    pub fn get_access_flags_raw(&self) -> u32 {
        self.access_flags_raw
    }

    /// Get the access flags of a class definition
    pub fn get_access_flags(&self) -> String {
        AccessFlag::vec_to_string(&self.access_flags)
    }

    /// Get the superclass descriptor, if this class has one.
    pub fn get_superclass(&self) -> Option<&str> {
        self.superclass_str.as_deref()
    }

    /// Get the list of implemented interface descriptors
    /// (e.g. `Ljava/io/Serializable;`), in declaration order.
    pub fn get_interfaces(&self) -> &[String] {
        &self.interface_descriptors
    }

    /// Get the source file name recorded in debug metadata, if present.
    pub fn get_source_file(&self) -> Option<&str> {
        self.source_file_str.as_deref()
    }

    pub fn get_inner_class_annotation(&self) -> Option<&InnerClassAnnotation> {
        self.inner_class.as_ref()
    }

    pub fn get_member_classes(&self) -> &[String] {
        &self.member_classes
    }

    pub fn get_enclosing_class(&self) -> Option<&str> {
        self.enclosing_class.as_deref()
    }

    pub fn get_enclosing_method(&self) -> Option<&str> {
        self.enclosing_method.as_deref()
    }

    /// Get the methods of a class definition
    pub fn get_methods(&self) -> Vec<&EncodedMethod> {
        let mut methods = Vec::new();

        if let Some(class_data) = &self.class_data {
            methods.extend(&class_data.direct_methods);
            methods.extend(&class_data.virtual_methods);
        }

        methods
    }

    /// Get the fields declared by this class.
    pub fn get_fields(&self) -> Vec<&EncodedField> {
        let mut fields = Vec::new();

        if let Some(class_data) = &self.class_data {
            fields.extend(&class_data.static_fields);
            fields.extend(&class_data.instance_fields);
        }

        fields
    }

    /// Get encoded static initial values declared by this class.
    pub fn get_static_values(&self) -> &[EncodedValue] {
        &self.static_values
    }

    /// Get a method from a class definition using the method name
    pub fn get_encoded_method(&self, method_name: &String) -> Option<&EncodedMethod> {
        if let Some(class_data) = &self.class_data {
            for method in &class_data.direct_methods {
                if method.get_method_name() == method_name {
                    return Some(method);
                }
            }
            for method in &class_data.virtual_methods {
                if method.get_method_name() == method_name {
                    return Some(method);
                }
            }
        }
        None
    }
}

impl EncodedField {
    /// Get the raw access flags bitfield for this field.
    pub fn get_access_flags_raw(&self) -> u32 {
        self.access_flags_raw
    }

    /// Get the full field reference.
    pub fn get_field(&self) -> &str {
        &self.field
    }

    /// Get the access flags of a field.
    pub fn get_access_flags(&self) -> String {
        AccessFlag::vec_to_string(&self.access_flags)
    }

    /// Get the encoded initial value for a static field.
    pub fn get_initial_value(&self) -> Option<&EncodedValue> {
        self.initial_value.as_ref()
    }
}

impl EncodedMethod {
    /// Get the raw access flags bitfield for this method.
    pub fn get_access_flags_raw(&self) -> u32 {
        self.access_flags_raw
    }

    /// Get the prototype of a method
    pub fn get_proto(&self) -> &str {
        &self.proto
    }

    /// Get the name of a method
    pub fn get_method_name(&self) -> &str {
        let matches = METHOD_REGEX.captures(&self.proto);
        let method_name = match matches {
            Some(matched) => match matched.name("method") {
                Some(name) => name.as_str(),
                None => "",
            },
            None => "",
        };

        if method_name.is_empty() {
            warn!("Cannot retrieve method name from prototype");
            debug!("Prototype: {}", &self.proto);
        };

        method_name
    }

    /// Get the access flags of a method
    pub fn get_access_flags(&self) -> String {
        AccessFlag::vec_to_string(&self.access_flags)
    }
}
