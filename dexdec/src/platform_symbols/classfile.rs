use std::io;

use super::{
    PlatformAnnotation, PlatformAnnotationValue, PlatformClass, PlatformConstant, PlatformField,
    PlatformMethod, SymbolAvailability,
};

pub(crate) struct ClassFileDecoder;

impl ClassFileDecoder {
    const MAGIC: u32 = 0xcafebabe;
    const MAX_ANNOTATION_DEPTH: usize = 64;

    pub(crate) fn decode(bytes: &[u8]) -> io::Result<PlatformClass> {
        let mut reader = ClassReader::new(bytes);
        if reader.u4()? != Self::MAGIC {
            return Err(invalid_data("invalid class-file header"));
        }
        let _minor = reader.u2()?;
        let major = reader.u2()?;
        if major < 45 {
            return Err(invalid_data("unsupported class-file version"));
        }
        let constants = ConstantPool::read(&mut reader)?;
        let mut access_flags = u32::from(reader.u2()?);
        let descriptor = constants.class_descriptor(reader.u2()?)?;
        let super_index = reader.u2()?;
        let super_class = (super_index != 0)
            .then(|| constants.class_descriptor(super_index))
            .transpose()?;
        let interface_count = usize::from(reader.u2()?);
        let mut interfaces = Vec::with_capacity(interface_count);
        for _ in 0..interface_count {
            interfaces.push(constants.class_descriptor(reader.u2()?)?);
        }

        let field_count = usize::from(reader.u2()?);
        let mut fields = Vec::with_capacity(field_count);
        for _ in 0..field_count {
            fields.push(Self::field(&mut reader, &constants)?);
        }
        let method_count = usize::from(reader.u2()?);
        let mut methods = Vec::with_capacity(method_count);
        for _ in 0..method_count {
            methods.push(Self::method(&mut reader, &constants)?);
        }
        let attributes = DecodedAttributes::read(&mut reader, &constants)?;
        if attributes.synthetic {
            access_flags |= 0x1000;
        }
        reader.finish()?;

        let mut annotations = attributes.annotations;
        annotations.extend(
            attributes
                .type_annotations
                .into_iter()
                .map(|annotation| annotation.annotation),
        );
        normalize_annotations(&mut annotations);
        Ok(PlatformClass {
            descriptor,
            source: 0,
            availability: SymbolAvailability::exact(0),
            access_flags,
            super_class,
            interfaces,
            signature: attributes.signature,
            annotations,
            fields,
            methods,
        })
    }

    fn field(reader: &mut ClassReader<'_>, constants: &ConstantPool) -> io::Result<PlatformField> {
        let mut access_flags = u32::from(reader.u2()?);
        let name = constants.utf8(reader.u2()?)?.to_string();
        let descriptor = constants.utf8(reader.u2()?)?.to_string();
        let attributes = DecodedAttributes::read(reader, constants)?;
        if attributes.synthetic {
            access_flags |= 0x1000;
        }
        let constant = attributes
            .constant
            .map(|index| constants.constant(index))
            .transpose()?;
        let mut annotations = attributes.annotations;
        annotations.extend(
            attributes
                .type_annotations
                .into_iter()
                .map(|annotation| annotation.annotation),
        );
        normalize_annotations(&mut annotations);
        Ok(PlatformField {
            name,
            descriptor,
            signature: attributes.signature,
            access_flags,
            constant,
            annotations,
        })
    }

    fn method(
        reader: &mut ClassReader<'_>,
        constants: &ConstantPool,
    ) -> io::Result<PlatformMethod> {
        let mut access_flags = u32::from(reader.u2()?);
        let name = constants.utf8(reader.u2()?)?.to_string();
        let descriptor = constants.utf8(reader.u2()?)?.to_string();
        let attributes = DecodedAttributes::read(reader, constants)?;
        if attributes.synthetic {
            access_flags |= 0x1000;
        }
        let mut annotations = attributes.annotations;
        let mut parameter_annotations = attributes.parameter_annotations;
        for annotation in attributes.type_annotations {
            match annotation.target {
                TypeAnnotationTarget::MethodReturn => annotations.push(annotation.annotation),
                TypeAnnotationTarget::FormalParameter(parameter) => {
                    if parameter_annotations.len() <= parameter {
                        parameter_annotations.resize_with(parameter + 1, Vec::new);
                    }
                    parameter_annotations[parameter].push(annotation.annotation);
                }
                TypeAnnotationTarget::Other => {}
            }
        }
        normalize_annotations(&mut annotations);
        for annotations in &mut parameter_annotations {
            normalize_annotations(annotations);
        }
        Ok(PlatformMethod {
            name,
            descriptor,
            signature: attributes.signature,
            access_flags,
            exceptions: attributes.exceptions,
            parameter_names: attributes.parameter_names,
            annotations,
            parameter_annotations,
            parameter_domains: Vec::new(),
        })
    }
}

#[derive(Default)]
struct DecodedAttributes {
    signature: Option<String>,
    constant: Option<u16>,
    exceptions: Vec<String>,
    parameter_names: Vec<Option<String>>,
    annotations: Vec<PlatformAnnotation>,
    parameter_annotations: Vec<Vec<PlatformAnnotation>>,
    type_annotations: Vec<DecodedTypeAnnotation>,
    synthetic: bool,
}

impl DecodedAttributes {
    fn read(reader: &mut ClassReader<'_>, constants: &ConstantPool) -> io::Result<Self> {
        let count = usize::from(reader.u2()?);
        let mut decoded = Self::default();
        for _ in 0..count {
            let name = constants.utf8(reader.u2()?)?;
            let length = reader.usize_from_u4("attribute")?;
            let mut attribute = ClassReader::new(reader.bytes(length)?);
            match name {
                "Signature" => {
                    decoded.signature = Some(constants.utf8(attribute.u2()?)?.to_string());
                    attribute.finish()?;
                }
                "ConstantValue" => {
                    decoded.constant = Some(attribute.u2()?);
                    attribute.finish()?;
                }
                "Exceptions" => {
                    let exception_count = usize::from(attribute.u2()?);
                    for _ in 0..exception_count {
                        decoded
                            .exceptions
                            .push(constants.class_descriptor(attribute.u2()?)?);
                    }
                    attribute.finish()?;
                }
                "MethodParameters" => {
                    let parameter_count = usize::from(attribute.u1()?);
                    for _ in 0..parameter_count {
                        let index = attribute.u2()?;
                        decoded.parameter_names.push(
                            (index != 0)
                                .then(|| constants.utf8(index).map(str::to_string))
                                .transpose()?,
                        );
                        let _access = attribute.u2()?;
                    }
                    attribute.finish()?;
                }
                "RuntimeVisibleAnnotations" | "RuntimeInvisibleAnnotations" => {
                    decoded
                        .annotations
                        .extend(read_annotations(&mut attribute, constants)?);
                    attribute.finish()?;
                }
                "RuntimeVisibleParameterAnnotations" | "RuntimeInvisibleParameterAnnotations" => {
                    merge_parameter_annotations(
                        &mut decoded.parameter_annotations,
                        read_parameter_annotations(&mut attribute, constants)?,
                    );
                    attribute.finish()?;
                }
                "RuntimeVisibleTypeAnnotations" | "RuntimeInvisibleTypeAnnotations" => {
                    decoded
                        .type_annotations
                        .extend(read_type_annotations(&mut attribute, constants)?);
                    attribute.finish()?;
                }
                "Synthetic" => {
                    decoded.synthetic = true;
                    attribute.finish()?;
                }
                _ => {}
            }
        }
        Ok(decoded)
    }
}

#[derive(Debug)]
struct DecodedTypeAnnotation {
    target: TypeAnnotationTarget,
    annotation: PlatformAnnotation,
}

#[derive(Debug, Clone, Copy)]
enum TypeAnnotationTarget {
    MethodReturn,
    FormalParameter(usize),
    Other,
}

fn read_annotations(
    reader: &mut ClassReader<'_>,
    constants: &ConstantPool,
) -> io::Result<Vec<PlatformAnnotation>> {
    let count = usize::from(reader.u2()?);
    let mut annotations = Vec::with_capacity(count);
    for _ in 0..count {
        annotations.push(read_annotation(reader, constants, 0)?);
    }
    Ok(annotations)
}

fn read_parameter_annotations(
    reader: &mut ClassReader<'_>,
    constants: &ConstantPool,
) -> io::Result<Vec<Vec<PlatformAnnotation>>> {
    let parameter_count = usize::from(reader.u1()?);
    let mut parameters = Vec::with_capacity(parameter_count);
    for _ in 0..parameter_count {
        let annotation_count = usize::from(reader.u2()?);
        let mut annotations = Vec::with_capacity(annotation_count);
        for _ in 0..annotation_count {
            annotations.push(read_annotation(reader, constants, 0)?);
        }
        parameters.push(annotations);
    }
    Ok(parameters)
}

fn merge_parameter_annotations(
    destination: &mut Vec<Vec<PlatformAnnotation>>,
    source: Vec<Vec<PlatformAnnotation>>,
) {
    if destination.len() < source.len() {
        destination.resize_with(source.len(), Vec::new);
    }
    for (index, annotations) in source.into_iter().enumerate() {
        destination[index].extend(annotations);
    }
}

fn read_type_annotations(
    reader: &mut ClassReader<'_>,
    constants: &ConstantPool,
) -> io::Result<Vec<DecodedTypeAnnotation>> {
    let count = usize::from(reader.u2()?);
    let mut annotations = Vec::with_capacity(count);
    for _ in 0..count {
        let target_type = reader.u1()?;
        let target = skip_type_annotation_target(reader, target_type)?;
        let path_length = usize::from(reader.u1()?);
        reader.skip(
            path_length
                .checked_mul(2)
                .ok_or_else(|| invalid_data("type annotation path overflow"))?,
        )?;
        annotations.push(DecodedTypeAnnotation {
            target,
            annotation: read_annotation(reader, constants, 0)?,
        });
    }
    Ok(annotations)
}

fn skip_type_annotation_target(
    reader: &mut ClassReader<'_>,
    target_type: u8,
) -> io::Result<TypeAnnotationTarget> {
    match target_type {
        0x00 | 0x01 => {
            reader.skip(1)?;
            Ok(TypeAnnotationTarget::Other)
        }
        0x10 => {
            reader.skip(2)?;
            Ok(TypeAnnotationTarget::Other)
        }
        0x11 | 0x12 => {
            reader.skip(2)?;
            Ok(TypeAnnotationTarget::Other)
        }
        0x13 | 0x15 => Ok(TypeAnnotationTarget::Other),
        0x14 => Ok(TypeAnnotationTarget::MethodReturn),
        0x16 => Ok(TypeAnnotationTarget::FormalParameter(usize::from(
            reader.u1()?,
        ))),
        0x17 => {
            reader.skip(2)?;
            Ok(TypeAnnotationTarget::Other)
        }
        0x40 | 0x41 => {
            let count = usize::from(reader.u2()?);
            reader.skip(
                count
                    .checked_mul(6)
                    .ok_or_else(|| invalid_data("local-variable annotation table overflow"))?,
            )?;
            Ok(TypeAnnotationTarget::Other)
        }
        0x42..=0x46 => {
            reader.skip(2)?;
            Ok(TypeAnnotationTarget::Other)
        }
        0x47..=0x4b => {
            reader.skip(3)?;
            Ok(TypeAnnotationTarget::Other)
        }
        _ => Err(invalid_data("invalid type-annotation target")),
    }
}

fn read_annotation(
    reader: &mut ClassReader<'_>,
    constants: &ConstantPool,
    depth: usize,
) -> io::Result<PlatformAnnotation> {
    if depth >= ClassFileDecoder::MAX_ANNOTATION_DEPTH {
        return Err(invalid_data("annotation nesting exceeds safety limit"));
    }
    let descriptor = constants.utf8(reader.u2()?)?.to_string();
    let pair_count = usize::from(reader.u2()?);
    let mut elements = std::collections::BTreeMap::new();
    for _ in 0..pair_count {
        let name = constants.utf8(reader.u2()?)?.to_string();
        let value = read_element_value(reader, constants, depth + 1)?;
        elements.insert(name, value);
    }
    Ok(PlatformAnnotation {
        descriptor,
        elements,
    })
}

fn read_element_value(
    reader: &mut ClassReader<'_>,
    constants: &ConstantPool,
    depth: usize,
) -> io::Result<PlatformAnnotationValue> {
    if depth >= ClassFileDecoder::MAX_ANNOTATION_DEPTH {
        return Err(invalid_data(
            "annotation value nesting exceeds safety limit",
        ));
    }
    Ok(match reader.u1()? {
        b'B' | b'C' | b'I' | b'S' => {
            PlatformAnnotationValue::Integer(i64::from(constants.integer(reader.u2()?)?))
        }
        b'Z' => PlatformAnnotationValue::Boolean(constants.integer(reader.u2()?)? != 0),
        b'J' => PlatformAnnotationValue::Integer(constants.long(reader.u2()?)?),
        b'F' => PlatformAnnotationValue::Float(constants.float(reader.u2()?)?),
        b'D' => PlatformAnnotationValue::Double(constants.double(reader.u2()?)?),
        b's' => PlatformAnnotationValue::String(constants.utf8(reader.u2()?)?.to_string()),
        b'c' => PlatformAnnotationValue::Type(constants.utf8(reader.u2()?)?.to_string()),
        b'e' => PlatformAnnotationValue::Enum {
            descriptor: constants.utf8(reader.u2()?)?.to_string(),
            constant: constants.utf8(reader.u2()?)?.to_string(),
        },
        b'@' => PlatformAnnotationValue::Annotation(Box::new(read_annotation(
            reader,
            constants,
            depth + 1,
        )?)),
        b'[' => {
            let count = usize::from(reader.u2()?);
            let mut values = Vec::with_capacity(count);
            for _ in 0..count {
                values.push(read_element_value(reader, constants, depth + 1)?);
            }
            PlatformAnnotationValue::Array(values)
        }
        _ => return Err(invalid_data("invalid annotation element tag")),
    })
}

fn normalize_annotations(annotations: &mut Vec<PlatformAnnotation>) {
    annotations.sort();
    annotations.dedup();
}

#[derive(Debug)]
enum ConstantPoolEntry {
    Unusable,
    Utf8(String),
    Integer(i32),
    Float(u32),
    Long(i64),
    Double(u64),
    Class(u16),
    String(u16),
    Other,
}

struct ConstantPool {
    entries: Vec<ConstantPoolEntry>,
}

impl ConstantPool {
    fn read(reader: &mut ClassReader<'_>) -> io::Result<Self> {
        let count = usize::from(reader.u2()?);
        if count == 0 {
            return Err(invalid_data("class-file constant pool is empty"));
        }
        let mut entries = Vec::with_capacity(count);
        entries.push(ConstantPoolEntry::Unusable);
        let mut index = 1;
        while index < count {
            let tag = reader.u1()?;
            let (entry, wide) = match tag {
                1 => {
                    let len = usize::from(reader.u2()?);
                    let bytes = reader.bytes(len)?;
                    let value = decode_modified_utf8(bytes)?;
                    (ConstantPoolEntry::Utf8(value), false)
                }
                3 => (
                    ConstantPoolEntry::Integer(i32::from_be_bytes(reader.array()?)),
                    false,
                ),
                4 => (
                    ConstantPoolEntry::Float(u32::from_be_bytes(reader.array()?)),
                    false,
                ),
                5 => (
                    ConstantPoolEntry::Long(i64::from_be_bytes(reader.array()?)),
                    true,
                ),
                6 => (
                    ConstantPoolEntry::Double(u64::from_be_bytes(reader.array()?)),
                    true,
                ),
                7 => (ConstantPoolEntry::Class(reader.u2()?), false),
                8 => (ConstantPoolEntry::String(reader.u2()?), false),
                9..=11 | 12 | 17 | 18 => {
                    reader.skip(4)?;
                    (ConstantPoolEntry::Other, false)
                }
                15 => {
                    reader.skip(3)?;
                    (ConstantPoolEntry::Other, false)
                }
                16 | 19 | 20 => {
                    reader.skip(2)?;
                    (ConstantPoolEntry::Other, false)
                }
                _ => return Err(invalid_data("invalid class-file constant tag")),
            };
            entries.push(entry);
            index += 1;
            if wide {
                if index >= count {
                    return Err(invalid_data("wide constant exceeds constant pool"));
                }
                entries.push(ConstantPoolEntry::Unusable);
                index += 1;
            }
        }
        Ok(Self { entries })
    }

    fn entry(&self, index: u16) -> io::Result<&ConstantPoolEntry> {
        self.entries
            .get(usize::from(index))
            .ok_or_else(|| invalid_data("invalid constant-pool index"))
    }

    fn utf8(&self, index: u16) -> io::Result<&str> {
        match self.entry(index)? {
            ConstantPoolEntry::Utf8(value) => Ok(value),
            _ => Err(invalid_data("constant-pool entry is not UTF-8")),
        }
    }

    fn class_descriptor(&self, index: u16) -> io::Result<String> {
        let ConstantPoolEntry::Class(name) = self.entry(index)? else {
            return Err(invalid_data("constant-pool entry is not a class"));
        };
        let name = self.utf8(*name)?;
        if name.starts_with('[') {
            Ok(name.to_string())
        } else if name.is_empty() || name.starts_with('L') || name.ends_with(';') {
            Err(invalid_data("invalid class-file internal name"))
        } else {
            Ok(format!("L{name};"))
        }
    }

    fn constant(&self, index: u16) -> io::Result<PlatformConstant> {
        match self.entry(index)? {
            ConstantPoolEntry::Integer(value) => Ok(PlatformConstant::Integer(i64::from(*value))),
            ConstantPoolEntry::Float(bits) => Ok(PlatformConstant::Float(*bits)),
            ConstantPoolEntry::Long(value) => Ok(PlatformConstant::Integer(*value)),
            ConstantPoolEntry::Double(bits) => Ok(PlatformConstant::Double(*bits)),
            ConstantPoolEntry::String(index) => {
                Ok(PlatformConstant::String(self.utf8(*index)?.to_string()))
            }
            _ => Err(invalid_data(
                "constant-pool entry cannot initialize a field",
            )),
        }
    }

    fn integer(&self, index: u16) -> io::Result<i32> {
        match self.entry(index)? {
            ConstantPoolEntry::Integer(value) => Ok(*value),
            _ => Err(invalid_data("annotation value is not an integer")),
        }
    }

    fn long(&self, index: u16) -> io::Result<i64> {
        match self.entry(index)? {
            ConstantPoolEntry::Long(value) => Ok(*value),
            _ => Err(invalid_data("annotation value is not a long")),
        }
    }

    fn float(&self, index: u16) -> io::Result<u32> {
        match self.entry(index)? {
            ConstantPoolEntry::Float(value) => Ok(*value),
            _ => Err(invalid_data("annotation value is not a float")),
        }
    }

    fn double(&self, index: u16) -> io::Result<u64> {
        match self.entry(index)? {
            ConstantPoolEntry::Double(value) => Ok(*value),
            _ => Err(invalid_data("annotation value is not a double")),
        }
    }
}

struct ClassReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ClassReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn finish(&self) -> io::Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(invalid_data("trailing bytes in class-file structure"))
        }
    }

    fn bytes(&mut self, len: usize) -> io::Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "truncated class file"))?;
        let bytes = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(bytes)
    }

    fn skip(&mut self, len: usize) -> io::Result<()> {
        self.bytes(len).map(|_| ())
    }

    fn array<const N: usize>(&mut self) -> io::Result<[u8; N]> {
        self.bytes(N)?
            .try_into()
            .map_err(|_| invalid_data("invalid fixed-width class-file value"))
    }

    fn u1(&mut self) -> io::Result<u8> {
        Ok(self.array::<1>()?[0])
    }

    fn u2(&mut self) -> io::Result<u16> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn u4(&mut self) -> io::Result<u32> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn usize_from_u4(&mut self, kind: &'static str) -> io::Result<usize> {
        usize::try_from(self.u4()?).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{kind} length exceeds address space"),
            )
        })
    }
}

fn invalid_data(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn decode_modified_utf8(bytes: &[u8]) -> io::Result<String> {
    let mut units = Vec::<u16>::with_capacity(bytes.len());
    let mut offset = 0;
    while offset < bytes.len() {
        let first = bytes[offset];
        offset += 1;
        match first {
            0x01..=0x7f => units.push(u16::from(first)),
            0xc0..=0xdf => {
                let second = continuation(bytes, &mut offset)?;
                let value = (u16::from(first & 0x1f) << 6) | u16::from(second);
                if value != 0 && value < 0x80 {
                    return Err(invalid_data("overlong modified UTF-8 sequence"));
                }
                units.push(value);
            }
            0xe0..=0xef => {
                let second = continuation(bytes, &mut offset)?;
                let third = continuation(bytes, &mut offset)?;
                let value =
                    (u16::from(first & 0x0f) << 12) | (u16::from(second) << 6) | u16::from(third);
                if value < 0x800 {
                    return Err(invalid_data("overlong modified UTF-8 sequence"));
                }
                units.push(value);
            }
            _ => return Err(invalid_data("invalid modified UTF-8 leading byte")),
        }
    }
    Ok(String::from_utf16_lossy(&units))
}

fn continuation(bytes: &[u8], offset: &mut usize) -> io::Result<u8> {
    let byte = bytes
        .get(*offset)
        .copied()
        .ok_or_else(|| invalid_data("truncated modified UTF-8 sequence"))?;
    *offset += 1;
    if byte & 0xc0 != 0x80 {
        return Err(invalid_data("invalid modified UTF-8 continuation byte"));
    }
    Ok(byte & 0x3f)
}
