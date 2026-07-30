//! DEX encoded values.

use std::io::{Seek, SeekFrom};

use crate::dex::fields::DexFields;
use crate::dex::methods::DexMethods;
use crate::dex::protos::DexProtos;
use crate::dex::reader::{DexEndianness, DexReader};
use crate::dex::strings::{DexString, DexStrings};
use crate::dex::types::DexTypes;
use crate::error::DexError;

#[derive(Debug, Clone, PartialEq)]
pub enum EncodedValue {
    Byte(i8),
    Short(i16),
    Char(u16),
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    MethodType(String),
    MethodHandle(u32),
    Method(String),
    Field(String),
    Enum(String),
    String(DexString),
    Type(String),
    Array(Vec<EncodedValue>),
    Annotation(EncodedAnnotation),
    Null,
    Boolean(bool),
    Unsupported { value_type: u8, raw: u64 },
}

#[derive(Debug, Clone, PartialEq)]
pub struct EncodedAnnotation {
    pub annotation_type: String,
    pub elements: Vec<AnnotationElement>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AnnotationElement {
    pub name: String,
    pub value: EncodedValue,
}

impl EncodedValue {
    pub fn read(
        reader: &mut DexReader,
        strings: &DexStrings,
        types: &DexTypes,
        protos: Option<&DexProtos>,
        fields: Option<&DexFields>,
        methods: Option<&DexMethods>,
    ) -> Result<Self, DexError> {
        let header = reader.read_u8()?;
        let value_type = header & 0x1f;
        let value_arg = header >> 5;

        match value_type {
            0x00 => Ok(Self::Byte(read_signed(reader, value_arg, 1)? as i8)),
            0x02 => Ok(Self::Short(read_signed(reader, value_arg, 2)? as i16)),
            0x03 => Ok(Self::Char(read_unsigned(reader, value_arg, 2)? as u16)),
            0x04 => Ok(Self::Int(read_signed(reader, value_arg, 4)? as i32)),
            0x06 => Ok(Self::Long(read_signed(reader, value_arg, 8)?)),
            0x10 => Ok(Self::Float(f32::from_bits(
                read_zero_extended_to_right(reader, value_arg, 4)? as u32,
            ))),
            0x11 => Ok(Self::Double(f64::from_bits(read_zero_extended_to_right(
                reader, value_arg, 8,
            )?))),
            0x15 => {
                let idx = read_unsigned(reader, value_arg, 4)? as usize;
                let value = protos
                    .and_then(|protos| protos.items.get(idx))
                    .ok_or(DexError::InvalidTypeIdx)?
                    .clone();
                Ok(Self::MethodType(value))
            }
            0x16 => {
                let idx = read_unsigned(reader, value_arg, 4)?;
                Ok(Self::MethodHandle(idx as u32))
            }
            0x17 => {
                let idx = read_unsigned(reader, value_arg, 4)? as usize;
                let value = strings
                    .strings
                    .get(idx)
                    .ok_or(DexError::InvalidStringIdx)?
                    .clone();
                Ok(Self::String(value))
            }
            0x18 => {
                let idx = read_unsigned(reader, value_arg, 4)? as usize;
                let value = types
                    .items
                    .get(idx)
                    .ok_or(DexError::InvalidTypeIdx)?
                    .clone();
                Ok(Self::Type(value))
            }
            0x19 => {
                let idx = read_unsigned(reader, value_arg, 4)? as usize;
                let value = fields
                    .and_then(|fields| fields.items.get(idx))
                    .ok_or(DexError::InvalidFieldIdx)?
                    .clone();
                Ok(Self::Field(value))
            }
            0x1a => {
                let idx = read_unsigned(reader, value_arg, 4)? as usize;
                let value = methods
                    .and_then(|methods| methods.items.get(idx))
                    .ok_or(DexError::InvalidMethodIdx)?
                    .clone();
                Ok(Self::Method(value))
            }
            0x1b => {
                let idx = read_unsigned(reader, value_arg, 4)? as usize;
                let value = fields
                    .and_then(|fields| fields.items.get(idx))
                    .ok_or(DexError::InvalidFieldIdx)?
                    .clone();
                Ok(Self::Enum(value))
            }
            0x1c => Ok(Self::Array(read_encoded_array_inline(
                reader, strings, types, protos, fields, methods,
            )?)),
            0x1d => Ok(Self::Annotation(read_encoded_annotation(
                reader, strings, types, protos, fields, methods,
            )?)),
            0x1e => Ok(Self::Null),
            0x1f => Ok(Self::Boolean(value_arg != 0)),
            _ => Ok(Self::Unsupported {
                value_type,
                raw: read_unsigned(reader, value_arg, 8)?,
            }),
        }
    }
}

pub fn read_encoded_array(
    reader: &mut DexReader,
    offset: u32,
    strings: &DexStrings,
    types: &DexTypes,
    protos: Option<&DexProtos>,
    fields: Option<&DexFields>,
    methods: Option<&DexMethods>,
) -> Result<Vec<EncodedValue>, DexError> {
    let current_offset = reader.bytes.position();
    reader.bytes.seek(SeekFrom::Start(offset.into()))?;

    let (size, _) = reader.read_uleb128()?;
    let mut values = Vec::with_capacity(size as usize);
    for _ in 0..size {
        values.push(EncodedValue::read(
            reader, strings, types, protos, fields, methods,
        )?);
    }

    reader.bytes.seek(SeekFrom::Start(current_offset))?;
    Ok(values)
}

pub fn read_encoded_annotation(
    reader: &mut DexReader,
    strings: &DexStrings,
    types: &DexTypes,
    protos: Option<&DexProtos>,
    fields: Option<&DexFields>,
    methods: Option<&DexMethods>,
) -> Result<EncodedAnnotation, DexError> {
    let (type_idx, _) = reader.read_uleb128()?;
    let annotation_type = types
        .items
        .get(type_idx as usize)
        .ok_or(DexError::InvalidTypeIdx)?
        .clone();
    let (size, _) = reader.read_uleb128()?;
    let mut elements = Vec::with_capacity(size as usize);
    for _ in 0..size {
        let (name_idx, _) = reader.read_uleb128()?;
        let name = strings
            .strings
            .get(name_idx as usize)
            .ok_or(DexError::InvalidStringIdx)?
            .to_string();
        let value = EncodedValue::read(reader, strings, types, protos, fields, methods)?;
        elements.push(AnnotationElement { name, value });
    }
    Ok(EncodedAnnotation {
        annotation_type,
        elements,
    })
}

fn read_encoded_array_inline(
    reader: &mut DexReader,
    strings: &DexStrings,
    types: &DexTypes,
    protos: Option<&DexProtos>,
    fields: Option<&DexFields>,
    methods: Option<&DexMethods>,
) -> Result<Vec<EncodedValue>, DexError> {
    let (size, _) = reader.read_uleb128()?;
    let mut values = Vec::with_capacity(size as usize);
    for _ in 0..size {
        values.push(EncodedValue::read(
            reader, strings, types, protos, fields, methods,
        )?);
    }
    Ok(values)
}

fn read_unsigned(reader: &mut DexReader, value_arg: u8, max_bytes: usize) -> Result<u64, DexError> {
    let byte_count = byte_count(value_arg, max_bytes)?;
    read_unsigned_bytes(reader, byte_count)
}

fn read_signed(reader: &mut DexReader, value_arg: u8, max_bytes: usize) -> Result<i64, DexError> {
    let byte_count = byte_count(value_arg, max_bytes)?;
    let raw = read_unsigned_bytes(reader, byte_count)?;
    let shift = (8 - byte_count) * 8;
    Ok(((raw << shift) as i64) >> shift)
}

fn read_zero_extended_to_right(
    reader: &mut DexReader,
    value_arg: u8,
    max_bytes: usize,
) -> Result<u64, DexError> {
    let byte_count = byte_count(value_arg, max_bytes)?;
    let raw = read_unsigned_bytes(reader, byte_count)?;
    let shift = (max_bytes - byte_count) * 8;
    Ok(raw << shift)
}

fn read_unsigned_bytes(reader: &mut DexReader, byte_count: usize) -> Result<u64, DexError> {
    let mut bytes = [0u8; 8];
    for byte in bytes.iter_mut().take(byte_count) {
        *byte = reader.read_u8()?;
    }

    Ok(match reader.endianness {
        DexEndianness::LittleEndian => u64::from_le_bytes(bytes),
        DexEndianness::BigEndian => {
            bytes[..byte_count].reverse();
            u64::from_le_bytes(bytes)
        }
    })
}

fn byte_count(value_arg: u8, max_bytes: usize) -> Result<usize, DexError> {
    let byte_count = value_arg as usize + 1;
    if byte_count > max_bytes {
        return Err(DexError::InvalidEncodedValue);
    }
    Ok(byte_count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn reader(bytes: Vec<u8>) -> DexReader {
        DexReader {
            bytes_len: bytes.len() as u64,
            bytes: Cursor::new(bytes.into()),
            endianness: DexEndianness::LittleEndian,
        }
    }

    fn empty_strings() -> DexStrings {
        DexStrings {
            strings: Vec::new(),
        }
    }

    fn empty_types() -> DexTypes {
        DexTypes { items: Vec::new() }
    }

    #[test]
    fn value_method_uses_method_id_table() {
        let mut reader = reader(vec![0x1a, 0x00]);
        let methods = DexMethods {
            items: vec!["Lpkg/Owner;->method()V".to_string()],
        };

        let value = EncodedValue::read(
            &mut reader,
            &empty_strings(),
            &empty_types(),
            None,
            None,
            Some(&methods),
        )
        .expect("method value");

        assert_eq!(value, EncodedValue::Method(methods.items[0].clone()));
    }

    #[test]
    fn value_method_handle_is_not_a_method_reference() {
        let mut reader = reader(vec![0x16, 0x07]);

        let value = EncodedValue::read(
            &mut reader,
            &empty_strings(),
            &empty_types(),
            None,
            None,
            None,
        )
        .expect("method handle value");

        assert_eq!(value, EncodedValue::MethodHandle(7));
    }
}
