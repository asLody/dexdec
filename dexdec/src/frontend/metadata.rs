//! Typed DEX metadata values and annotation nodes shared by declarations.

use crate::ir::{
    ArgType, DescriptorParseError, FieldReference, MethodDescriptor, MethodReference,
    ReferenceParseError, Utf16String,
};

#[derive(Debug, Clone)]
pub enum MetadataConversionError {
    Type {
        descriptor: String,
        source: DescriptorParseError,
    },
    Field {
        reference: String,
        source: ReferenceParseError,
    },
    Method {
        reference: String,
        source: ReferenceParseError,
    },
    MethodType {
        descriptor: String,
        source: DescriptorParseError,
    },
}

impl std::fmt::Display for MetadataConversionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Type { descriptor, source } => {
                write!(formatter, "invalid DEX type value {descriptor}: {source}")
            }
            Self::Field { reference, source } => {
                write!(formatter, "invalid DEX field value {reference}: {source}")
            }
            Self::Method { reference, source } => {
                write!(formatter, "invalid DEX method value {reference}: {source}")
            }
            Self::MethodType { descriptor, source } => {
                write!(
                    formatter,
                    "invalid DEX method type value {descriptor}: {source}"
                )
            }
        }
    }
}

impl std::error::Error for MetadataConversionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Type { source, .. } | Self::MethodType { source, .. } => Some(source),
            Self::Field { source, .. } | Self::Method { source, .. } => Some(source),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AnnotationNode {
    pub visibility: AnnotationVisibility,
    pub annotation_type: ArgType,
    pub elements: Vec<AnnotationElement>,
}

impl AnnotationNode {
    pub fn is_java_source_annotation(&self) -> bool {
        matches!(
            self.visibility,
            AnnotationVisibility::Build | AnnotationVisibility::Runtime
        ) && !is_dalvik_system_annotation(&self.annotation_type)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationVisibility {
    Build,
    Runtime,
    System,
    Unknown(u8),
}

#[derive(Debug, Clone, PartialEq)]
pub struct AnnotationElement {
    pub name: String,
    pub value: DexValue,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DexValue {
    Null,
    Boolean(bool),
    Byte(i8),
    Short(i16),
    Char(u16),
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    String(Utf16String),
    Type(ArgType),
    Field(FieldReference),
    Method(MethodReference),
    MethodType(MethodDescriptor),
    Enum(FieldReference),
    Array(Vec<DexValue>),
    Annotation(Box<AnnotationNode>),
    Unsupported { value_type: u8, raw: u64 },
}

impl From<rusty_dex::dex::classes::AnnotationVisibility> for AnnotationVisibility {
    fn from(value: rusty_dex::dex::classes::AnnotationVisibility) -> Self {
        match value {
            rusty_dex::dex::classes::AnnotationVisibility::Build => Self::Build,
            rusty_dex::dex::classes::AnnotationVisibility::Runtime => Self::Runtime,
            rusty_dex::dex::classes::AnnotationVisibility::System => Self::System,
            rusty_dex::dex::classes::AnnotationVisibility::Unknown(value) => Self::Unknown(value),
        }
    }
}

impl TryFrom<&rusty_dex::dex::classes::DexAnnotation> for AnnotationNode {
    type Error = MetadataConversionError;

    fn try_from(value: &rusty_dex::dex::classes::DexAnnotation) -> Result<Self, Self::Error> {
        Ok(Self {
            visibility: value.visibility.into(),
            annotation_type: parse_annotation_type(&value.annotation.annotation_type)?,
            elements: value
                .annotation
                .elements
                .iter()
                .map(|element| {
                    Ok(AnnotationElement {
                        name: element.name.clone(),
                        value: DexValue::try_from(&element.value)?,
                    })
                })
                .collect::<Result<Vec<_>, MetadataConversionError>>()?,
        })
    }
}

impl TryFrom<&rusty_dex::dex::encoded_value::EncodedAnnotation> for AnnotationNode {
    type Error = MetadataConversionError;

    fn try_from(
        value: &rusty_dex::dex::encoded_value::EncodedAnnotation,
    ) -> Result<Self, Self::Error> {
        Ok(Self {
            visibility: AnnotationVisibility::Runtime,
            annotation_type: parse_annotation_type(&value.annotation_type)?,
            elements: value
                .elements
                .iter()
                .map(|element| {
                    Ok(AnnotationElement {
                        name: element.name.clone(),
                        value: DexValue::try_from(&element.value)?,
                    })
                })
                .collect::<Result<Vec<_>, MetadataConversionError>>()?,
        })
    }
}

impl TryFrom<&rusty_dex::dex::encoded_value::EncodedValue> for DexValue {
    type Error = MetadataConversionError;

    fn try_from(value: &rusty_dex::dex::encoded_value::EncodedValue) -> Result<Self, Self::Error> {
        use rusty_dex::dex::encoded_value::EncodedValue;
        Ok(match value {
            EncodedValue::Byte(value) => Self::Byte(*value),
            EncodedValue::Short(value) => Self::Short(*value),
            EncodedValue::Char(value) => Self::Char(*value),
            EncodedValue::Int(value) => Self::Int(*value),
            EncodedValue::Long(value) => Self::Long(*value),
            EncodedValue::Float(value) => Self::Float(*value),
            EncodedValue::Double(value) => Self::Double(*value),
            EncodedValue::MethodType(value) => {
                Self::MethodType(value.parse().map_err(|source| {
                    MetadataConversionError::MethodType {
                        descriptor: value.clone(),
                        source,
                    }
                })?)
            }
            EncodedValue::MethodHandle(index) => Self::Unsupported {
                value_type: 0x16,
                raw: u64::from(*index),
            },
            EncodedValue::Method(value) => {
                Self::Method(
                    value
                        .parse()
                        .map_err(|source| MetadataConversionError::Method {
                            reference: value.clone(),
                            source,
                        })?,
                )
            }
            EncodedValue::Field(value) => {
                Self::Field(
                    value
                        .parse()
                        .map_err(|source| MetadataConversionError::Field {
                            reference: value.clone(),
                            source,
                        })?,
                )
            }
            EncodedValue::Enum(value) => {
                Self::Enum(
                    value
                        .parse()
                        .map_err(|source| MetadataConversionError::Field {
                            reference: value.clone(),
                            source,
                        })?,
                )
            }
            EncodedValue::String(value) => {
                Self::String(Utf16String::from_utf16(value.utf16().to_vec()))
            }
            EncodedValue::Type(value) => Self::Type(parse_annotation_type(value)?),
            EncodedValue::Array(values) => Self::Array(
                values
                    .iter()
                    .map(DexValue::try_from)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            EncodedValue::Annotation(annotation) => {
                Self::Annotation(Box::new(AnnotationNode::try_from(annotation)?))
            }
            EncodedValue::Null => Self::Null,
            EncodedValue::Boolean(value) => Self::Boolean(*value),
            EncodedValue::Unsupported { value_type, raw } => Self::Unsupported {
                value_type: *value_type,
                raw: *raw,
            },
        })
    }
}

fn parse_annotation_type(descriptor: &str) -> Result<ArgType, MetadataConversionError> {
    descriptor
        .parse::<ArgType>()
        .map_err(|source| MetadataConversionError::Type {
            descriptor: descriptor.to_string(),
            source,
        })
}

fn is_dalvik_system_annotation(ty: &ArgType) -> bool {
    let descriptor = ty.to_descriptor();
    matches!(
        descriptor.as_str(),
        "Ldalvik/annotation/AnnotationDefault;"
            | "Ldalvik/annotation/EnclosingClass;"
            | "Ldalvik/annotation/EnclosingMethod;"
            | "Ldalvik/annotation/InnerClass;"
            | "Ldalvik/annotation/MemberClasses;"
            | "Ldalvik/annotation/Signature;"
            | "Ldalvik/annotation/Throws;"
    )
}
