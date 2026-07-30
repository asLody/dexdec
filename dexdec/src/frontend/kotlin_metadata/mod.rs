//! Decoding of the `@kotlin.Metadata` annotation.
//!
//! A Kotlin class compiles to bytecode that cannot express what its source said:
//! nullability, `val` against `var`, `internal` visibility, parameter names and
//! default arguments all disappear. The compiler therefore attaches the original
//! declarations to every class it emits, and reading them recovers facts that no
//! amount of analysis over the DEX could prove.

mod encoding;
mod names;
mod schema;
mod wire;

use encoding::{BitEncoding, EncodingError};
use names::NameResolver;
use wire::{Message, WireError, WireReader};

pub use schema::{
    ClassKind, Constructor, DeclarationFlags, Declarations, Function, JvmSignature, Property,
    TypeReference, ValueParameter, Visibility,
};

use super::metadata::{AnnotationNode, DexValue};
use crate::ir::ArgType;

/// What the annotation says its class is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetadataKind {
    Class,
    FileFacade,
    SyntheticClass,
    MultiFileClassFacade,
    MultiFileClassPart,
}

impl MetadataKind {
    fn of(value: i32) -> Option<Self> {
        match value {
            1 => Some(Self::Class),
            2 => Some(Self::FileFacade),
            3 => Some(Self::SyntheticClass),
            4 => Some(Self::MultiFileClassFacade),
            5 => Some(Self::MultiFileClassPart),
            _ => None,
        }
    }

    /// Whether the declaration table describes members of this class.
    ///
    /// A synthetic class carries no declarations of its own, and a multi-file
    /// facade only lists the parts it merges.
    fn carries_declarations(self) -> bool {
        matches!(
            self,
            Self::Class | Self::FileFacade | Self::MultiFileClassPart
        )
    }
}

#[derive(Debug, Clone)]
pub enum MetadataError {
    Encoding(EncodingError),
    Wire(WireError),
    UnsupportedVersion([i32; 3]),
}

impl std::fmt::Display for MetadataError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Encoding(source) => write!(formatter, "kotlin metadata encoding: {source}"),
            Self::Wire(source) => write!(formatter, "kotlin metadata: {source}"),
            Self::UnsupportedVersion([major, minor, patch]) => write!(
                formatter,
                "kotlin metadata version {major}.{minor}.{patch} is newer than this reader"
            ),
        }
    }
}

impl std::error::Error for MetadataError {}

impl From<EncodingError> for MetadataError {
    fn from(source: EncodingError) -> Self {
        Self::Encoding(source)
    }
}

impl From<WireError> for MetadataError {
    fn from(source: WireError) -> Self {
        Self::Wire(source)
    }
}

/// The declarations one class was compiled from.
pub struct KotlinMetadata {
    kind: MetadataKind,
    version: [i32; 3],
    declarations: Declarations,
}

impl KotlinMetadata {
    /// The annotation type the compiler writes.
    const ANNOTATION: &'static str = "kotlin/Metadata";

    /// The highest metadata version whose layout this reader was written for.
    ///
    /// Kotlin promises that a reader may keep reading later minor versions, so
    /// only a new major version is refused.
    const SUPPORTED_MAJOR: i32 = 2;

    pub fn is_metadata(annotation: &AnnotationNode) -> bool {
        matches!(&annotation.annotation_type, ArgType::Object(name) if name == Self::ANNOTATION)
    }

    /// Reads the metadata attached to a declaration, if it carries any.
    pub fn of(annotations: &[AnnotationNode]) -> Option<Result<Self, MetadataError>> {
        annotations
            .iter()
            .find(|annotation| Self::is_metadata(annotation))
            .map(Self::decode)
    }

    pub fn kind(&self) -> MetadataKind {
        self.kind
    }

    pub fn version(&self) -> [i32; 3] {
        self.version
    }

    pub fn declarations(&self) -> &Declarations {
        &self.declarations
    }

    fn decode(annotation: &AnnotationNode) -> Result<Self, MetadataError> {
        let kind = Self::integer(annotation, "k")
            .and_then(MetadataKind::of)
            .unwrap_or(MetadataKind::Class);
        let version = Self::version_of(annotation);
        if version[0] > Self::SUPPORTED_MAJOR {
            return Err(MetadataError::UnsupportedVersion(version));
        }
        if !kind.carries_declarations() {
            return Ok(Self {
                kind,
                version,
                declarations: Declarations::default(),
            });
        }
        let data = Self::string_array(annotation, "d1");
        let strings = Self::string_array(annotation, "d2")
            .iter()
            .map(|units| String::from_utf16_lossy(units))
            .collect::<Vec<_>>();
        let bytes = BitEncoding::decode(&data)?;

        // The stream is a length-delimited name table followed by the
        // declarations, exactly as Kotlin's writer emits them.
        let mut reader = WireReader::new(&bytes);
        let table = Message::parse(reader.delimited()?)?;
        let names = NameResolver::new(&table, strings)?;
        let body = Message::parse(reader.remainder())?;
        let declarations = match kind {
            MetadataKind::Class => Declarations::class(&body, &names)?,
            _ => Declarations::package(&body, &names)?,
        };
        Ok(Self {
            kind,
            version,
            declarations,
        })
    }

    fn version_of(annotation: &AnnotationNode) -> [i32; 3] {
        let mut version = [0i32; 3];
        let Some(DexValue::Array(values)) = Self::element(annotation, "mv") else {
            return version;
        };
        for (slot, value) in version.iter_mut().zip(values) {
            if let DexValue::Int(value) = value {
                *slot = *value;
            }
        }
        version
    }

    fn element<'a>(annotation: &'a AnnotationNode, name: &str) -> Option<&'a DexValue> {
        annotation
            .elements
            .iter()
            .find(|element| element.name == name)
            .map(|element| &element.value)
    }

    fn integer(annotation: &AnnotationNode, name: &str) -> Option<i32> {
        match Self::element(annotation, name) {
            Some(DexValue::Int(value)) => Some(*value),
            _ => None,
        }
    }

    fn string_array(annotation: &AnnotationNode, name: &str) -> Vec<Vec<u16>> {
        let Some(DexValue::Array(values)) = Self::element(annotation, name) else {
            return Vec::new();
        };
        values
            .iter()
            .filter_map(|value| match value {
                DexValue::String(text) => Some(text.as_utf16().to_vec()),
                _ => None,
            })
            .collect()
    }
}
