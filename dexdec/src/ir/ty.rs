//! Type System
//!
//! This module defines the type system for IR, inspired by jadx's ArgType.
//!
//! ## Type Hierarchy
//!
//! - Primitive types (int, long, float, double, etc.)
//! - Object types (Ljava/lang/String;)
//! - Array types ([I, [Ljava/lang/Object;)
//! - Unknown types (used during type inference)

use std::{fmt, str::FromStr};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DescriptorParseError {
    UnexpectedEnd { offset: usize },
    UnexpectedByte { offset: usize, byte: u8 },
    VoidNotAllowed { offset: usize },
    EmptyObject { offset: usize },
    TrailingInput { offset: usize },
    MissingMethodStart,
    MissingMethodEnd { offset: usize },
}

impl fmt::Display for DescriptorParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEnd { offset } => {
                write!(formatter, "unexpected end of descriptor at {offset}")
            }
            Self::UnexpectedByte { offset, byte } => write!(
                formatter,
                "unexpected descriptor byte 0x{byte:02x} at {offset}"
            ),
            Self::VoidNotAllowed { offset } => {
                write!(formatter, "void type is not allowed at {offset}")
            }
            Self::EmptyObject { offset } => {
                write!(formatter, "empty object descriptor at {offset}")
            }
            Self::TrailingInput { offset } => {
                write!(formatter, "trailing descriptor input at {offset}")
            }
            Self::MissingMethodStart => {
                formatter.write_str("method descriptor must start with '('")
            }
            Self::MissingMethodEnd { offset } => {
                write!(formatter, "method parameter list is not closed at {offset}")
            }
        }
    }
}

impl std::error::Error for DescriptorParseError {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MethodDescriptor {
    pub parameters: Vec<ArgType>,
    pub return_type: ArgType,
}

impl FromStr for MethodDescriptor {
    type Err = DescriptorParseError;

    fn from_str(descriptor: &str) -> Result<Self, Self::Err> {
        let mut parser = DescriptorParser::new(descriptor);
        if !parser.consume(b'(') {
            return Err(DescriptorParseError::MissingMethodStart);
        }
        let mut parameters = Vec::new();
        while parser.peek() != Some(b')') {
            if parser.peek().is_none() {
                return Err(DescriptorParseError::MissingMethodEnd {
                    offset: parser.offset,
                });
            }
            parameters.push(parser.ty(false)?);
        }
        parser.offset += 1;
        let return_type = parser.ty(true)?;
        parser.finish()?;
        Ok(Self {
            parameters,
            return_type,
        })
    }
}

impl fmt::Display for MethodDescriptor {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("(")?;
        for parameter in &self.parameters {
            formatter.write_str(&parameter.to_descriptor())?;
        }
        write!(formatter, "){}", self.return_type.to_descriptor())
    }
}

struct DescriptorParser<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl FromStr for ArgType {
    type Err = DescriptorParseError;

    fn from_str(descriptor: &str) -> Result<Self, Self::Err> {
        let mut parser = DescriptorParser::new(descriptor);
        let ty = parser.ty(true)?;
        parser.finish()?;
        Ok(ty)
    }
}

impl<'a> DescriptorParser<'a> {
    fn new(descriptor: &'a str) -> Self {
        Self {
            bytes: descriptor.as_bytes(),
            offset: 0,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.offset).copied()
    }

    fn consume(&mut self, expected: u8) -> bool {
        if self.peek() != Some(expected) {
            return false;
        }
        self.offset += 1;
        true
    }

    fn ty(&mut self, allow_void: bool) -> Result<ArgType, DescriptorParseError> {
        let start = self.offset;
        let byte = self.peek().ok_or(DescriptorParseError::UnexpectedEnd {
            offset: self.offset,
        })?;
        self.offset += 1;
        Ok(match byte {
            b'V' if allow_void => ArgType::VOID,
            b'V' => return Err(DescriptorParseError::VoidNotAllowed { offset: start }),
            b'Z' => ArgType::BOOLEAN,
            b'B' => ArgType::BYTE,
            b'S' => ArgType::SHORT,
            b'C' => ArgType::CHAR,
            b'I' => ArgType::INT,
            b'J' => ArgType::LONG,
            b'F' => ArgType::FLOAT,
            b'D' => ArgType::DOUBLE,
            b'[' => ArgType::array(self.ty(false)?),
            b'L' => {
                let name_start = self.offset;
                let Some(relative_end) = self.bytes[name_start..]
                    .iter()
                    .position(|byte| *byte == b';')
                else {
                    return Err(DescriptorParseError::UnexpectedEnd {
                        offset: self.bytes.len(),
                    });
                };
                if relative_end == 0 {
                    return Err(DescriptorParseError::EmptyObject { offset: start });
                }
                let end = name_start + relative_end;
                let name = std::str::from_utf8(&self.bytes[name_start..end]).map_err(|error| {
                    DescriptorParseError::UnexpectedByte {
                        offset: name_start + error.valid_up_to(),
                        byte: self.bytes[name_start + error.valid_up_to()],
                    }
                })?;
                self.offset = end + 1;
                ArgType::Object(name.to_string())
            }
            byte => {
                return Err(DescriptorParseError::UnexpectedByte {
                    offset: start,
                    byte,
                });
            }
        })
    }

    fn finish(&self) -> Result<(), DescriptorParseError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(DescriptorParseError::TrailingInput {
                offset: self.offset,
            })
        }
    }
}

/// Primitive types in Dalvik/Kotlin
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveType {
    Void,
    Boolean,
    Byte,
    Short,
    Char,
    Int,
    Long,
    Float,
    Double,
    Object,
    Array,
}

impl PrimitiveType {
    /// Check if this is a wide type (takes 2 registers)
    pub fn is_wide(&self) -> bool {
        matches!(self, PrimitiveType::Long | PrimitiveType::Double)
    }

    /// Get the type descriptor character
    pub fn descriptor(&self) -> char {
        match self {
            PrimitiveType::Void => 'V',
            PrimitiveType::Boolean => 'Z',
            PrimitiveType::Byte => 'B',
            PrimitiveType::Short => 'S',
            PrimitiveType::Char => 'C',
            PrimitiveType::Int => 'I',
            PrimitiveType::Long => 'J',
            PrimitiveType::Float => 'F',
            PrimitiveType::Double => 'D',
            PrimitiveType::Object => 'L',
            PrimitiveType::Array => '[',
        }
    }

    /// Parse from type descriptor character
    pub fn from_descriptor(c: char) -> Option<Self> {
        match c {
            'V' => Some(PrimitiveType::Void),
            'Z' => Some(PrimitiveType::Boolean),
            'B' => Some(PrimitiveType::Byte),
            'S' => Some(PrimitiveType::Short),
            'C' => Some(PrimitiveType::Char),
            'I' => Some(PrimitiveType::Int),
            'J' => Some(PrimitiveType::Long),
            'F' => Some(PrimitiveType::Float),
            'D' => Some(PrimitiveType::Double),
            'L' => Some(PrimitiveType::Object),
            '[' => Some(PrimitiveType::Array),
            _ => None,
        }
    }
}

/// Argument type - represents the type of an instruction argument
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArgType {
    /// Primitive type
    Primitive(PrimitiveType),

    /// Object type with class name (e.g., "java/lang/String")
    Object(String),

    /// Array type with element type
    Array(Box<ArgType>),

    /// Unknown type (one of the possible types)
    Unknown(Vec<PrimitiveType>),
}

impl ArgType {
    // ==================== Common Type Constants ====================

    pub const VOID: ArgType = ArgType::Primitive(PrimitiveType::Void);
    pub const BOOLEAN: ArgType = ArgType::Primitive(PrimitiveType::Boolean);
    pub const BYTE: ArgType = ArgType::Primitive(PrimitiveType::Byte);
    pub const SHORT: ArgType = ArgType::Primitive(PrimitiveType::Short);
    pub const CHAR: ArgType = ArgType::Primitive(PrimitiveType::Char);
    pub const INT: ArgType = ArgType::Primitive(PrimitiveType::Int);
    pub const LONG: ArgType = ArgType::Primitive(PrimitiveType::Long);
    pub const FLOAT: ArgType = ArgType::Primitive(PrimitiveType::Float);
    pub const DOUBLE: ArgType = ArgType::Primitive(PrimitiveType::Double);

    /// Unknown narrow type (int, float, boolean, short, byte, char, object, array)
    pub fn narrow() -> ArgType {
        ArgType::Unknown(vec![
            PrimitiveType::Int,
            PrimitiveType::Float,
            PrimitiveType::Boolean,
            PrimitiveType::Short,
            PrimitiveType::Byte,
            PrimitiveType::Char,
            PrimitiveType::Object,
            PrimitiveType::Array,
        ])
    }

    /// Unknown wide type (long, double)
    pub fn wide() -> ArgType {
        ArgType::Unknown(vec![PrimitiveType::Long, PrimitiveType::Double])
    }

    /// Unknown object type (object or array)
    pub fn unknown_object() -> ArgType {
        ArgType::Unknown(vec![PrimitiveType::Object, PrimitiveType::Array])
    }

    /// DEX equality operands may be integral values, references, or null.
    pub fn equality_operand() -> ArgType {
        ArgType::Unknown(vec![
            PrimitiveType::Int,
            PrimitiveType::Boolean,
            PrimitiveType::Short,
            PrimitiveType::Byte,
            PrimitiveType::Char,
            PrimitiveType::Object,
            PrimitiveType::Array,
        ])
    }

    /// Any unknown type
    pub fn unknown() -> ArgType {
        ArgType::Unknown(vec![
            PrimitiveType::Int,
            PrimitiveType::Long,
            PrimitiveType::Float,
            PrimitiveType::Double,
            PrimitiveType::Boolean,
            PrimitiveType::Short,
            PrimitiveType::Byte,
            PrimitiveType::Char,
            PrimitiveType::Object,
            PrimitiveType::Array,
        ])
    }

    // ==================== Common Object Types ====================

    pub fn object(name: &str) -> ArgType {
        ArgType::Object(name.to_string())
    }

    pub fn string() -> ArgType {
        ArgType::Object("java/lang/String".to_string())
    }

    pub fn class() -> ArgType {
        ArgType::Object("java/lang/Class".to_string())
    }

    pub fn throwable() -> ArgType {
        ArgType::Object("java/lang/Throwable".to_string())
    }

    // ==================== Array Types ====================

    pub fn array(element: ArgType) -> ArgType {
        ArgType::Array(Box::new(element))
    }

    pub fn int_array() -> ArgType {
        ArgType::array(ArgType::INT)
    }

    pub fn object_array() -> ArgType {
        ArgType::array(ArgType::Object("java/lang/Object".to_string()))
    }

    // ==================== Type Queries ====================

    /// Check if this type is known (not Unknown)
    pub fn is_known(&self) -> bool {
        !matches!(self, ArgType::Unknown(_))
    }

    /// Check if this is a primitive type
    pub fn is_primitive(&self) -> bool {
        matches!(self, ArgType::Primitive(_))
    }

    /// Check if this is an object type
    pub fn is_object(&self) -> bool {
        matches!(self, ArgType::Object(_))
    }

    /// Check if this is an array type
    pub fn is_array(&self) -> bool {
        matches!(self, ArgType::Array(_))
    }

    /// Whether this is a concrete JVM reference type.
    pub fn is_reference(&self) -> bool {
        matches!(self, ArgType::Object(_) | ArgType::Array(_))
    }

    /// Check if this type takes 2 registers (wide)
    pub fn is_wide(&self) -> bool {
        match self {
            ArgType::Primitive(p) => p.is_wide(),
            ArgType::Unknown(types) => types.iter().all(|t| t.is_wide()),
            _ => false,
        }
    }

    /// Get the primitive type if this is a primitive
    pub fn as_primitive(&self) -> Option<PrimitiveType> {
        match self {
            ArgType::Primitive(p) => Some(*p),
            _ => None,
        }
    }

    /// Get the object class name if this is an object
    pub fn as_object(&self) -> Option<&str> {
        match self {
            ArgType::Object(name) => Some(name),
            _ => None,
        }
    }

    /// Get the array element type if this is an array
    pub fn as_array_element(&self) -> Option<&ArgType> {
        match self {
            ArgType::Array(elem) => Some(elem),
            _ => None,
        }
    }

    // ==================== Parsing ====================

    /// Convert to DEX type descriptor
    pub fn to_descriptor(&self) -> String {
        match self {
            ArgType::Primitive(p) => p.descriptor().to_string(),
            ArgType::Object(name) => format!("L{};", name),
            ArgType::Array(elem) => format!("[{}", elem.to_descriptor()),
            ArgType::Unknown(_) => "?".to_string(),
        }
    }
}

impl fmt::Display for ArgType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArgType::Primitive(PrimitiveType::Void) => write!(f, "void"),
            ArgType::Primitive(PrimitiveType::Boolean) => write!(f, "boolean"),
            ArgType::Primitive(PrimitiveType::Byte) => write!(f, "byte"),
            ArgType::Primitive(PrimitiveType::Short) => write!(f, "short"),
            ArgType::Primitive(PrimitiveType::Char) => write!(f, "char"),
            ArgType::Primitive(PrimitiveType::Int) => write!(f, "int"),
            ArgType::Primitive(PrimitiveType::Long) => write!(f, "long"),
            ArgType::Primitive(PrimitiveType::Float) => write!(f, "float"),
            ArgType::Primitive(PrimitiveType::Double) => write!(f, "double"),
            ArgType::Primitive(PrimitiveType::Object) => write!(f, "Object"),
            ArgType::Primitive(PrimitiveType::Array) => write!(f, "Array"),
            ArgType::Object(name) => {
                // Convert "java/lang/String" to "String"
                let short = name.rsplit('/').next().unwrap_or(name);
                write!(f, "{}", short)
            }
            ArgType::Array(elem) => write!(f, "{}[]", elem),
            ArgType::Unknown(types) => {
                if types.len() == 1 {
                    write!(f, "?{:?}", types[0])
                } else {
                    write!(f, "?")
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_primitive() {
        assert_eq!("I".parse::<ArgType>(), Ok(ArgType::INT));
        assert_eq!("J".parse::<ArgType>(), Ok(ArgType::LONG));
        assert_eq!("Z".parse::<ArgType>(), Ok(ArgType::BOOLEAN));
        assert_eq!("V".parse::<ArgType>(), Ok(ArgType::VOID));
    }

    #[test]
    fn test_parse_object() {
        let t = "Ljava/lang/String;".parse::<ArgType>().unwrap();
        assert!(t.is_object());
        assert_eq!(t.as_object(), Some("java/lang/String"));
    }

    #[test]
    fn test_parse_array() {
        let t = "[I".parse::<ArgType>().unwrap();
        assert!(t.is_array());
        assert_eq!(t.as_array_element(), Some(&ArgType::INT));

        let t2 = "[[Ljava/lang/Object;".parse::<ArgType>().unwrap();
        assert!(t2.is_array());
    }

    #[test]
    fn test_to_descriptor() {
        assert_eq!(ArgType::INT.to_descriptor(), "I");
        assert_eq!(ArgType::string().to_descriptor(), "Ljava/lang/String;");
        assert_eq!(ArgType::int_array().to_descriptor(), "[I");
    }

    #[test]
    fn test_is_wide() {
        assert!(ArgType::LONG.is_wide());
        assert!(ArgType::DOUBLE.is_wide());
        assert!(!ArgType::INT.is_wide());
        assert!(!ArgType::FLOAT.is_wide());
    }
}
