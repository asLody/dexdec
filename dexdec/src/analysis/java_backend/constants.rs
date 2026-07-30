use crate::frontend::{AnnotationNode, DexValue};
use crate::ir::ty::ArgType;
use crate::language::java::{
    JavaAnnotation, JavaAnnotationElement, JavaAnnotationValue, JavaExpr, JavaIdentifier,
    JavaLiteral, JavaMemberNames,
};

use super::type_names::{JavaTypeNameError, JavaTypeNameResolver};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JavaConstantError {
    TypeName(JavaTypeNameError),
    Unsupported { value_type: u8, raw: u64 },
    InvalidAnnotationValue(&'static str),
    InvalidFieldValue(&'static str),
    InvalidNullType(ArgType),
}

impl std::fmt::Display for JavaConstantError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeName(source) => source.fmt(formatter),
            Self::Unsupported { value_type, raw } => write!(
                formatter,
                "DEX value type 0x{value_type:x} with payload {raw} has no Java source form"
            ),
            Self::InvalidAnnotationValue(kind) => {
                write!(formatter, "{kind} is not a legal Java annotation value")
            }
            Self::InvalidFieldValue(kind) => {
                write!(formatter, "{kind} is not a legal Java field initializer")
            }
            Self::InvalidNullType(ty) => write!(formatter, "null cannot initialize Java type {ty}"),
        }
    }
}

impl std::error::Error for JavaConstantError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::TypeName(source) => Some(source),
            _ => None,
        }
    }
}

impl From<JavaTypeNameError> for JavaConstantError {
    fn from(source: JavaTypeNameError) -> Self {
        Self::TypeName(source)
    }
}

pub(super) struct JavaConstantLowering<'a> {
    names: &'a JavaTypeNameResolver,
    members: &'a JavaMemberNames,
}

impl<'a> JavaConstantLowering<'a> {
    pub(super) fn new(names: &'a JavaTypeNameResolver, members: &'a JavaMemberNames) -> Self {
        Self { names, members }
    }

    pub(super) fn annotations(
        &self,
        annotations: &[AnnotationNode],
    ) -> Result<Vec<JavaAnnotation>, JavaConstantError> {
        annotations
            .iter()
            .map(|annotation| self.annotation(annotation))
            .collect()
    }

    pub(super) fn annotation(
        &self,
        annotation: &AnnotationNode,
    ) -> Result<JavaAnnotation, JavaConstantError> {
        Ok(JavaAnnotation {
            ty: self.names.resolve_type(&annotation.annotation_type)?,
            elements: annotation
                .elements
                .iter()
                .map(|element| {
                    Ok(JavaAnnotationElement {
                        name: JavaIdentifier::from_dex(&element.name),
                        value: self.annotation_value(&element.value)?,
                    })
                })
                .collect::<Result<Vec<_>, JavaConstantError>>()?,
        })
    }

    pub(super) fn field_initializer(
        &self,
        field_type: &ArgType,
        value: &DexValue,
    ) -> Result<JavaExpr, JavaConstantError> {
        use crate::ir::PrimitiveType;

        Ok(match value {
            DexValue::Null => {
                if !matches!(field_type, ArgType::Object(_) | ArgType::Array(_)) {
                    return Err(JavaConstantError::InvalidNullType(field_type.clone()));
                }
                JavaExpr::Literal(JavaLiteral::Null)
            }
            DexValue::Boolean(value) => JavaExpr::Literal(JavaLiteral::Boolean(*value)),
            DexValue::Byte(value) => JavaExpr::Literal(JavaLiteral::Integer(i32::from(*value))),
            DexValue::Short(value) => JavaExpr::Literal(JavaLiteral::Integer(i32::from(*value))),
            DexValue::Char(value) => JavaExpr::Literal(JavaLiteral::Character(*value)),
            DexValue::Int(value) => match field_type.as_primitive() {
                Some(PrimitiveType::Boolean) => {
                    JavaExpr::Literal(JavaLiteral::Boolean(*value != 0))
                }
                Some(PrimitiveType::Char) => {
                    JavaExpr::Literal(JavaLiteral::Character(*value as u16))
                }
                _ => JavaExpr::Literal(JavaLiteral::Integer(*value)),
            },
            DexValue::Long(value) => JavaExpr::Literal(JavaLiteral::Long(*value)),
            DexValue::Float(value) => JavaExpr::Literal(JavaLiteral::Float(*value)),
            DexValue::Double(value) => JavaExpr::Literal(JavaLiteral::Double(*value)),
            DexValue::String(value) => JavaExpr::Literal(JavaLiteral::String(value.clone())),
            DexValue::Type(ty) => JavaExpr::ClassLiteral(self.names.resolve_type(ty)?),
            DexValue::Enum(field) => JavaExpr::StaticField {
                owner: self.names.resolve_type(&field.owner)?,
                name: self.members.field(field),
            },
            DexValue::Field(_) => {
                return Err(JavaConstantError::InvalidFieldValue("field reference"));
            }
            DexValue::Method(_) => {
                return Err(JavaConstantError::InvalidFieldValue("method reference"));
            }
            DexValue::MethodType(_) => {
                return Err(JavaConstantError::InvalidFieldValue("method type"));
            }
            DexValue::Array(_) => return Err(JavaConstantError::InvalidFieldValue("array")),
            DexValue::Annotation(_) => {
                return Err(JavaConstantError::InvalidFieldValue("annotation"));
            }
            DexValue::Unsupported { value_type, raw } => {
                return Err(JavaConstantError::Unsupported {
                    value_type: *value_type,
                    raw: *raw,
                });
            }
        })
    }

    fn annotation_value(&self, value: &DexValue) -> Result<JavaAnnotationValue, JavaConstantError> {
        Ok(match value {
            DexValue::Null => {
                return Err(JavaConstantError::InvalidAnnotationValue("null"));
            }
            DexValue::Boolean(value) => Self::expression(JavaLiteral::Boolean(*value)),
            DexValue::Byte(value) => Self::expression(JavaLiteral::Integer(i32::from(*value))),
            DexValue::Short(value) => Self::expression(JavaLiteral::Integer(i32::from(*value))),
            DexValue::Char(value) => Self::expression(JavaLiteral::Character(*value)),
            DexValue::Int(value) => Self::expression(JavaLiteral::Integer(*value)),
            DexValue::Long(value) => Self::expression(JavaLiteral::Long(*value)),
            DexValue::Float(value) => Self::expression(JavaLiteral::Float(*value)),
            DexValue::Double(value) => Self::expression(JavaLiteral::Double(*value)),
            DexValue::String(value) => Self::expression(JavaLiteral::String(value.clone())),
            DexValue::Type(ty) => JavaAnnotationValue::Expression(JavaExpr::ClassLiteral(
                self.names.resolve_type(ty)?,
            )),
            DexValue::Enum(field) => JavaAnnotationValue::Expression(JavaExpr::StaticField {
                owner: self.names.resolve_type(&field.owner)?,
                name: self.members.field(field),
            }),
            DexValue::Array(values) => JavaAnnotationValue::Array(
                values
                    .iter()
                    .map(|value| self.annotation_value(value))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            DexValue::Annotation(annotation) => {
                JavaAnnotationValue::Annotation(Box::new(self.annotation(annotation)?))
            }
            DexValue::Field(_) => {
                return Err(JavaConstantError::InvalidAnnotationValue("field reference"));
            }
            DexValue::Method(_) => {
                return Err(JavaConstantError::InvalidAnnotationValue(
                    "method reference",
                ));
            }
            DexValue::MethodType(_) => {
                return Err(JavaConstantError::InvalidAnnotationValue("method type"));
            }
            DexValue::Unsupported { value_type, raw } => {
                return Err(JavaConstantError::Unsupported {
                    value_type: *value_type,
                    raw: *raw,
                });
            }
        })
    }

    fn expression(literal: JavaLiteral) -> JavaAnnotationValue {
        JavaAnnotationValue::Expression(JavaExpr::Literal(literal))
    }
}
