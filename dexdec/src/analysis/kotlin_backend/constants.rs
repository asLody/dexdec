use crate::frontend::{AnnotationNode, DexValue};
use crate::ir::ty::ArgType;
use crate::language::kotlin::{
    KotlinAnnotation, KotlinAnnotationElement, KotlinAnnotationValue, KotlinExpr, KotlinIdentifier,
    KotlinLiteral, KotlinMemberNames,
};

use super::type_names::{KotlinTypeNameError, KotlinTypeNameResolver};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KotlinConstantError {
    TypeName(KotlinTypeNameError),
    Unsupported { value_type: u8, raw: u64 },
    InvalidAnnotationValue(&'static str),
    InvalidFieldValue(&'static str),
    InvalidNullType(ArgType),
}

impl std::fmt::Display for KotlinConstantError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeName(source) => source.fmt(formatter),
            Self::Unsupported { value_type, raw } => write!(
                formatter,
                "DEX value type 0x{value_type:x} with payload {raw} has no Kotlin source form"
            ),
            Self::InvalidAnnotationValue(kind) => {
                write!(formatter, "{kind} is not a legal Kotlin annotation value")
            }
            Self::InvalidFieldValue(kind) => {
                write!(formatter, "{kind} is not a legal Kotlin field initializer")
            }
            Self::InvalidNullType(ty) => {
                write!(formatter, "null cannot initialize Kotlin type {ty}")
            }
        }
    }
}

impl std::error::Error for KotlinConstantError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::TypeName(source) => Some(source),
            _ => None,
        }
    }
}

impl From<KotlinTypeNameError> for KotlinConstantError {
    fn from(source: KotlinTypeNameError) -> Self {
        Self::TypeName(source)
    }
}

pub(super) struct KotlinConstantLowering<'a> {
    names: &'a KotlinTypeNameResolver,
    members: &'a KotlinMemberNames,
}

impl<'a> KotlinConstantLowering<'a> {
    pub(super) fn new(names: &'a KotlinTypeNameResolver, members: &'a KotlinMemberNames) -> Self {
        Self { names, members }
    }

    pub(super) fn annotations(
        &self,
        annotations: &[AnnotationNode],
    ) -> Result<Vec<KotlinAnnotation>, KotlinConstantError> {
        annotations
            .iter()
            // The Kotlin compiler recreates this transport annotation from the
            // source declarations. Emitting its encoded protobuf as a source
            // annotation is redundant and can preserve stale metadata.
            .filter(|annotation| {
                !crate::frontend::kotlin_metadata::KotlinMetadata::is_metadata(annotation)
            })
            .map(|annotation| self.annotation(annotation))
            .collect()
    }

    pub(super) fn annotation(
        &self,
        annotation: &AnnotationNode,
    ) -> Result<KotlinAnnotation, KotlinConstantError> {
        if annotation.annotation_type.as_object() == Some("java/lang/Deprecated")
            && annotation.elements.is_empty()
        {
            return Ok(KotlinAnnotation {
                ty: self.names.resolve_type(&annotation.annotation_type)?,
                elements: vec![KotlinAnnotationElement {
                    name: KotlinIdentifier::from_dex("message"),
                    value: KotlinAnnotationValue::Expression(KotlinExpr::Literal(
                        KotlinLiteral::String("Deprecated in Java".into()),
                    )),
                }],
            });
        }
        Ok(KotlinAnnotation {
            ty: self.names.resolve_type(&annotation.annotation_type)?,
            elements: annotation
                .elements
                .iter()
                .map(|element| {
                    Ok(KotlinAnnotationElement {
                        name: KotlinIdentifier::from_dex(&element.name),
                        value: self.annotation_value(&element.value)?,
                    })
                })
                .collect::<Result<Vec<_>, KotlinConstantError>>()?,
        })
    }

    pub(super) fn field_initializer(
        &self,
        field_type: &ArgType,
        value: &DexValue,
    ) -> Result<KotlinExpr, KotlinConstantError> {
        use crate::ir::PrimitiveType;

        Ok(match value {
            DexValue::Null => {
                if !matches!(field_type, ArgType::Object(_) | ArgType::Array(_)) {
                    return Err(KotlinConstantError::InvalidNullType(field_type.clone()));
                }
                KotlinExpr::Literal(KotlinLiteral::Null)
            }
            DexValue::Boolean(value) => KotlinExpr::Literal(KotlinLiteral::Boolean(*value)),
            DexValue::Byte(value) => KotlinExpr::Literal(KotlinLiteral::Integer(i32::from(*value))),
            DexValue::Short(value) => {
                KotlinExpr::Literal(KotlinLiteral::Integer(i32::from(*value)))
            }
            DexValue::Char(value) => KotlinExpr::Literal(KotlinLiteral::Character(*value)),
            DexValue::Int(value) => match field_type.as_primitive() {
                Some(PrimitiveType::Boolean) => {
                    KotlinExpr::Literal(KotlinLiteral::Boolean(*value != 0))
                }
                Some(PrimitiveType::Char) => {
                    KotlinExpr::Literal(KotlinLiteral::Character(*value as u16))
                }
                _ => KotlinExpr::Literal(KotlinLiteral::Integer(*value)),
            },
            DexValue::Long(value) => KotlinExpr::Literal(KotlinLiteral::Long(*value)),
            DexValue::Float(value) => KotlinExpr::Literal(KotlinLiteral::Float(*value)),
            DexValue::Double(value) => KotlinExpr::Literal(KotlinLiteral::Double(*value)),
            DexValue::String(value) => KotlinExpr::Literal(KotlinLiteral::String(value.clone())),
            DexValue::Type(ty) => KotlinExpr::ClassLiteral(self.names.resolve_type(ty)?),
            DexValue::Enum(field) => KotlinExpr::StaticField {
                owner: self.names.resolve_type(&field.owner)?,
                name: self.members.field(field),
            },
            DexValue::Field(_) => {
                return Err(KotlinConstantError::InvalidFieldValue("field reference"));
            }
            DexValue::Method(_) => {
                return Err(KotlinConstantError::InvalidFieldValue("method reference"));
            }
            DexValue::MethodType(_) => {
                return Err(KotlinConstantError::InvalidFieldValue("method type"));
            }
            DexValue::Array(_) => return Err(KotlinConstantError::InvalidFieldValue("array")),
            DexValue::Annotation(_) => {
                return Err(KotlinConstantError::InvalidFieldValue("annotation"));
            }
            DexValue::Unsupported { value_type, raw } => {
                return Err(KotlinConstantError::Unsupported {
                    value_type: *value_type,
                    raw: *raw,
                });
            }
        })
    }

    fn annotation_value(
        &self,
        value: &DexValue,
    ) -> Result<KotlinAnnotationValue, KotlinConstantError> {
        Ok(match value {
            DexValue::Null => {
                return Err(KotlinConstantError::InvalidAnnotationValue("null"));
            }
            DexValue::Boolean(value) => Self::expression(KotlinLiteral::Boolean(*value)),
            DexValue::Byte(value) => Self::expression(KotlinLiteral::Integer(i32::from(*value))),
            DexValue::Short(value) => Self::expression(KotlinLiteral::Integer(i32::from(*value))),
            DexValue::Char(value) => Self::expression(KotlinLiteral::Character(*value)),
            DexValue::Int(value) => Self::expression(KotlinLiteral::Integer(*value)),
            DexValue::Long(value) => Self::expression(KotlinLiteral::Long(*value)),
            DexValue::Float(value) => Self::expression(KotlinLiteral::Float(*value)),
            DexValue::Double(value) => Self::expression(KotlinLiteral::Double(*value)),
            DexValue::String(value) => Self::expression(KotlinLiteral::String(value.clone())),
            DexValue::Type(ty) => KotlinAnnotationValue::Expression(KotlinExpr::ClassLiteral(
                self.names.resolve_type(ty)?,
            )),
            DexValue::Enum(field) => KotlinAnnotationValue::Expression(KotlinExpr::StaticField {
                owner: self.names.resolve_type(&field.owner)?,
                name: self.members.field(field),
            }),
            DexValue::Array(values) => KotlinAnnotationValue::Array(
                values
                    .iter()
                    .map(|value| self.annotation_value(value))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            DexValue::Annotation(annotation) => {
                KotlinAnnotationValue::Annotation(Box::new(self.annotation(annotation)?))
            }
            DexValue::Field(_) => {
                return Err(KotlinConstantError::InvalidAnnotationValue(
                    "field reference",
                ));
            }
            DexValue::Method(_) => {
                return Err(KotlinConstantError::InvalidAnnotationValue(
                    "method reference",
                ));
            }
            DexValue::MethodType(_) => {
                return Err(KotlinConstantError::InvalidAnnotationValue("method type"));
            }
            DexValue::Unsupported { value_type, raw } => {
                return Err(KotlinConstantError::Unsupported {
                    value_type: *value_type,
                    raw: *raw,
                });
            }
        })
    }

    fn expression(literal: KotlinLiteral) -> KotlinAnnotationValue {
        KotlinAnnotationValue::Expression(KotlinExpr::Literal(literal))
    }
}
