use crate::ir::{ArgType, MethodReference, PrimitiveType};

use super::{KotlinExpr, KotlinIdentifier};

/// Source forms provided by Kotlin for well-known JVM member contracts.
///
/// Rules are keyed by complete member identity. This keeps JVM-to-Kotlin
/// interop policy out of the printer and prevents unrelated methods with the
/// same spelling from being rewritten.
pub(super) struct KotlinJvmCallSyntax;

impl KotlinJvmCallSyntax {
    pub(super) fn lower(
        method: &MethodReference,
        receiver: Option<&KotlinExpr>,
        args: &[KotlinExpr],
        is_subtype: impl Fn(&ArgType, &ArgType) -> bool,
        uses_mapped_collection_size: impl Fn(&ArgType) -> bool,
    ) -> Option<KotlinExpr> {
        let owner = method.owner.as_object()?;
        match (
            owner,
            method.name.as_str(),
            method.descriptor.parameters.as_slice(),
            method.descriptor.return_type.as_primitive(),
            receiver,
            args,
        ) {
            (
                "java/lang/String" | "java/lang/CharSequence",
                "length",
                [],
                Some(PrimitiveType::Int),
                Some(receiver),
                [],
            ) => Some(KotlinExpr::Field {
                owner: Box::new(receiver.clone()),
                name: KotlinIdentifier::from_dex("length"),
            }),
            (
                "java/lang/String" | "java/lang/CharSequence",
                "charAt",
                [_],
                Some(PrimitiveType::Char),
                Some(receiver),
                [index],
            ) => Some(KotlinExpr::ArrayAccess {
                array: Box::new(receiver.clone()),
                index: Box::new(index.clone()),
            }),
            (
                "java/lang/String",
                method @ ("indexOf" | "lastIndexOf"),
                [ArgType::Primitive(PrimitiveType::Int)],
                Some(PrimitiveType::Int),
                Some(receiver),
                [character],
            ) => Some(KotlinExpr::Call {
                receiver: Some(Box::new(receiver.clone())),
                owner: None,
                type_arguments: Vec::new(),
                method: KotlinIdentifier::from_dex(method),
                args: vec![KotlinExpr::Cast {
                    ty: super::KotlinType::Primitive(super::KotlinPrimitiveType::Char),
                    value: Box::new(character.clone()),
                }]
                .into(),
            }),
            (
                "java/lang/String",
                method @ ("indexOf" | "lastIndexOf"),
                [ArgType::Primitive(PrimitiveType::Int), ArgType::Primitive(PrimitiveType::Int)],
                Some(PrimitiveType::Int),
                Some(receiver),
                [character, start],
            ) => Some(KotlinExpr::Call {
                receiver: Some(Box::new(receiver.clone())),
                owner: None,
                type_arguments: Vec::new(),
                method: KotlinIdentifier::from_dex(method),
                args: vec![
                    KotlinExpr::Cast {
                        ty: super::KotlinType::Primitive(super::KotlinPrimitiveType::Char),
                        value: Box::new(character.clone()),
                    },
                    start.clone(),
                ]
                .into(),
            }),
            ("java/lang/String", "valueOf", [ArgType::Array(element)], _, None, [chars])
                if element.as_ref() == &ArgType::CHAR
                    && method.descriptor.return_type.as_object() == Some("java/lang/String") =>
            {
                Some(KotlinExpr::Call {
                    receiver: Some(Box::new(chars.clone())),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: KotlinIdentifier::from_dex("concatToString"),
                    args: Vec::new().into(),
                })
            }
            _ if method.name == "size"
                && method.descriptor.parameters.is_empty()
                && method.descriptor.return_type == ArgType::INT
                && receiver.is_some()
                && (Self::is_collection_owner(&method.owner, &is_subtype)
                    || uses_mapped_collection_size(&method.owner)) =>
            {
                Some(KotlinExpr::Field {
                    owner: Box::new(receiver?.clone()),
                    name: KotlinIdentifier::from_dex("size"),
                })
            }
            _ if method.name == "get"
                && method.descriptor.parameters.as_slice() == [ArgType::INT]
                && method.descriptor.return_type.is_reference()
                && receiver.is_some()
                && Self::is_list_owner(&method.owner, &is_subtype) =>
            {
                Some(KotlinExpr::ArrayAccess {
                    array: Box::new(receiver?.clone()),
                    index: Box::new(args.first()?.clone()),
                })
            }
            _ if method.name == "remove"
                && method.descriptor.parameters.as_slice() == [ArgType::INT]
                && method.descriptor.return_type.is_reference()
                && receiver.is_some()
                && Self::is_list_owner(&method.owner, &is_subtype) =>
            {
                Some(KotlinExpr::Call {
                    receiver: Some(Box::new(receiver?.clone())),
                    owner: None,
                    type_arguments: Vec::new(),
                    method: KotlinIdentifier::from_dex("removeAt"),
                    args: args.to_vec().into(),
                })
            }
            _ => None,
        }
    }

    fn is_collection_owner(
        owner: &ArgType,
        is_subtype: &impl Fn(&ArgType, &ArgType) -> bool,
    ) -> bool {
        [
            ArgType::object("java/util/Collection"),
            ArgType::object("java/util/Map"),
        ]
        .iter()
        .any(|contract| owner == contract || is_subtype(owner, contract))
    }

    fn is_list_owner(owner: &ArgType, is_subtype: &impl Fn(&ArgType, &ArgType) -> bool) -> bool {
        let list = ArgType::object("java/util/List");
        owner == &list || is_subtype(owner, &list)
    }
}
