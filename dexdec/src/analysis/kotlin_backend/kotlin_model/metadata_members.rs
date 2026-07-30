//! One view of the members a Kotlin class declares in its own metadata.
//!
//! Functions, constructors and the accessors a property compiles to all reach
//! the DEX as methods, so every consumer needs the same three things: which DEX
//! method a declaration belongs to, and how its source parameters line up with
//! the ones that method actually takes.

use crate::frontend::kotlin_metadata::{Declarations, Property, TypeReference, Visibility};
use crate::frontend::MethodNode;

/// Where the fields backing a class's properties actually live.
///
/// A companion object's backing fields are emitted on the class that encloses
/// it, not on the companion, so a fact keyed only to the declaring class would
/// never match the field it describes.
pub(super) fn backing_field_owners(
    class: &crate::frontend::ClassNode,
    declarations: &Declarations,
) -> Vec<crate::ir::ArgType> {
    let owner = class.class_type().clone();
    if declarations.flags.class_kind()
        != crate::frontend::kotlin_metadata::ClassKind::CompanionObject
    {
        return vec![owner];
    }
    let enclosing = match &owner {
        crate::ir::ArgType::Object(name) => name
            .rsplit_once('$')
            .map(|(outer, _)| crate::ir::ArgType::object(outer)),
        _ => None,
    };
    enclosing
        .into_iter()
        .chain(std::iter::once(owner))
        .collect()
}

/// Resolves the DEX field that stores a Kotlin property.
///
/// Kotlin omits a property's JVM field signature when the default ABI is
/// sufficient. In that case the backing field has the source property name;
/// matching the sole field with that name is exact because Kotlin cannot
/// declare two properties of one class under the same name. An explicit JVM
/// signature always wins, including companion fields owned by the outer class.
pub(super) fn backing_field_references(
    class: &crate::frontend::ClassNode,
    declarations: &Declarations,
    property: &Property,
) -> Vec<crate::ir::FieldReference> {
    if let Some(field) = &property.field {
        let Ok(field_type) = field.descriptor.parse::<crate::ir::ArgType>() else {
            return Vec::new();
        };
        return backing_field_owners(class, declarations)
            .into_iter()
            .map(|owner| crate::ir::FieldReference {
                owner,
                name: field.name.clone(),
                field_type: field_type.clone(),
            })
            .collect();
    }

    let mut candidates = class
        .fields()
        .iter()
        .filter(|field| field.name() == property.name);
    let Some(field) = candidates.next() else {
        return Vec::new();
    };
    if candidates.next().is_some() {
        return Vec::new();
    }
    vec![crate::ir::FieldReference {
        owner: class.class_type().clone(),
        name: field.name().to_string(),
        field_type: field.field_type().clone(),
    }]
}

/// One source parameter, as the metadata records it.
pub(super) struct MetadataParameter<'a> {
    pub(super) name: Option<&'a str>,
    pub(super) ty: Option<&'a TypeReference>,
    pub(super) has_default: bool,
    pub(super) vararg_element_type: Option<&'a TypeReference>,
}

/// One member the metadata describes, keyed by the JVM signature the compiler
/// recorded for it.
pub(super) struct MetadataCallable<'a> {
    pub(super) name: String,
    pub(super) descriptor: String,
    pub(super) return_type: Option<&'a TypeReference>,
    pub(super) parameters: Vec<MetadataParameter<'a>>,
    pub(super) receiver_type: Option<&'a TypeReference>,
    pub(super) is_suspend: bool,
    /// Extra parameters the compiler adds around the source ones: an extension
    /// receiver before them, a coroutine continuation after.
    pub(super) leading: usize,
    pub(super) trailing: usize,
    pub(super) is_unsigned_constructor: bool,
    /// The name the source gave this member, where it has one of its own.
    pub(super) source_name: Option<&'a str>,
    pub(super) visibility: Visibility,
}

impl<'a> MetadataCallable<'a> {
    pub(super) fn of(declarations: &'a Declarations) -> Vec<Self> {
        let mut callables = Vec::new();
        for function in &declarations.functions {
            let signature = function
                .signature
                .clone()
                .or_else(|| function.default_jvm_signature());
            let Some(signature) = signature else {
                continue;
            };
            callables.push(Self {
                name: signature.name,
                descriptor: signature.descriptor,
                return_type: function.return_type.as_ref(),
                parameters: function
                    .parameters
                    .iter()
                    .map(|parameter| MetadataParameter {
                        name: Some(parameter.name.as_str()),
                        ty: parameter.ty.as_ref(),
                        has_default: parameter.has_default,
                        vararg_element_type: parameter.vararg_element_type.as_ref(),
                    })
                    .collect(),
                receiver_type: function.receiver_type.as_ref(),
                is_suspend: function.flags.is_suspend(),
                leading: usize::from(function.has_receiver),
                trailing: usize::from(function.flags.is_suspend()),
                is_unsigned_constructor: false,
                source_name: Some(function.name.as_str()),
                visibility: function.flags.visibility(),
            });
        }
        for constructor in &declarations.constructors {
            callables.push(Self {
                name: constructor
                    .signature
                    .as_ref()
                    .map(|signature| signature.name.clone())
                    .unwrap_or_else(|| "<init>".to_string()),
                descriptor: constructor
                    .signature
                    .as_ref()
                    .map(|signature| signature.descriptor.clone())
                    .unwrap_or_default(),
                return_type: None,
                parameters: constructor
                    .parameters
                    .iter()
                    .map(|parameter| MetadataParameter {
                        name: Some(parameter.name.as_str()),
                        ty: parameter.ty.as_ref(),
                        has_default: parameter.has_default,
                        vararg_element_type: parameter.vararg_element_type.as_ref(),
                    })
                    .collect(),
                receiver_type: None,
                is_suspend: false,
                leading: 0,
                trailing: 0,
                is_unsigned_constructor: constructor
                    .signature
                    .as_ref()
                    .is_none_or(|signature| signature.descriptor.is_empty()),
                source_name: None,
                visibility: constructor.flags.visibility(),
            });
        }
        // A property reaches the DEX as accessors, and both sides of it carry
        // the property's own type. The value a setter takes has no name of its
        // own in the source.
        for property in &declarations.properties {
            if let Some(getter) = &property.getter {
                callables.push(Self {
                    name: getter.name.clone(),
                    descriptor: getter.descriptor.clone(),
                    return_type: property.ty.as_ref(),
                    parameters: Vec::new(),
                    receiver_type: None,
                    is_suspend: false,
                    leading: 0,
                    trailing: 0,
                    is_unsigned_constructor: false,
                    source_name: None,
                    visibility: property.flags.visibility(),
                });
            }
            if let Some(setter) = &property.setter {
                callables.push(Self {
                    name: setter.name.clone(),
                    descriptor: setter.descriptor.clone(),
                    return_type: None,
                    parameters: vec![MetadataParameter {
                        name: None,
                        ty: property.ty.as_ref(),
                        has_default: false,
                        vararg_element_type: None,
                    }],
                    receiver_type: None,
                    is_suspend: false,
                    leading: 0,
                    trailing: 0,
                    is_unsigned_constructor: false,
                    source_name: None,
                    visibility: property.flags.visibility(),
                });
            }
        }
        callables
    }

    /// The source name to declare this member under, when using it is lossless.
    ///
    /// An `internal` member reaches the JVM with a module suffix appended to its
    /// name, and declaring it `internal` under the source name recompiles to
    /// exactly the name it has now. Other differences between the two names —
    /// `@JvmName`, inline-class mangling — are not restated by any modifier, so
    /// renaming would change what the class offers and the JVM name stands.
    pub(super) fn unmangled_name(&self) -> Option<&'a str> {
        let source = self.source_name?;
        (self.visibility == Visibility::Internal
            && self.name.len() > source.len()
            && self.name.starts_with(source)
            && self.name.as_bytes().get(source.len()) == Some(&b'$'))
        .then_some(source)
    }

    /// Finds the declaration a DEX method was compiled from.
    pub(super) fn resolve<'c>(
        callables: &'c [MetadataCallable<'a>],
        class: &crate::frontend::ClassNode,
        method: &MethodNode,
    ) -> Option<&'c MetadataCallable<'a>> {
        let descriptor = Self::descriptor(method);
        callables
            .iter()
            .find(|callable| callable.name == method.name() && callable.descriptor == descriptor)
            .or_else(|| Self::sole_constructor(callables, class, method))
    }

    /// Where the source parameters begin among the ones the DEX method takes.
    ///
    /// The compiler surrounds them with parameters the source never wrote — an
    /// extension receiver before, a coroutine continuation after — so the two
    /// lists line up only once every DEX parameter is accounted for. When they
    /// do not, the alignment is unknown and no fact is attached rather than one
    /// attached to the wrong parameter.
    pub(super) fn parameter_offset(&self, method: &MethodNode) -> Option<usize> {
        let accounted = self
            .leading
            .checked_add(self.parameters.len())?
            .checked_add(self.trailing)?;
        (accounted == method.param_types().len()).then_some(self.leading)
    }

    /// Matches a constructor the compiler recorded without a JVM signature.
    ///
    /// The signature is written only when it differs from the one the source
    /// parameters imply, so most constructors carry none. Matching then falls
    /// back to arity, and only when that leaves exactly one candidate on each
    /// side, so no constructor is attached to the wrong overload.
    fn sole_constructor<'c>(
        callables: &'c [MetadataCallable<'a>],
        class: &crate::frontend::ClassNode,
        method: &MethodNode,
    ) -> Option<&'c MetadataCallable<'a>> {
        if method.name() != "<init>" {
            return None;
        }
        let arity = method.param_types().len();
        let mut candidates = callables.iter().filter(|callable| {
            callable.is_unsigned_constructor && callable.parameters.len() == arity
        });
        let candidate = candidates.next().filter(|_| candidates.next().is_none())?;
        let mut overloads = class
            .methods()
            .iter()
            .filter(|other| other.name() == "<init>" && other.param_types().len() == arity);
        overloads.next()?;
        overloads.next().is_none().then_some(candidate)
    }

    /// Renders the JVM descriptor the metadata records a member against.
    pub(super) fn descriptor(method: &MethodNode) -> String {
        let mut descriptor = String::from("(");
        for parameter in method.param_types() {
            descriptor.push_str(&parameter.to_descriptor());
        }
        descriptor.push(')');
        descriptor.push_str(&method.return_type().to_descriptor());
        descriptor
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::kotlin_metadata::{DeclarationFlags, Property};
    use crate::frontend::{AccessInfo, ClassInfo, ClassNode, FieldInfo, FieldNode};
    use crate::ir::ArgType;

    #[test]
    fn resolves_default_abi_backing_field_without_recorded_signature() {
        let mut class = ClassNode::new(
            1,
            ClassInfo::from_type_descriptor("Lfixture/Sample;").unwrap(),
            AccessInfo::for_class(0),
        );
        class.add_field(FieldNode::new(
            1,
            FieldInfo::new(
                "Lfixture/Sample;".to_string(),
                "required".to_string(),
                ArgType::string(),
            ),
            AccessInfo::for_field(0),
        ));
        let property = Property {
            name: "required".to_string(),
            flags: DeclarationFlags::default(),
            ty: None,
            has_receiver: false,
            receiver_type: None,
            field: None,
            getter: None,
            setter: None,
            getter_is_default: true,
            setter_is_default: true,
        };

        assert_eq!(
            backing_field_references(&class, &Declarations::default(), &property),
            vec![crate::ir::FieldReference {
                owner: ArgType::object("fixture/Sample"),
                name: "required".to_string(),
                field_type: ArgType::string(),
            }]
        );
    }
}
