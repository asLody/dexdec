use std::{fmt, str::FromStr};

use super::{ArgType, DescriptorParseError, MethodDescriptor};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MethodReference {
    pub owner: ArgType,
    pub name: String,
    pub descriptor: MethodDescriptor,
}

impl MethodReference {
    pub fn is_constructor(&self) -> bool {
        self.name == "<init>"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldReference {
    pub owner: ArgType,
    pub name: String,
    pub field_type: ArgType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemberReference {
    Method(MethodReference),
    Field(FieldReference),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReferenceParseError {
    MissingOwnerSeparator,
    MissingMethodDescriptor,
    MissingFieldDescriptor,
    EmptyMemberName,
    InvalidOwner(DescriptorParseError),
    NonObjectOwner(ArgType),
    InvalidDescriptor(DescriptorParseError),
    VoidField,
}

impl fmt::Display for ReferenceParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingOwnerSeparator => f.write_str("member reference has no '->' separator"),
            Self::MissingMethodDescriptor => {
                f.write_str("method reference has no method descriptor")
            }
            Self::MissingFieldDescriptor => f.write_str("field reference has no field descriptor"),
            Self::EmptyMemberName => f.write_str("member reference has an empty name"),
            Self::InvalidOwner(source) => write!(f, "invalid member owner: {source}"),
            Self::NonObjectOwner(owner) => write!(f, "member owner {owner} is not an object type"),
            Self::InvalidDescriptor(source) => write!(f, "invalid member descriptor: {source}"),
            Self::VoidField => f.write_str("field type cannot be void"),
        }
    }
}

impl std::error::Error for ReferenceParseError {}

impl FromStr for MethodReference {
    type Err = ReferenceParseError;

    fn from_str(reference: &str) -> Result<Self, Self::Err> {
        let (owner, member) = reference
            .split_once("->")
            .ok_or(ReferenceParseError::MissingOwnerSeparator)?;
        let open = member
            .find('(')
            .ok_or(ReferenceParseError::MissingMethodDescriptor)?;
        if open == 0 {
            return Err(ReferenceParseError::EmptyMemberName);
        }
        let owner = owner
            .parse::<ArgType>()
            .map_err(ReferenceParseError::InvalidOwner)?;
        if !owner.is_reference() {
            return Err(ReferenceParseError::NonObjectOwner(owner));
        }
        let descriptor = member[open..]
            .parse::<MethodDescriptor>()
            .map_err(ReferenceParseError::InvalidDescriptor)?;
        Ok(Self {
            owner,
            name: member[..open].to_string(),
            descriptor,
        })
    }
}

impl FromStr for FieldReference {
    type Err = ReferenceParseError;

    fn from_str(reference: &str) -> Result<Self, Self::Err> {
        let (owner, member) = reference
            .split_once("->")
            .ok_or(ReferenceParseError::MissingOwnerSeparator)?;
        let (name, descriptor) = member
            .split_once(':')
            .ok_or(ReferenceParseError::MissingFieldDescriptor)?;
        if name.is_empty() {
            return Err(ReferenceParseError::EmptyMemberName);
        }
        let owner = owner
            .parse::<ArgType>()
            .map_err(ReferenceParseError::InvalidOwner)?;
        if owner.as_object().is_none() {
            return Err(ReferenceParseError::NonObjectOwner(owner));
        }
        let field_type = descriptor
            .parse::<ArgType>()
            .map_err(ReferenceParseError::InvalidDescriptor)?;
        if field_type == ArgType::VOID {
            return Err(ReferenceParseError::VoidField);
        }
        Ok(Self {
            owner,
            name: name.to_string(),
            field_type,
        })
    }
}

impl fmt::Display for MethodReference {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{}->{}{}",
            self.owner.to_descriptor(),
            self.name,
            self.descriptor
        )
    }
}

impl fmt::Display for FieldReference {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{}->{}:{}",
            self.owner.to_descriptor(),
            self.name,
            self.field_type.to_descriptor()
        )
    }
}

impl fmt::Display for MemberReference {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Method(reference) => reference.fmt(formatter),
            Self::Field(reference) => reference.fmt(formatter),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn method_references_accept_primitive_array_owners() {
        let reference = "[B->clone()Ljava/lang/Object;"
            .parse::<MethodReference>()
            .expect("array clone reference");

        assert_eq!(reference.owner, ArgType::array(ArgType::BYTE));
        assert_eq!(reference.name, "clone");
    }

    #[test]
    fn method_references_accept_object_array_owners() {
        let reference = "[Ljava/lang/String;->clone()Ljava/lang/Object;"
            .parse::<MethodReference>()
            .expect("object array clone reference");

        assert_eq!(reference.owner, ArgType::array(ArgType::string()));
    }

    #[test]
    fn field_references_still_require_class_owners() {
        assert!(matches!(
            "[I->length:I".parse::<FieldReference>(),
            Err(ReferenceParseError::NonObjectOwner(ArgType::Array(_)))
        ));
    }
}
