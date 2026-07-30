//! Symbol reference queries for interactive clients.

/// A DEX symbol or a descriptor-constrained member set.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ReferenceTarget {
    Class {
        descriptor: String,
    },
    Field {
        class: String,
        name: String,
        descriptor: String,
    },
    Method {
        class: String,
        name: String,
        descriptor: String,
    },
    FieldName {
        class: String,
        name: String,
    },
    MethodArity {
        class: String,
        name: String,
        arity: usize,
    },
    MethodParameters {
        class: String,
        name: String,
        parameters: Vec<String>,
    },
}

impl ReferenceTarget {
    pub fn class(descriptor: impl Into<String>) -> Self {
        Self::Class {
            descriptor: descriptor.into(),
        }
    }

    pub fn field(
        class: impl Into<String>,
        name: impl Into<String>,
        descriptor: impl Into<String>,
    ) -> Self {
        Self::Field {
            class: class.into(),
            name: name.into(),
            descriptor: descriptor.into(),
        }
    }

    pub fn method(
        class: impl Into<String>,
        name: impl Into<String>,
        descriptor: impl Into<String>,
    ) -> Self {
        Self::Method {
            class: class.into(),
            name: name.into(),
            descriptor: descriptor.into(),
        }
    }

    pub fn field_name(class: impl Into<String>, name: impl Into<String>) -> Self {
        Self::FieldName {
            class: class.into(),
            name: name.into(),
        }
    }

    pub fn method_arity(class: impl Into<String>, name: impl Into<String>, arity: usize) -> Self {
        Self::MethodArity {
            class: class.into(),
            name: name.into(),
            arity,
        }
    }

    pub fn method_parameters(
        class: impl Into<String>,
        name: impl Into<String>,
        parameters: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self::MethodParameters {
            class: class.into(),
            name: name.into(),
            parameters: parameters.into_iter().map(Into::into).collect(),
        }
    }

    pub(crate) fn dex_target(&self) -> crate::frontend::DexReferenceTarget {
        use crate::frontend::DexReferenceTarget;

        match self {
            Self::Class { descriptor } => DexReferenceTarget::Class(descriptor.clone()),
            Self::Field {
                class,
                name,
                descriptor,
            } => DexReferenceTarget::Field(format!("{class}->{name}:{descriptor}")),
            Self::Method {
                class,
                name,
                descriptor,
            } => DexReferenceTarget::Method(format!("{class}->{name}{descriptor}")),
            Self::FieldName { class, name } => DexReferenceTarget::FieldName {
                class: class.clone(),
                name: name.clone(),
            },
            Self::MethodArity { class, name, arity } => DexReferenceTarget::MethodArity {
                class: class.clone(),
                name: name.clone(),
                arity: *arity,
            },
            Self::MethodParameters {
                class,
                name,
                parameters,
            } => DexReferenceTarget::MethodParameters {
                class: class.clone(),
                name: name.clone(),
                parameters: parameters.clone(),
            },
        }
    }
}

/// A method containing at least one reference to the requested symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ReferenceLocation {
    pub class: String,
    pub method: String,
    pub descriptor: String,
    /// Dalvik code-unit offset within the method.
    pub offset: u32,
}

/// Complete result for one symbol query.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ReferenceResults {
    pub target: ReferenceTarget,
    pub locations: Vec<ReferenceLocation>,
}
