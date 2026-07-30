//! Field node - represents a field in a class
//!
//! Similar to jadx's FieldNode, stores field information including:
//! - Field name and type
//! - Access flags
//! - Parent class reference

use super::{AccessInfo, AnnotationNode, DexValue};
use crate::ir::ty::ArgType;

/// Unique identifier for a field within a DEX file
pub type FieldId = u32;

/// Field information (name + type + declaring class)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldInfo {
    /// Declaring class type (e.g., "Ljava/lang/String;")
    pub declaring_class: String,
    /// Field name
    pub name: String,
    /// Field type
    pub field_type: ArgType,
}

impl FieldInfo {
    /// Create new field info
    pub fn new(declaring_class: String, name: String, field_type: ArgType) -> Self {
        Self {
            declaring_class,
            name,
            field_type,
        }
    }

    /// Get short ID (name:type)
    pub fn short_id(&self) -> String {
        format!("{}:{}", self.name, self.field_type.to_descriptor())
    }

    /// Get full ID (class->name:type)
    pub fn full_id(&self) -> String {
        format!(
            "{}->{}:{}",
            self.declaring_class,
            self.name,
            self.field_type.to_descriptor()
        )
    }
}

/// Field node - represents a field in a class
#[derive(Debug, Clone)]
pub struct FieldNode {
    /// Field ID within DEX file
    pub id: FieldId,
    /// Field information
    pub info: FieldInfo,
    /// Access flags
    pub access_flags: AccessInfo,
    /// Initial value (for static fields)
    pub initial_value: Option<DexValue>,
    /// JVM generic signature recovered from the
    /// `Ldalvik/annotation/Signature;` field annotation, when present.
    pub signature: Option<String>,
    /// Kotlin source annotations preserved from DEX annotation sets.
    pub annotations: Vec<AnnotationNode>,
}

impl FieldNode {
    /// Create a new field node
    pub fn new(id: FieldId, info: FieldInfo, access_flags: AccessInfo) -> Self {
        Self {
            id,
            info,
            access_flags,
            initial_value: None,
            signature: None,
            annotations: Vec::new(),
        }
    }

    /// Create field node with initial value
    pub fn with_initial_value(mut self, value: DexValue) -> Self {
        self.initial_value = Some(value);
        self
    }

    /// Attach a recovered JVM generic signature.
    pub fn with_signature(mut self, signature: Option<String>) -> Self {
        self.signature = signature;
        self
    }

    /// Get field name
    #[inline]
    pub fn name(&self) -> &str {
        &self.info.name
    }

    /// Get field type
    #[inline]
    pub fn field_type(&self) -> &ArgType {
        &self.info.field_type
    }

    /// Get declaring class
    #[inline]
    pub fn declaring_class(&self) -> &str {
        &self.info.declaring_class
    }

    /// Check if static
    #[inline]
    pub fn is_static(&self) -> bool {
        self.access_flags.is_static()
    }

    /// Check if instance (non-static)
    #[inline]
    pub fn is_instance(&self) -> bool {
        !self.is_static()
    }

    /// Check if final
    #[inline]
    pub fn is_final(&self) -> bool {
        self.access_flags.is_final()
    }

    /// Check if volatile
    #[inline]
    pub fn is_volatile(&self) -> bool {
        self.access_flags.is_volatile()
    }

    /// Check if transient
    #[inline]
    pub fn is_transient(&self) -> bool {
        self.access_flags.is_transient()
    }

    /// Check if synthetic
    #[inline]
    pub fn is_synthetic(&self) -> bool {
        self.access_flags.is_synthetic()
    }

    /// Get short ID
    pub fn short_id(&self) -> String {
        self.info.short_id()
    }

    /// Get full ID
    pub fn full_id(&self) -> String {
        self.info.full_id()
    }
}

impl std::fmt::Display for FieldNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {}",
            self.access_flags.to_modifier_string(),
            self.info.field_type,
            self.info.name
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_field_info() {
        let info = FieldInfo::new(
            "Ljava/lang/String;".to_string(),
            "value".to_string(),
            ArgType::array(ArgType::CHAR),
        );
        assert_eq!(info.short_id(), "value:[C");
        assert!(info.full_id().contains("Ljava/lang/String;"));
    }

    #[test]
    fn test_field_node() {
        let info = FieldInfo::new("LTest;".to_string(), "count".to_string(), ArgType::INT);
        let field = FieldNode::new(0, info, AccessInfo::for_field(0x0009)); // public static

        assert!(field.is_static());
        assert!(!field.is_instance());
        assert_eq!(field.name(), "count");
    }
}
