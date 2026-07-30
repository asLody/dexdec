//! Class node - represents a class in the DEX file
//!
//! Similar to jadx's ClassNode, stores class information including:
//! - Class name and package
//! - Superclass and interfaces
//! - Methods and fields
//! - Inner classes
//! - Access flags and annotations

use super::{AccessInfo, AnnotationNode, FieldNode, MethodNode};
use crate::ir::{ArgType, DescriptorParseError};
use std::collections::HashMap;

/// Unique identifier for a class within a DEX file
pub type ClassId = u32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InnerClassInfo {
    pub simple_name: Option<String>,
    pub access_flags_raw: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnclosingInfo {
    pub class_descriptor: Option<String>,
    pub method_reference: Option<String>,
    /// Resolved declaration context for `method_reference`. This is populated
    /// while loaded classes are linked, not inferred from captured fields.
    pub method_static: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ClassMetadata {
    pub inner_class: Option<InnerClassInfo>,
    pub member_classes: Vec<String>,
    pub enclosing: Option<EnclosingInfo>,
}

/// Class information (type + package)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassInfo {
    ty: ArgType,
    /// Full class type (e.g., "Ljava/lang/String;")
    pub type_descriptor: String,
    /// Package name (e.g., "java.lang")
    pub package: String,
    /// Simple class name (e.g., "String")
    pub name: String,
    /// Full qualified name (e.g., "java.lang.String")
    pub full_name: String,
}

impl ClassInfo {
    /// Create class info from type descriptor
    pub fn from_type_descriptor(type_desc: &str) -> Result<Self, ClassInfoError> {
        let ty = type_desc
            .parse::<ArgType>()
            .map_err(ClassInfoError::Descriptor)?;
        let internal = ty
            .as_object()
            .ok_or_else(|| ClassInfoError::NotClass(ty.clone()))?;

        // Convert to full name: "java/lang/String" -> "java.lang.String"
        let full_name = internal.replace('/', ".");

        // Extract package and name
        let (package, name) = if let Some(last_dot) = full_name.rfind('.') {
            (
                full_name[..last_dot].to_string(),
                full_name[last_dot + 1..].to_string(),
            )
        } else {
            (String::new(), full_name.clone())
        };

        // Handle inner classes ($ separator)
        let simple_name = if let Some(last_dollar) = name.rfind('$') {
            name[last_dollar + 1..].to_string()
        } else {
            name.clone()
        };

        Ok(Self {
            ty,
            type_descriptor: type_desc.to_string(),
            package,
            name: simple_name,
            full_name,
        })
    }

    /// Get raw name (internal format with /)
    pub fn raw_name(&self) -> &str {
        &self.type_descriptor
    }

    /// Check if this is an inner class
    pub fn is_inner(&self) -> bool {
        self.full_name.contains('$')
    }

    /// Get outer class name for inner class
    pub fn outer_class_name(&self) -> Option<String> {
        if let Some(dollar_pos) = self.full_name.rfind('$') {
            Some(self.full_name[..dollar_pos].to_string())
        } else {
            None
        }
    }
}

/// Processing state of a class
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassState {
    /// Not yet loaded
    NotLoaded,
    /// Structure loaded (fields, methods declared)
    Loaded,
    /// Currently being processed
    Processing,
    /// Processing complete
    ProcessComplete,
    /// Error during processing
    Error,
}

impl Default for ClassState {
    fn default() -> Self {
        ClassState::NotLoaded
    }
}

/// Class node - represents a class in the DEX file
#[derive(Debug)]
pub struct ClassNode {
    /// Class ID within DEX file
    pub id: ClassId,
    /// Class information
    pub info: ClassInfo,
    /// Access flags
    pub access_flags: AccessInfo,
    /// Superclass type (None for java.lang.Object)
    pub super_class: Option<ArgType>,
    /// Implemented interfaces
    pub interfaces: Vec<ArgType>,
    /// Source file name (debug info)
    pub source_file: Option<String>,
    /// JVM generic class signature recovered from the
    /// `Ldalvik/annotation/Signature;` class-level annotation, when present.
    pub signature: Option<String>,
    /// Dalvik inner/enclosing metadata recovered from class annotations.
    pub metadata: ClassMetadata,
    /// Kotlin source annotations preserved from DEX annotation sets.
    pub annotations: Vec<AnnotationNode>,
    /// Methods in this class
    methods: Vec<MethodNode>,
    /// Fields in this class
    fields: Vec<FieldNode>,
    /// Inner classes
    inner_classes: Vec<String>,
    /// Parent class (for inner classes)
    parent_class: Option<String>,
    /// Processing state
    state: ClassState,
    /// Method lookup cache
    method_cache: HashMap<String, usize>,
    /// Field lookup cache
    field_cache: HashMap<String, usize>,
}

impl ClassNode {
    /// Create a new class node
    pub fn new(id: ClassId, info: ClassInfo, access_flags: AccessInfo) -> Self {
        Self {
            id,
            info,
            access_flags,
            super_class: None,
            interfaces: Vec::new(),
            source_file: None,
            signature: None,
            metadata: ClassMetadata::default(),
            annotations: Vec::new(),
            methods: Vec::new(),
            fields: Vec::new(),
            inner_classes: Vec::new(),
            parent_class: None,
            state: ClassState::NotLoaded,
            method_cache: HashMap::new(),
            field_cache: HashMap::new(),
        }
    }

    /// Set superclass
    pub fn set_super_class(&mut self, super_class: ArgType) {
        self.super_class = Some(super_class);
    }

    /// Add interface
    pub fn add_interface(&mut self, interface: ArgType) {
        self.interfaces.push(interface);
    }

    /// Add a method
    pub fn add_method(&mut self, method: MethodNode) {
        let key = method.short_id();
        let idx = self.methods.len();
        self.methods.push(method);
        self.method_cache.insert(key, idx);
    }

    /// Add a field
    pub fn add_field(&mut self, field: FieldNode) {
        let key = field.short_id();
        let idx = self.fields.len();
        self.fields.push(field);
        self.field_cache.insert(key, idx);
    }

    /// Add inner class
    pub fn add_inner_class(&mut self, inner_descriptor: impl Into<String>) {
        let inner_descriptor = inner_descriptor.into();
        if !self.inner_classes.contains(&inner_descriptor) {
            self.inner_classes.push(inner_descriptor);
        }
    }

    /// Set parent class
    pub fn set_parent_class(&mut self, parent_descriptor: impl Into<String>) {
        self.parent_class = Some(parent_descriptor.into());
    }

    pub fn clear_parent_class(&mut self) {
        self.parent_class = None;
    }

    pub fn clear_inner_classes(&mut self) {
        self.inner_classes.clear();
    }

    pub fn sort_inner_classes(&mut self) {
        self.inner_classes.sort();
    }

    pub fn set_metadata(&mut self, metadata: ClassMetadata) {
        self.metadata = metadata;
    }

    // ==================== Getters ====================

    /// Get class name
    #[inline]
    pub fn name(&self) -> &str {
        &self.info.name
    }

    /// Get full class name
    #[inline]
    pub fn full_name(&self) -> &str {
        &self.info.full_name
    }

    /// Get package name
    #[inline]
    pub fn package(&self) -> &str {
        &self.info.package
    }

    /// Get type descriptor
    #[inline]
    pub fn type_descriptor(&self) -> &str {
        &self.info.type_descriptor
    }

    /// Get class type
    pub fn class_type(&self) -> &ArgType {
        &self.info.ty
    }

    /// Get processing state
    #[inline]
    pub fn state(&self) -> ClassState {
        self.state
    }

    /// Set processing state
    pub fn set_state(&mut self, state: ClassState) {
        self.state = state;
    }

    // ==================== Access flags shortcuts ====================

    #[inline]
    pub fn is_public(&self) -> bool {
        self.access_flags.is_public()
    }

    #[inline]
    pub fn is_interface(&self) -> bool {
        self.access_flags.is_interface()
    }

    #[inline]
    pub fn is_abstract(&self) -> bool {
        self.access_flags.is_abstract()
    }

    #[inline]
    pub fn is_annotation(&self) -> bool {
        self.access_flags.is_annotation()
    }

    #[inline]
    pub fn is_enum(&self) -> bool {
        self.access_flags.is_enum()
    }

    #[inline]
    pub fn is_final(&self) -> bool {
        self.access_flags.is_final()
    }

    #[inline]
    pub fn is_synthetic(&self) -> bool {
        self.access_flags.is_synthetic()
    }

    /// Check if inner class
    #[inline]
    pub fn is_inner(&self) -> bool {
        self.parent_class.is_some()
    }

    #[inline]
    pub fn is_anonymous(&self) -> bool {
        self.metadata
            .inner_class
            .as_ref()
            .and_then(|inner| inner.simple_name.as_deref())
            .map_or(true, looks_like_anonymous_inner_name)
            && self.metadata.inner_class.is_some()
    }

    #[inline]
    pub fn is_local_class(&self) -> bool {
        self.metadata
            .enclosing
            .as_ref()
            .is_some_and(|enclosing| enclosing.method_reference.is_some())
            && !self.is_anonymous()
    }

    /// Check if top-level class
    #[inline]
    pub fn is_top_level(&self) -> bool {
        !self.is_inner()
    }

    // ==================== Methods ====================

    /// Get all methods
    pub fn methods(&self) -> &[MethodNode] {
        &self.methods
    }

    /// Get mutable methods
    pub fn methods_mut(&mut self) -> &mut [MethodNode] {
        &mut self.methods
    }

    /// Get method by index
    pub fn method(&self, idx: usize) -> Option<&MethodNode> {
        self.methods.get(idx)
    }

    /// Get mutable method by index
    pub fn method_mut(&mut self, idx: usize) -> Option<&mut MethodNode> {
        self.methods.get_mut(idx)
    }

    /// Find method by short ID
    pub fn find_method(&self, short_id: &str) -> Option<&MethodNode> {
        self.method_cache
            .get(short_id)
            .and_then(|&idx| self.methods.get(idx))
    }

    /// Find mutable method by short ID
    pub fn find_method_mut(&mut self, short_id: &str) -> Option<&mut MethodNode> {
        if let Some(&idx) = self.method_cache.get(short_id) {
            self.methods.get_mut(idx)
        } else {
            None
        }
    }

    /// Find method by name (returns first match)
    pub fn find_method_by_name(&self, name: &str) -> Option<&MethodNode> {
        self.methods.iter().find(|m| m.name() == name)
    }

    /// Get class initializer (<clinit>)
    pub fn class_init(&self) -> Option<&MethodNode> {
        self.find_method("<clinit>()V")
    }

    /// Get default constructor
    pub fn default_constructor(&self) -> Option<&MethodNode> {
        self.find_method("<init>()V")
    }

    /// Get all constructors
    pub fn constructors(&self) -> impl Iterator<Item = &MethodNode> {
        self.methods.iter().filter(|m| m.is_constructor())
    }

    // ==================== Fields ====================

    /// Get all fields
    pub fn fields(&self) -> &[FieldNode] {
        &self.fields
    }

    /// Get mutable fields
    pub fn fields_mut(&mut self) -> &mut [FieldNode] {
        &mut self.fields
    }

    /// Get field by index
    pub fn field(&self, idx: usize) -> Option<&FieldNode> {
        self.fields.get(idx)
    }

    /// Find field by short ID
    pub fn find_field(&self, short_id: &str) -> Option<&FieldNode> {
        self.field_cache
            .get(short_id)
            .and_then(|&idx| self.fields.get(idx))
    }

    /// Find field by name
    pub fn find_field_by_name(&self, name: &str) -> Option<&FieldNode> {
        self.fields.iter().find(|f| f.name() == name)
    }

    /// Get static fields
    pub fn static_fields(&self) -> impl Iterator<Item = &FieldNode> {
        self.fields.iter().filter(|f| f.is_static())
    }

    /// Get instance fields
    pub fn instance_fields(&self) -> impl Iterator<Item = &FieldNode> {
        self.fields.iter().filter(|f| f.is_instance())
    }

    // ==================== Inner classes ====================

    /// Get inner class IDs
    pub fn inner_class_names(&self) -> &[String] {
        &self.inner_classes
    }

    /// Get parent class ID
    pub fn parent_class_name(&self) -> Option<&str> {
        self.parent_class.as_deref()
    }

    // ==================== Loading ====================

    /// Mark class as loaded
    pub fn mark_loaded(&mut self) {
        self.state = ClassState::Loaded;
    }

    /// Rebuild caches after bulk modifications
    pub fn rebuild_caches(&mut self) {
        self.method_cache.clear();
        for (idx, method) in self.methods.iter().enumerate() {
            self.method_cache.insert(method.short_id(), idx);
        }

        self.field_cache.clear();
        for (idx, field) in self.fields.iter().enumerate() {
            self.field_cache.insert(field.short_id(), idx);
        }
    }
}

#[derive(Debug, Clone)]
pub enum ClassInfoError {
    Descriptor(DescriptorParseError),
    NotClass(ArgType),
}

impl std::fmt::Display for ClassInfoError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Descriptor(source) => write!(formatter, "invalid class descriptor: {source}"),
            Self::NotClass(ty) => write!(formatter, "class descriptor denotes {ty}"),
        }
    }
}

impl std::error::Error for ClassInfoError {}

fn looks_like_anonymous_inner_name(name: &str) -> bool {
    !name.is_empty() && name.chars().all(|ch| ch.is_ascii_digit())
}

impl std::fmt::Display for ClassNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let class_type = if self.is_interface() {
            "interface"
        } else if self.is_enum() {
            "enum"
        } else if self.is_annotation() {
            "@interface"
        } else {
            "class"
        };

        write!(
            f,
            "{} {} {}",
            self.access_flags.to_modifier_string(),
            class_type,
            self.full_name()
        )
    }
}

impl Clone for ClassNode {
    fn clone(&self) -> Self {
        let method_cache = self
            .methods
            .iter()
            .enumerate()
            .map(|(idx, method)| (method.short_id(), idx))
            .collect();
        let field_cache = self
            .fields
            .iter()
            .enumerate()
            .map(|(idx, field)| (field.short_id(), idx))
            .collect();
        Self {
            id: self.id,
            info: self.info.clone(),
            access_flags: self.access_flags,
            super_class: self.super_class.clone(),
            interfaces: self.interfaces.clone(),
            source_file: self.source_file.clone(),
            signature: self.signature.clone(),
            metadata: self.metadata.clone(),
            annotations: self.annotations.clone(),
            methods: self.methods.clone(),
            fields: self.fields.clone(),
            inner_classes: self.inner_classes.clone(),
            parent_class: self.parent_class.clone(),
            state: ClassState::NotLoaded,
            method_cache,
            field_cache,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_class_info_simple() {
        let info = ClassInfo::from_type_descriptor("Ljava/lang/String;").unwrap();
        assert_eq!(info.package, "java.lang");
        assert_eq!(info.name, "String");
        assert_eq!(info.full_name, "java.lang.String");
        assert!(!info.is_inner());
    }

    #[test]
    fn test_class_info_inner() {
        let info = ClassInfo::from_type_descriptor("Ljava/util/Map$Entry;").unwrap();
        assert_eq!(info.package, "java.util");
        assert_eq!(info.name, "Entry");
        assert_eq!(info.full_name, "java.util.Map$Entry");
        assert!(info.is_inner());
        assert_eq!(info.outer_class_name(), Some("java.util.Map".to_string()));
    }

    #[test]
    fn test_class_info_default_package() {
        let info = ClassInfo::from_type_descriptor("LTest;").unwrap();
        assert_eq!(info.package, "");
        assert_eq!(info.name, "Test");
        assert_eq!(info.full_name, "Test");
    }

    #[test]
    fn test_class_node() {
        let info = ClassInfo::from_type_descriptor("LTest;").unwrap();
        let cls = ClassNode::new(0, info, AccessInfo::for_class(0x0001)); // public

        assert!(cls.is_public());
        assert!(!cls.is_interface());
        assert!(cls.is_top_level());
        assert_eq!(cls.name(), "Test");
    }
}
