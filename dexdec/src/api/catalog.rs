//! Lightweight archive and class metadata for interactive clients.

use std::path::PathBuf;

use crate::frontend::{ClassNode, DexFileReader, DexMemberDeclaration, DexMemberKind, DexResult};

use super::kotlin_source_path;

/// A lightweight archive index built without loading or decompiling classes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ArchiveCatalog {
    classes: Vec<ClassSummary>,
}

impl ArchiveCatalog {
    pub(crate) fn from_reader(reader: &DexFileReader) -> Self {
        let mut classes = reader
            .class_names()
            .into_iter()
            .map(|descriptor| {
                let parent_descriptor = reader.lexical_parent(&descriptor).map(str::to_string);
                let nested_name = reader.lexical_simple_name(&descriptor).map(str::to_string);
                ClassSummary::from_descriptor(descriptor, parent_descriptor, nested_name)
            })
            .collect::<Vec<_>>();
        classes.sort_unstable_by(|left, right| left.qualified_name.cmp(&right.qualified_name));
        classes.dedup_by(|left, right| left.descriptor == right.descriptor);
        Self { classes }
    }

    pub fn classes(&self) -> &[ClassSummary] {
        &self.classes
    }

    pub fn len(&self) -> usize {
        self.classes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.classes.is_empty()
    }
}

/// Member declarations available without decoding method bytecode.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ArchiveMemberCatalog {
    members: Vec<MemberSummary>,
}

impl ArchiveMemberCatalog {
    pub(crate) fn from_reader(reader: &DexFileReader) -> DexResult<Self> {
        let mut members = Vec::new();
        reader.visit_member_declarations(|member| members.push(member.into()))?;
        Ok(Self { members })
    }

    pub fn members(&self) -> &[MemberSummary] {
        &self.members
    }

    pub fn into_members(self) -> Vec<MemberSummary> {
        self.members
    }

    pub fn len(&self) -> usize {
        self.members.len()
    }

    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }
}

/// Receives member declarations as they are read from DEX class data.
///
/// Streaming avoids retaining a second archive-sized declaration directory in
/// clients that build their own compact indexes.
pub trait MemberVisitor {
    fn visit(&mut self, member: MemberSummary);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MemberKind {
    Field,
    Method,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct MemberSummary {
    pub owner: String,
    pub name: String,
    pub descriptor: String,
    pub kind: MemberKind,
    pub has_code: bool,
}

impl From<DexMemberDeclaration> for MemberSummary {
    fn from(declaration: DexMemberDeclaration) -> Self {
        Self {
            owner: declaration.owner,
            name: declaration.name,
            descriptor: declaration.descriptor,
            kind: match declaration.kind {
                DexMemberKind::Field => MemberKind::Field,
                DexMemberKind::Method => MemberKind::Method,
            },
            has_code: declaration.has_code,
        }
    }
}

/// Class identity available directly from a DEX class definition table.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ClassSummary {
    pub descriptor: String,
    pub qualified_name: String,
    pub package: String,
    pub binary_name: String,
    pub display_name: String,
    pub parent_descriptor: Option<String>,
    pub source_path: PathBuf,
}

impl ClassSummary {
    fn from_descriptor(
        descriptor: String,
        parent_descriptor: Option<String>,
        nested_name: Option<String>,
    ) -> Self {
        let internal_name = descriptor
            .strip_prefix('L')
            .and_then(|name| name.strip_suffix(';'))
            .unwrap_or(&descriptor);
        let (package_path, binary_name) = internal_name
            .rsplit_once('/')
            .map_or(("", internal_name), |(package, name)| (package, name));
        let package = package_path.replace('/', ".");
        let binary_name = binary_name.to_string();
        let display_name = nested_name.unwrap_or_else(|| binary_name.clone());
        let qualified_name = if package.is_empty() {
            binary_name.clone()
        } else {
            format!("{package}.{binary_name}")
        };
        Self {
            source_path: kotlin_source_path(&descriptor),
            descriptor,
            qualified_name,
            package,
            binary_name,
            display_name,
            parent_descriptor,
        }
    }
}

/// Kotlin declaration category for an inspected class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ClassKind {
    Class,
    Interface,
    Annotation,
    Enum,
}

/// Metadata for one class. Building it loads this class but does not decode methods.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ClassOutline {
    pub descriptor: String,
    pub qualified_name: String,
    pub kind: ClassKind,
    pub access_flags: u32,
    pub super_class: Option<String>,
    pub interfaces: Vec<String>,
    pub source_file: Option<String>,
    pub parent_class: Option<String>,
    pub nested_classes: Vec<String>,
    pub fields: Vec<FieldOutline>,
    pub methods: Vec<MethodOutline>,
}

impl ClassOutline {
    pub(crate) fn from_node(class: &ClassNode) -> Self {
        let kind = if class.is_annotation() {
            ClassKind::Annotation
        } else if class.is_enum() {
            ClassKind::Enum
        } else if class.is_interface() {
            ClassKind::Interface
        } else {
            ClassKind::Class
        };
        Self {
            descriptor: class.type_descriptor().to_string(),
            qualified_name: class.full_name().to_string(),
            kind,
            access_flags: class.access_flags.raw(),
            super_class: class.super_class.as_ref().map(|ty| ty.to_descriptor()),
            interfaces: class
                .interfaces
                .iter()
                .map(|ty| ty.to_descriptor())
                .collect(),
            source_file: class.source_file.clone(),
            parent_class: class.parent_class_name().map(str::to_string),
            nested_classes: class.inner_class_names().to_vec(),
            fields: class.fields().iter().map(FieldOutline::from).collect(),
            methods: class.methods().iter().map(MethodOutline::from).collect(),
        }
    }
}

/// Field declaration metadata without its decoded value flow.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct FieldOutline {
    pub name: String,
    pub descriptor: String,
    pub display_type: String,
    pub access_flags: u32,
}

impl From<&crate::frontend::FieldNode> for FieldOutline {
    fn from(field: &crate::frontend::FieldNode) -> Self {
        Self {
            name: field.name().to_string(),
            descriptor: field.field_type().to_descriptor(),
            display_type: field.field_type().to_string(),
            access_flags: field.access_flags.raw(),
        }
    }
}

/// Method declaration metadata. `has_code` is false for abstract and native methods.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct MethodOutline {
    pub name: String,
    pub descriptor: String,
    pub display_signature: String,
    pub access_flags: u32,
    pub has_code: bool,
    pub constructor: bool,
}

impl From<&crate::frontend::MethodNode> for MethodOutline {
    fn from(method: &crate::frontend::MethodNode) -> Self {
        Self {
            name: method.name().to_string(),
            descriptor: method.info.descriptor(),
            display_signature: method.info.readable_signature(),
            access_flags: method.access_flags.raw(),
            has_code: method.code().is_some(),
            constructor: method.is_constructor(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn summary_preserves_descriptor_and_java_identity() {
        let summary = ClassSummary::from_descriptor(
            "Lorg/example/Outer$Inner;".to_string(),
            Some("Lorg/example/Outer;".to_string()),
            Some("Inner".to_string()),
        );
        assert_eq!(summary.qualified_name, "org.example.Outer$Inner");
        assert_eq!(summary.package, "org.example");
        assert_eq!(summary.binary_name, "Outer$Inner");
        assert_eq!(summary.display_name, "Inner");
        assert_eq!(
            summary.parent_descriptor.as_deref(),
            Some("Lorg/example/Outer;")
        );
        assert_eq!(
            summary.source_path,
            PathBuf::from("org/example/`Outer$Inner`.kt")
        );
    }
}
