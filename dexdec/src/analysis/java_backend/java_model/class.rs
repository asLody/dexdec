use crate::frontend::{AccessInfo, AnnotationNode, ClassNode, DexValue, FieldNode};
use crate::ir::generic_types::ClassSignature;
use crate::ir::ty::{ArgType, PrimitiveType};
use crate::language::java::{JavaClassName, JavaIdentifier, JavaModifier};

use super::method::{JavaMethodBody, JavaMethodModel};
use super::source_abi::{EnclosingInstanceAbi, FunctionObjectClass, OuterInstanceField};

#[derive(Debug, Clone)]
pub(in crate::analysis::java_backend) struct JavaClassModel {
    pub declaration: JavaClassDeclaration,
    pub fields: Vec<JavaFieldDeclaration>,
    pub methods: Vec<JavaMethodModel>,
    pub function_object: bool,
    pub outer_instance: Option<OuterInstanceField>,
    /// Inner classes to render nested inside this class body, in declaration
    /// order. Each entry is itself a fully-formed `JavaClassModel` so the
    /// renderer can recurse at the next indentation level.
    pub nested: Vec<JavaClassModel>,
}

impl JavaClassModel {
    pub fn from_class_node(
        class: &ClassNode,
        methods: Vec<JavaMethodModel>,
        outer_instance: Option<OuterInstanceField>,
    ) -> Result<Self, crate::ir::generic_types::SignatureError> {
        Ok(Self {
            declaration: JavaClassDeclaration::from_class_node(class)?,
            fields: field_declarations_from_class(class, outer_instance.as_ref())?,
            methods,
            function_object: FunctionObjectClass::analyze(class),
            outer_instance,
            nested: Vec::new(),
        })
    }

    pub fn with_nested(mut self, nested: Vec<JavaClassModel>) -> Self {
        self.nested = nested;
        self
    }

    /// Assigns declaration names after the complete lexical type tree exists.
    /// Anonymous DEX names repeat at each nesting level (`$1$1$1`), while Java
    /// forbids a member type from reusing any enclosing type name. A top-down
    /// allocation keeps the descriptor-to-source-type mapping injective before
    /// signatures and method bodies are lowered.
    pub(in crate::analysis::java_backend) fn assign_lexical_type_names(
        &mut self,
        source_abi: &super::source_abi::JavaSourceAbi,
    ) {
        Self::assign_nested_type_names(self, &[], source_abi);
    }

    fn assign_nested_type_names(
        owner: &mut Self,
        inherited: &[JavaIdentifier],
        source_abi: &super::source_abi::JavaSourceAbi,
    ) {
        let mut lexical = inherited.to_vec();
        lexical.push(owner.declaration.name.clone());
        if let Some(signature) = &owner.declaration.signature {
            lexical.extend(
                signature
                    .type_parameters
                    .iter()
                    .map(|parameter| JavaIdentifier::from_dex(&parameter.name)),
            );
        }

        let mut assigned = std::collections::BTreeSet::new();
        for nested in &mut owner.nested {
            let mut scope = crate::language::java::JavaNameScope::default();
            for name in lexical.iter().chain(&assigned) {
                scope.reserve(name.clone());
            }
            if nested.declaration.is_anonymous {
                if let Some(owner) = nested.declaration.current_type() {
                    for name in source_abi.inherited_member_type_names(&owner) {
                        scope.reserve(name.clone());
                    }
                }
            }
            nested.declaration.name = scope.claim(nested.declaration.name.clone());
            assigned.insert(nested.declaration.name.clone());
        }
        for nested in &mut owner.nested {
            Self::assign_nested_type_names(nested, &lexical, source_abi);
        }
    }

    pub fn as_nested_source_member(mut self, class: &ClassNode) -> Self {
        self.declaration.is_nested = true;
        self.declaration.package = None;
        let lifted_from_static_method =
            class.metadata.enclosing.as_ref().is_some_and(|enclosing| {
                enclosing.method_reference.is_some() && enclosing.method_static == Some(true)
            });
        let lifted_without_enclosing_instance =
            (class.is_anonymous() || class.is_local_class() || FunctionObjectClass::analyze(class))
                && EnclosingInstanceAbi::analyze(class).is_none();
        if (lifted_from_static_method || lifted_without_enclosing_instance)
            && !self.declaration.modifiers.contains(&JavaModifier::Static)
        {
            self.declaration.modifiers.push(JavaModifier::Static);
        }
        self
    }

    pub(in crate::analysis::java_backend) fn method_references(
        &self,
    ) -> std::collections::BTreeSet<crate::ir::MethodReference> {
        let mut references = std::collections::BTreeSet::new();
        let mut pending = vec![self];
        while let Some(class) = pending.pop() {
            pending.extend(class.nested.iter().rev());
            references.extend(
                class
                    .methods
                    .iter()
                    .filter_map(|method| method.body.as_ref())
                    .flat_map(JavaMethodBody::method_references),
            );
        }
        references
    }

    pub(in crate::analysis::java_backend) fn field_references(
        &self,
    ) -> std::collections::BTreeSet<crate::ir::FieldReference> {
        let mut references = std::collections::BTreeSet::new();
        let mut pending = vec![self];
        while let Some(class) = pending.pop() {
            pending.extend(class.nested.iter().rev());
            references.extend(
                class
                    .methods
                    .iter()
                    .filter_map(|method| method.body.as_ref())
                    .flat_map(JavaMethodBody::field_references),
            );
        }
        references
    }

    pub(in crate::analysis::java_backend) fn function_interface(
        &self,
    ) -> Option<&crate::ir::generic_types::JvmTypeSignature> {
        self.methods
            .iter()
            .find_map(|method| method.declaration.function_interface.as_ref())
    }

    pub(in crate::analysis::java_backend) fn outer_instances(
        &self,
    ) -> impl Iterator<Item = (&crate::ir::FieldReference, &ArgType)> {
        let mut instances = Vec::new();
        let mut pending = vec![self];
        while let Some(class) = pending.pop() {
            pending.extend(class.nested.iter().rev());
            if let Some(outer) = &class.outer_instance {
                instances.push((&outer.reference, &outer.outer_type));
            }
        }
        instances.into_iter()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::java_backend) struct JavaFieldDeclaration {
    pub annotations: Vec<AnnotationNode>,
    pub modifiers: Vec<JavaModifier>,
    pub field_type: ArgType,
    pub name: JavaIdentifier,
    pub initializer: Option<DexValue>,
    pub access_flags: AccessInfo,
    /// Parsed JVM generic field signature, when the field carries a
    /// `Ldalvik/annotation/Signature;` annotation.
    pub signature: Option<crate::ir::generic_types::JvmTypeSignature>,
}

impl JavaFieldDeclaration {
    pub fn from_field_node(
        field: &FieldNode,
    ) -> Result<Self, crate::ir::generic_types::SignatureError> {
        Ok(Self {
            annotations: field.annotations.clone(),
            modifiers: field_modifiers(&field.access_flags),
            field_type: field.field_type().clone(),
            name: JavaIdentifier::from_dex(field.name()),
            initializer: Self::initial_value(field),
            access_flags: field.access_flags,
            signature: field
                .signature
                .as_deref()
                .map(crate::ir::generic_types::GenericSignatures::field)
                .transpose()?,
        })
    }

    fn initial_value(field: &FieldNode) -> Option<DexValue> {
        field.initial_value.clone().or_else(|| {
            (field.access_flags.is_static() && field.access_flags.is_final())
                .then(|| Self::default_value(field.field_type()))
                .flatten()
        })
    }

    fn default_value(ty: &ArgType) -> Option<DexValue> {
        match ty {
            ArgType::Primitive(PrimitiveType::Boolean) => Some(DexValue::Boolean(false)),
            ArgType::Primitive(PrimitiveType::Byte) => Some(DexValue::Byte(0)),
            ArgType::Primitive(PrimitiveType::Short) => Some(DexValue::Short(0)),
            ArgType::Primitive(PrimitiveType::Char) => Some(DexValue::Char(0)),
            ArgType::Primitive(PrimitiveType::Int) => Some(DexValue::Int(0)),
            ArgType::Primitive(PrimitiveType::Long) => Some(DexValue::Long(0)),
            ArgType::Primitive(PrimitiveType::Float) => Some(DexValue::Float(0.0)),
            ArgType::Primitive(PrimitiveType::Double) => Some(DexValue::Double(0.0)),
            ArgType::Object(_) | ArgType::Array(_) => Some(DexValue::Null),
            ArgType::Primitive(
                PrimitiveType::Void | PrimitiveType::Object | PrimitiveType::Array,
            )
            | ArgType::Unknown(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct JavaClassDeclaration {
    pub annotations: Vec<AnnotationNode>,
    pub package: Option<JavaClassName>,
    pub modifiers: Vec<JavaModifier>,
    pub kind: JavaClassKind,
    pub name: JavaIdentifier,
    pub binary_name: String,
    pub type_descriptor: Option<String>,
    pub extends: Option<ArgType>,
    pub implements: Vec<ArgType>,
    /// `true` when this class is nested inside another class. The renderer
    /// uses this to drop the package line and suppress outer-class-name
    /// qualification.
    pub is_nested: bool,
    pub is_anonymous: bool,
    /// Parsed JVM generic class signature, when the class carries a
    /// `Ldalvik/annotation/Signature;` annotation.
    pub signature: Option<ClassSignature>,
}

impl JavaClassDeclaration {
    pub fn new(name: JavaIdentifier) -> Self {
        Self {
            annotations: Vec::new(),
            package: None,
            modifiers: Vec::new(),
            kind: JavaClassKind::Class,
            name,
            binary_name: String::new(),
            type_descriptor: None,
            extends: None,
            implements: Vec::new(),
            is_nested: false,
            is_anonymous: false,
            signature: None,
        }
    }

    pub(crate) fn from_class_node(
        class: &ClassNode,
    ) -> Result<Self, crate::ir::generic_types::SignatureError> {
        let kind = class_kind(class);
        let extends = class
            .super_class
            .as_ref()
            .and_then(|ty| class_extends(kind, ty));
        let implements = if kind == JavaClassKind::Annotation {
            Vec::new()
        } else {
            class.interfaces.clone()
        };
        let is_inner = class.is_inner();
        let decl_name = declaration_name(class);
        let binary_name = binary_class_name(class);

        let mut decl = Self::new(decl_name)
            .with_binary_name(binary_name)
            .with_type_descriptor(class.type_descriptor())
            .with_modifiers(class_modifiers(class, kind))
            .with_kind(kind)
            .with_extends(extends)
            .with_implements(implements);
        if !is_inner {
            decl = decl.with_package(class.package());
        }
        decl.is_nested = is_inner;
        decl.is_anonymous = class.is_anonymous();
        if let Some(sig) = class.signature.as_deref() {
            decl.signature = Some(crate::ir::generic_types::GenericSignatures::class(sig)?);
        }
        decl.annotations = class.annotations.clone();
        Ok(decl)
    }

    pub fn with_binary_name(mut self, binary_name: impl Into<String>) -> Self {
        self.binary_name = binary_name.into();
        self
    }

    pub fn with_type_descriptor(mut self, descriptor: impl Into<String>) -> Self {
        let descriptor = descriptor.into();
        if !descriptor.is_empty() {
            self.type_descriptor = Some(descriptor);
        }
        self
    }

    pub fn with_package(mut self, package: impl Into<String>) -> Self {
        let package = package.into();
        if !package.is_empty() {
            self.package = Some(JavaClassName::from_source(&package));
        }
        self
    }

    pub fn with_modifiers(mut self, modifiers: Vec<JavaModifier>) -> Self {
        self.modifiers = modifiers;
        self
    }

    pub fn with_kind(mut self, kind: JavaClassKind) -> Self {
        self.kind = kind;
        self
    }

    pub fn with_extends(mut self, extends: Option<ArgType>) -> Self {
        self.extends = extends;
        self
    }

    pub fn with_implements(mut self, implements: Vec<ArgType>) -> Self {
        self.implements = implements;
        self
    }

    pub(in crate::analysis::java_backend) fn current_type(&self) -> Option<ArgType> {
        self.type_descriptor
            .as_deref()
            .and_then(|descriptor| descriptor.parse().ok())
            .or_else(|| {
                let package = self
                    .package
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_default();
                let qualified = if package.is_empty() {
                    self.name.to_string()
                } else {
                    format!("{}.{}", package, self.name).replace('.', "/")
                };
                Some(ArgType::object(&qualified))
            })
    }
}

pub(in crate::analysis::java_backend) fn source_class_name(class: &ClassNode) -> JavaIdentifier {
    JavaIdentifier::from_dex(&binary_class_name(class))
}

pub(in crate::analysis::java_backend) fn declaration_name(class: &ClassNode) -> JavaIdentifier {
    if class.is_inner() {
        return simple_inner_class_name(class);
    }
    source_class_name(class)
}

fn binary_class_name(class: &ClassNode) -> String {
    class
        .type_descriptor()
        .strip_prefix('L')
        .and_then(|name| name.strip_suffix(';'))
        .and_then(|name| name.rsplit('/').next())
        .unwrap_or_else(|| class.name())
        .to_string()
}

/// Simple declaration name for a nested class: the segment after the last `$`
/// in the descriptor's class name. Anonymous classes (`$1`, `$2`, …) get a
/// synthetic `AnonymousN` placeholder since they have no source name.
pub(in crate::analysis::java_backend) fn simple_inner_class_name(
    class: &ClassNode,
) -> JavaIdentifier {
    if let Some(inner) = &class.metadata.inner_class {
        if let Some(name) = &inner.simple_name {
            if is_valid_source_class_name(name) {
                return JavaIdentifier::from_dex(name);
            }
        }
    }
    let descriptor = class.type_descriptor();
    let bare = descriptor
        .strip_prefix('L')
        .and_then(|name| name.strip_suffix(';'))
        .and_then(|name| name.rsplit('/').next())
        .unwrap_or_else(|| class.name());
    let last = bare.rsplit('$').next().unwrap_or(bare);
    if last.is_empty() {
        return JavaIdentifier::from_dex(&anonymous_class_name(bare));
    }
    // Anonymous classes are typically numeric (`$1`, `$2`). Replace with a
    // stable synthetic identifier; otherwise the class keyword would emit
    // `class 1 {` which is invalid Java.
    if last.chars().all(|c| c.is_ascii_digit()) {
        return JavaIdentifier::from_dex(&anonymous_class_name(bare));
    }
    if is_valid_source_class_name(last) {
        JavaIdentifier::from_dex(last)
    } else {
        JavaIdentifier::from_dex(&anonymous_class_name(bare))
    }
}

fn anonymous_class_name(bare_name: &str) -> String {
    // Stable placeholder derived from the trailing numeric id, falling back to
    // a sanitized form of the whole name. The renderer prefixes the class
    // keyword with no modifiers, producing e.g. `class Anonymous1 {`.
    let id = bare_name
        .rsplit('$')
        .find_map(|seg| seg.parse::<u32>().ok())
        .unwrap_or(1);
    format!("Anonymous{}", id)
}

fn is_valid_source_class_name(name: &str) -> bool {
    is_java_identifier(name)
}

fn is_java_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_' || first == '$')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '$')
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum JavaClassKind {
    Class,
    Interface,
    Enum,
    Annotation,
}

fn field_declarations_from_class(
    class: &ClassNode,
    proven_outer: Option<&OuterInstanceField>,
) -> Result<Vec<JavaFieldDeclaration>, crate::ir::generic_types::SignatureError> {
    let outer_instance = proven_outer
        .cloned()
        .or_else(|| OuterInstanceField::analyze(class));
    class
        .fields()
        .iter()
        .filter(|field| {
            !outer_instance
                .as_ref()
                .is_some_and(|outer| outer.matches(field))
        })
        .map(JavaFieldDeclaration::from_field_node)
        .collect()
}

fn class_kind(class: &ClassNode) -> JavaClassKind {
    if class.is_annotation() {
        JavaClassKind::Annotation
    } else if class.is_interface() {
        JavaClassKind::Interface
    } else if class.is_enum() && !class.is_anonymous() {
        JavaClassKind::Enum
    } else {
        JavaClassKind::Class
    }
}

fn class_modifiers(class: &ClassNode, kind: JavaClassKind) -> Vec<JavaModifier> {
    let access = class
        .metadata
        .inner_class
        .as_ref()
        .map(|inner| AccessInfo::for_class(inner.access_flags_raw))
        .unwrap_or(class.access_flags);
    let mut modifiers = Vec::new();

    if access.is_public() {
        modifiers.push(JavaModifier::Public);
    } else if access.is_private() {
        modifiers.push(JavaModifier::Private);
    } else if access.is_protected() {
        modifiers.push(JavaModifier::Protected);
    }

    if access.is_static() {
        modifiers.push(JavaModifier::Static);
    }
    if access.is_final() && kind != JavaClassKind::Enum {
        modifiers.push(JavaModifier::Final);
    }
    if access.is_abstract()
        && !matches!(
            kind,
            JavaClassKind::Interface | JavaClassKind::Annotation | JavaClassKind::Enum
        )
    {
        modifiers.push(JavaModifier::Abstract);
    }
    if access.is_strict() {
        modifiers.push(JavaModifier::StrictFp);
    }

    modifiers
}

fn field_modifiers(access: &AccessInfo) -> Vec<JavaModifier> {
    let mut modifiers = Vec::new();

    if access.is_public() {
        modifiers.push(JavaModifier::Public);
    } else if access.is_private() {
        modifiers.push(JavaModifier::Private);
    } else if access.is_protected() {
        modifiers.push(JavaModifier::Protected);
    }

    if access.is_static() {
        modifiers.push(JavaModifier::Static);
    }
    if access.is_final() {
        modifiers.push(JavaModifier::Final);
    }
    if access.is_transient() {
        modifiers.push(JavaModifier::Transient);
    }
    if access.is_volatile() {
        modifiers.push(JavaModifier::Volatile);
    }

    modifiers
}

fn class_extends(kind: JavaClassKind, ty: &ArgType) -> Option<ArgType> {
    let name = java_type_name(ty);
    if name == "Object"
        || matches!(
            kind,
            JavaClassKind::Interface | JavaClassKind::Annotation | JavaClassKind::Enum
        )
    {
        None
    } else {
        Some(ty.clone())
    }
}

fn java_type_name(ty: &ArgType) -> String {
    match ty {
        ArgType::Object(name) => name
            .rsplit('/')
            .next()
            .unwrap_or(name)
            .rsplit('$')
            .next()
            .unwrap_or(name)
            .to_string(),
        ArgType::Array(elem) => format!("{}[]", java_type_name(elem)),
        _ => ty.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{ClassInfo, InnerClassInfo};

    #[test]
    fn metadata_inner_class_has_one_declaration_name() {
        let info = ClassInfo::from_type_descriptor("Lcom/example/Vz;").expect("class descriptor");
        let mut class = ClassNode::new(0, info, AccessInfo::for_class(0));
        class.metadata.inner_class = Some(InnerClassInfo {
            simple_name: Some("Track".to_string()),
            access_flags_raw: 0,
        });
        class.set_parent_class("Lcom/example/Container;");

        assert_eq!(declaration_name(&class).as_str(), "Track");
    }

    #[test]
    fn class_declaration_does_not_reencode_a_reserved_name() {
        let info = ClassInfo::from_type_descriptor("Lcom/example/do;").expect("class descriptor");
        let class = ClassNode::new(0, info, AccessInfo::for_class(0));

        let declaration = JavaClassDeclaration::from_class_node(&class).expect("class declaration");

        assert_eq!(declaration.name, JavaIdentifier::from_dex("do"));
    }

    #[test]
    fn nested_source_member_preserves_non_static_inner_class_metadata() {
        let info =
            ClassInfo::from_type_descriptor("Lcom/example/Outer$Inner;").expect("class descriptor");
        let mut class = ClassNode::new(0, info, AccessInfo::for_class(0));
        class.metadata.inner_class = Some(InnerClassInfo {
            simple_name: Some("Inner".to_string()),
            access_flags_raw: 0,
        });
        class.set_parent_class("Lcom/example/Outer;");

        let model = JavaClassModel::from_class_node(&class, Vec::new(), None)
            .expect("class model")
            .as_nested_source_member(&class);

        assert!(!model.declaration.modifiers.contains(&JavaModifier::Static));
    }

    #[test]
    fn nested_source_member_preserves_static_inner_class_metadata() {
        let info =
            ClassInfo::from_type_descriptor("Lcom/example/Outer$Inner;").expect("class descriptor");
        let mut class = ClassNode::new(0, info, AccessInfo::for_class(0));
        class.metadata.inner_class = Some(InnerClassInfo {
            simple_name: Some("Inner".to_string()),
            access_flags_raw: 0x0008,
        });
        class.set_parent_class("Lcom/example/Outer;");

        let model = JavaClassModel::from_class_node(&class, Vec::new(), None)
            .expect("class model")
            .as_nested_source_member(&class);

        assert!(model.declaration.modifiers.contains(&JavaModifier::Static));
    }
}
