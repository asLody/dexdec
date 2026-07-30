use crate::frontend::{AccessInfo, AnnotationNode, ClassNode, DexValue, FieldNode};
use crate::ir::generic_types::ClassSignature;
use crate::ir::ty::{ArgType, PrimitiveType};
use crate::language::kotlin::{KotlinClassName, KotlinIdentifier, KotlinModifier};

use super::method::{KotlinMethodBody, KotlinMethodModel};
use super::source_abi::{EnclosingInstanceAbi, FunctionObjectClass, OuterInstanceField};

#[derive(Debug, Clone)]
pub(in crate::analysis::kotlin_backend) struct KotlinClassModel {
    pub declaration: KotlinClassDeclaration,
    pub fields: Vec<KotlinFieldDeclaration>,
    pub methods: Vec<KotlinMethodModel>,
    pub function_object: bool,
    pub outer_instance: Option<OuterInstanceField>,
    /// Inner classes to render nested inside this class body, in declaration
    /// order. Each entry is itself a fully-formed `KotlinClassModel` so the
    /// renderer can recurse at the next indentation level.
    pub nested: Vec<KotlinClassModel>,
}

impl KotlinClassModel {
    pub fn from_class_node(
        class: &ClassNode,
        methods: Vec<KotlinMethodModel>,
        outer_instance: Option<OuterInstanceField>,
    ) -> Result<Self, crate::ir::generic_types::SignatureError> {
        Ok(Self {
            declaration: KotlinClassDeclaration::from_class_node(class)?,
            fields: field_declarations_from_class(class, outer_instance.as_ref())?,
            methods,
            function_object: FunctionObjectClass::analyze(class),
            outer_instance,
            nested: Vec::new(),
        })
    }

    pub fn with_nested(mut self, nested: Vec<KotlinClassModel>) -> Self {
        self.nested = nested;
        self
    }

    /// Assigns declaration names after the complete lexical type tree exists.
    /// Anonymous DEX names repeat at each nesting level (`$1$1$1`), while Kotlin
    /// forbids a member type from reusing any enclosing type name. A top-down
    /// allocation keeps the descriptor-to-source-type mapping injective before
    /// signatures and method bodies are lowered.
    pub(in crate::analysis::kotlin_backend) fn assign_lexical_type_names(
        &mut self,
        source_abi: &super::source_abi::KotlinSourceAbi,
    ) {
        Self::assign_nested_type_names(self, &[], source_abi);
    }

    fn assign_nested_type_names(
        owner: &mut Self,
        inherited: &[KotlinIdentifier],
        source_abi: &super::source_abi::KotlinSourceAbi,
    ) {
        let mut lexical = inherited.to_vec();
        lexical.push(owner.declaration.name.clone());
        if let Some(signature) = &owner.declaration.signature {
            lexical.extend(
                signature
                    .type_parameters
                    .iter()
                    .map(|parameter| KotlinIdentifier::from_dex(&parameter.name)),
            );
        }

        let mut assigned = std::collections::BTreeSet::new();
        for nested in &mut owner.nested {
            let mut scope = crate::language::kotlin::KotlinNameScope::default();
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
            && !self.declaration.modifiers.contains(&KotlinModifier::Static)
        {
            self.declaration.modifiers.push(KotlinModifier::Static);
        }
        self
    }

    pub(in crate::analysis::kotlin_backend) fn method_references(
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
                    .flat_map(KotlinMethodBody::method_references),
            );
        }
        references
    }

    pub(in crate::analysis::kotlin_backend) fn field_references(
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
                    .flat_map(KotlinMethodBody::field_references),
            );
        }
        references
    }

    pub(in crate::analysis::kotlin_backend) fn function_interface(
        &self,
    ) -> Option<&crate::ir::generic_types::JvmTypeSignature> {
        self.methods
            .iter()
            .find_map(|method| method.declaration.function_interface.as_ref())
    }

    pub(in crate::analysis::kotlin_backend) fn outer_instances(
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
pub(in crate::analysis::kotlin_backend) struct KotlinFieldDeclaration {
    pub annotations: Vec<AnnotationNode>,
    pub modifiers: Vec<KotlinModifier>,
    pub field_type: ArgType,
    pub name: KotlinIdentifier,
    pub initializer: Option<DexValue>,
    pub access_flags: AccessInfo,
    /// Parsed JVM generic field signature, when the field carries a
    /// `Ldalvik/annotation/Signature;` annotation.
    pub signature: Option<crate::ir::generic_types::JvmTypeSignature>,
}

impl KotlinFieldDeclaration {
    pub fn from_field_node(
        field: &FieldNode,
    ) -> Result<Self, crate::ir::generic_types::SignatureError> {
        Ok(Self {
            annotations: field.annotations.clone(),
            modifiers: field_modifiers(&field.access_flags),
            field_type: field.field_type().clone(),
            name: KotlinIdentifier::from_dex(field.name()),
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
pub(crate) struct KotlinClassDeclaration {
    pub annotations: Vec<AnnotationNode>,
    pub package: Option<KotlinClassName>,
    pub modifiers: Vec<KotlinModifier>,
    pub kind: KotlinClassKind,
    pub name: KotlinIdentifier,
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

impl KotlinClassDeclaration {
    pub fn new(name: KotlinIdentifier) -> Self {
        Self {
            annotations: Vec::new(),
            package: None,
            modifiers: Vec::new(),
            kind: KotlinClassKind::Class,
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
        let implements = if kind == KotlinClassKind::Annotation {
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
            self.package = Some(KotlinClassName::from_source(&package));
        }
        self
    }

    pub fn with_modifiers(mut self, modifiers: Vec<KotlinModifier>) -> Self {
        self.modifiers = modifiers;
        self
    }

    pub fn with_kind(mut self, kind: KotlinClassKind) -> Self {
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

    pub(in crate::analysis::kotlin_backend) fn current_type(&self) -> Option<ArgType> {
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

pub(in crate::analysis::kotlin_backend) fn source_class_name(
    class: &ClassNode,
) -> KotlinIdentifier {
    KotlinIdentifier::from_dex(&binary_class_name(class))
}

pub(in crate::analysis::kotlin_backend) fn declaration_name(class: &ClassNode) -> KotlinIdentifier {
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
pub(in crate::analysis::kotlin_backend) fn simple_inner_class_name(
    class: &ClassNode,
) -> KotlinIdentifier {
    if let Some(inner) = &class.metadata.inner_class {
        if let Some(name) = &inner.simple_name {
            if is_valid_source_class_name(name) {
                return KotlinIdentifier::from_dex(name);
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
        return KotlinIdentifier::from_dex(&anonymous_class_name(bare));
    }
    // Anonymous classes are typically numeric (`$1`, `$2`). Replace with a
    // stable synthetic identifier; otherwise the class keyword would emit
    // `class 1 {` which is invalid Kotlin.
    if last.chars().all(|c| c.is_ascii_digit()) {
        return KotlinIdentifier::from_dex(&anonymous_class_name(bare));
    }
    if is_valid_source_class_name(last) {
        KotlinIdentifier::from_dex(last)
    } else {
        KotlinIdentifier::from_dex(&anonymous_class_name(bare))
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
pub(crate) enum KotlinClassKind {
    Class,
    Interface,
    Enum,
    Annotation,
}

fn field_declarations_from_class(
    class: &ClassNode,
    proven_outer: Option<&OuterInstanceField>,
) -> Result<Vec<KotlinFieldDeclaration>, crate::ir::generic_types::SignatureError> {
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
        .map(KotlinFieldDeclaration::from_field_node)
        .collect()
}

fn class_kind(class: &ClassNode) -> KotlinClassKind {
    if class.is_annotation() {
        KotlinClassKind::Annotation
    } else if class.is_interface() {
        KotlinClassKind::Interface
    } else if class.is_enum() && !class.is_anonymous() {
        KotlinClassKind::Enum
    } else {
        KotlinClassKind::Class
    }
}

fn class_modifiers(class: &ClassNode, kind: KotlinClassKind) -> Vec<KotlinModifier> {
    let access = class
        .metadata
        .inner_class
        .as_ref()
        .map(|inner| AccessInfo::for_class(inner.access_flags_raw))
        .unwrap_or(class.access_flags);
    let mut modifiers = Vec::new();

    if access.is_public() {
        modifiers.push(KotlinModifier::Public);
    } else if access.is_private() {
        modifiers.push(KotlinModifier::Private);
    } else if access.is_protected() {
        modifiers.push(KotlinModifier::Protected);
    }

    if access.is_static() {
        modifiers.push(KotlinModifier::Static);
    }
    if access.is_final() && kind != KotlinClassKind::Enum {
        modifiers.push(KotlinModifier::Final);
    }
    if access.is_abstract()
        && !matches!(
            kind,
            KotlinClassKind::Interface | KotlinClassKind::Annotation | KotlinClassKind::Enum
        )
    {
        modifiers.push(KotlinModifier::Abstract);
    }
    if kind == KotlinClassKind::Class && !access.is_final() && !access.is_abstract() {
        modifiers.push(KotlinModifier::Open);
    }
    if access.is_strict() {
        modifiers.push(KotlinModifier::StrictFp);
    }

    modifiers
}

fn field_modifiers(access: &AccessInfo) -> Vec<KotlinModifier> {
    let mut modifiers = Vec::new();

    if access.is_public() {
        modifiers.push(KotlinModifier::Public);
    } else if access.is_private() {
        modifiers.push(KotlinModifier::Private);
    } else if access.is_protected() {
        modifiers.push(KotlinModifier::Protected);
    }

    if access.is_static() {
        modifiers.push(KotlinModifier::Static);
    }
    if access.is_final() {
        modifiers.push(KotlinModifier::Final);
    }
    if access.is_transient() {
        modifiers.push(KotlinModifier::Transient);
    }
    if access.is_volatile() {
        modifiers.push(KotlinModifier::Volatile);
    }

    modifiers
}

fn class_extends(kind: KotlinClassKind, ty: &ArgType) -> Option<ArgType> {
    let name = java_type_name(ty);
    if name == "Object"
        || matches!(
            kind,
            KotlinClassKind::Interface | KotlinClassKind::Annotation | KotlinClassKind::Enum
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

        let declaration =
            KotlinClassDeclaration::from_class_node(&class).expect("class declaration");

        assert_eq!(declaration.name, KotlinIdentifier::from_dex("do"));
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

        let model = KotlinClassModel::from_class_node(&class, Vec::new(), None)
            .expect("class model")
            .as_nested_source_member(&class);

        assert!(!model
            .declaration
            .modifiers
            .contains(&KotlinModifier::Static));
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

        let model = KotlinClassModel::from_class_node(&class, Vec::new(), None)
            .expect("class model")
            .as_nested_source_member(&class);

        assert!(model
            .declaration
            .modifiers
            .contains(&KotlinModifier::Static));
    }
}
