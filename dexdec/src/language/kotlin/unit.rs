use super::{
    KotlinClassName, KotlinExpr, KotlinIdentifier, KotlinMethodBody, KotlinType,
    KotlinTypeParameter,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinModifier {
    Public,
    Protected,
    Private,
    Internal,
    Lateinit,
    Const,
    Sealed,
    Abstract,
    Open,
    Override,
    Suspend,
    Static,
    Final,
    Transient,
    Volatile,
    Synchronized,
    Native,
    StrictFp,
    Default,
}

impl KotlinModifier {
    pub(crate) const fn token(self) -> &'static str {
        match self {
            Self::Public => "public",
            Self::Protected => "protected",
            Self::Private => "private",
            Self::Internal => "internal",
            Self::Lateinit => "lateinit",
            Self::Const => "const",
            Self::Sealed => "sealed",
            Self::Abstract => "abstract",
            Self::Open => "open",
            Self::Override => "override",
            Self::Suspend => "suspend",
            Self::Static => "",
            Self::Final => "final",
            Self::Transient => "@kotlin.jvm.Transient",
            Self::Volatile => "@kotlin.jvm.Volatile",
            Self::Synchronized => "@kotlin.jvm.Synchronized",
            Self::Native => "external",
            Self::StrictFp => "@kotlin.jvm.Strictfp",
            Self::Default => "",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinTypeDeclarationKind {
    Class,
    Object,
    Interface,
    Enum,
    Annotation,
}

impl KotlinTypeDeclarationKind {
    pub(crate) const fn token(self) -> &'static str {
        match self {
            Self::Class => "class",
            Self::Object => "object",
            Self::Interface => "interface",
            Self::Enum => "enum class",
            Self::Annotation => "annotation class",
        }
    }

    pub const fn is_interface(self) -> bool {
        matches!(self, Self::Interface | Self::Annotation)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinAnnotation {
    pub ty: KotlinType,
    pub elements: Vec<KotlinAnnotationElement>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinAnnotationElement {
    pub name: KotlinIdentifier,
    pub value: KotlinAnnotationValue,
}

#[derive(Debug, Clone, PartialEq)]
pub enum KotlinAnnotationValue {
    Expression(KotlinExpr),
    Annotation(Box<KotlinAnnotation>),
    Array(Vec<KotlinAnnotationValue>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinCompilationUnit {
    pub package: Option<KotlinClassName>,
    pub imports: Vec<KotlinClassName>,
    pub declaration: KotlinTypeDeclaration,
}

/// One entry of a primary constructor: a property the class keeps, or a value
/// it only hands to its supertype.
#[derive(Debug, Clone, PartialEq)]
pub enum KotlinPrimaryParameter {
    Property(KotlinFieldDeclaration),
    Value(KotlinMethodParameter),
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinTypeDeclaration {
    pub annotations: Vec<KotlinAnnotation>,
    pub modifiers: Vec<KotlinModifier>,
    pub kind: KotlinTypeDeclarationKind,
    pub name: KotlinIdentifier,
    pub type_parameters: Vec<KotlinTypeParameter>,
    pub extends: Option<KotlinType>,
    /// Arguments the primary constructor passes to the supertype.
    pub superclass_arguments: Vec<KotlinExpr>,
    pub implements: Vec<KotlinType>,
    pub enum_constants: Vec<KotlinEnumConstant>,
    /// What the class declares in its primary constructor.
    pub primary_parameters: Vec<KotlinPrimaryParameter>,
    pub fields: Vec<KotlinFieldDeclaration>,
    pub properties: Vec<KotlinPropertyDeclaration>,
    pub methods: Vec<KotlinMethodDeclaration>,
    pub nested: Vec<KotlinTypeDeclaration>,
}

impl KotlinTypeDeclaration {
    pub(crate) fn rename(&mut self, name: KotlinIdentifier) {
        self.name = name.clone();
        for method in &mut self.methods {
            if method.kind == KotlinMethodDeclarationKind::Constructor {
                method.name = Some(name.clone());
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinAnonymousClassBody {
    pub super_constructor_call: bool,
    pub fields: Vec<KotlinFieldDeclaration>,
    pub properties: Vec<KotlinPropertyDeclaration>,
    pub methods: Vec<KotlinMethodDeclaration>,
    pub nested: Vec<KotlinTypeDeclaration>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinEnumConstant {
    pub annotations: Vec<KotlinAnnotation>,
    pub name: KotlinIdentifier,
    pub arguments: Vec<KotlinExpr>,
    pub body: Option<KotlinAnonymousClassBody>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinFieldDeclaration {
    pub annotations: Vec<KotlinAnnotation>,
    pub modifiers: Vec<KotlinModifier>,
    pub ty: KotlinType,
    pub name: KotlinIdentifier,
    pub nullable: bool,
    pub initializer: Option<KotlinExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinPropertyDeclaration {
    pub annotations: Vec<KotlinAnnotation>,
    pub modifiers: Vec<KotlinModifier>,
    pub ty: KotlinType,
    pub name: KotlinIdentifier,
    pub nullable: bool,
    pub getter: Option<KotlinMethodBody>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KotlinMethodDeclarationKind {
    Method,
    Constructor,
    ClassInitializer,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinMethodParameter {
    pub annotations: Vec<KotlinAnnotation>,
    pub ty: KotlinType,
    pub name: KotlinIdentifier,
    pub nullable: bool,
    pub varargs: bool,
    pub default_value: Option<KotlinExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinExtensionReceiver {
    pub ty: KotlinType,
    pub nullable: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct KotlinMethodDeclaration {
    pub annotations: Vec<KotlinAnnotation>,
    pub modifiers: Vec<KotlinModifier>,
    pub compiler_generated: bool,
    pub kind: KotlinMethodDeclarationKind,
    pub type_parameters: Vec<KotlinTypeParameter>,
    pub return_type: Option<KotlinType>,
    pub return_nullable: bool,
    pub name: Option<KotlinIdentifier>,
    pub receiver: Option<KotlinExtensionReceiver>,
    pub parameters: Vec<KotlinMethodParameter>,
    pub throws: Vec<KotlinType>,
    pub body: Option<KotlinMethodBody>,
}
