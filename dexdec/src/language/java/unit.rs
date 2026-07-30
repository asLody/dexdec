use super::{JavaClassName, JavaExpr, JavaIdentifier, JavaMethodBody, JavaType, JavaTypeParameter};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JavaModifier {
    Public,
    Protected,
    Private,
    Abstract,
    Static,
    Final,
    Transient,
    Volatile,
    Synchronized,
    Native,
    StrictFp,
    Default,
}

impl JavaModifier {
    pub(crate) const fn token(self) -> &'static str {
        match self {
            Self::Public => "public",
            Self::Protected => "protected",
            Self::Private => "private",
            Self::Abstract => "abstract",
            Self::Static => "static",
            Self::Final => "final",
            Self::Transient => "transient",
            Self::Volatile => "volatile",
            Self::Synchronized => "synchronized",
            Self::Native => "native",
            Self::StrictFp => "strictfp",
            Self::Default => "default",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JavaTypeDeclarationKind {
    Class,
    Interface,
    Enum,
    Annotation,
}

impl JavaTypeDeclarationKind {
    pub(crate) const fn token(self) -> &'static str {
        match self {
            Self::Class => "class",
            Self::Interface => "interface",
            Self::Enum => "enum",
            Self::Annotation => "@interface",
        }
    }

    pub const fn is_interface(self) -> bool {
        matches!(self, Self::Interface | Self::Annotation)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaAnnotation {
    pub ty: JavaType,
    pub elements: Vec<JavaAnnotationElement>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaAnnotationElement {
    pub name: JavaIdentifier,
    pub value: JavaAnnotationValue,
}

#[derive(Debug, Clone, PartialEq)]
pub enum JavaAnnotationValue {
    Expression(JavaExpr),
    Annotation(Box<JavaAnnotation>),
    Array(Vec<JavaAnnotationValue>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaCompilationUnit {
    pub package: Option<JavaClassName>,
    pub imports: Vec<JavaClassName>,
    pub declaration: JavaTypeDeclaration,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaTypeDeclaration {
    pub annotations: Vec<JavaAnnotation>,
    pub modifiers: Vec<JavaModifier>,
    pub kind: JavaTypeDeclarationKind,
    pub name: JavaIdentifier,
    pub type_parameters: Vec<JavaTypeParameter>,
    pub extends: Option<JavaType>,
    pub implements: Vec<JavaType>,
    pub enum_constants: Vec<JavaEnumConstant>,
    pub fields: Vec<JavaFieldDeclaration>,
    pub methods: Vec<JavaMethodDeclaration>,
    pub nested: Vec<JavaTypeDeclaration>,
}

impl JavaTypeDeclaration {
    pub(crate) fn rename(&mut self, name: JavaIdentifier) {
        self.name = name.clone();
        for method in &mut self.methods {
            if method.kind == JavaMethodDeclarationKind::Constructor {
                method.name = Some(name.clone());
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaAnonymousClassBody {
    pub fields: Vec<JavaFieldDeclaration>,
    pub methods: Vec<JavaMethodDeclaration>,
    pub nested: Vec<JavaTypeDeclaration>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaEnumConstant {
    pub annotations: Vec<JavaAnnotation>,
    pub name: JavaIdentifier,
    pub arguments: Vec<JavaExpr>,
    pub body: Option<JavaAnonymousClassBody>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaFieldDeclaration {
    pub annotations: Vec<JavaAnnotation>,
    pub modifiers: Vec<JavaModifier>,
    pub ty: JavaType,
    pub name: JavaIdentifier,
    pub initializer: Option<JavaExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JavaMethodDeclarationKind {
    Method,
    Constructor,
    ClassInitializer,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaMethodParameter {
    pub annotations: Vec<JavaAnnotation>,
    pub ty: JavaType,
    pub name: JavaIdentifier,
    pub varargs: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct JavaMethodDeclaration {
    pub annotations: Vec<JavaAnnotation>,
    pub modifiers: Vec<JavaModifier>,
    pub compiler_generated: bool,
    pub kind: JavaMethodDeclarationKind,
    pub type_parameters: Vec<JavaTypeParameter>,
    pub return_type: Option<JavaType>,
    pub name: Option<JavaIdentifier>,
    pub parameters: Vec<JavaMethodParameter>,
    pub throws: Vec<JavaType>,
    pub body: Option<JavaMethodBody>,
}
