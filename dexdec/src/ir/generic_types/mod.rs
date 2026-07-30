//! JVM generic signature types and parser (JVM spec §4.7.9.1).
//!
//! DEX bytecode carries only erased types, but generic signatures survive as
//! `dalvik/annotation/Signature` strings on classes, fields, and methods. This
//! module parses those strings into a typed AST that the renderer can emit as
//! Kotlin source (`<K, V>`, `Map<K, V>`, `List<? extends Number>`, …).
//!
//! The grammar is a strict subset of the JVM `Signature` attribute grammar:
//!
//! ```text
//! ClassSignature   ::= [TypeParameters] SuperclassSig SuperinterfaceSig*
//! MethodSignature  ::= [TypeParameters] ( KotlinTypeSig* ) KotlinTypeSig
//! FieldSignature   ::= KotlinTypeSig
//! TypeParameters   ::= < TypeParameter+ >
//! TypeParameter    ::= Identifier : [ReferenceTypeSig] (: ReferenceTypeSig)*
//! KotlinTypeSig      ::= ReferenceTypeSig | BaseType
//! ReferenceTypeSig ::= ClassTypeSig | TypeVariableSig | ArrayTypeSig
//! ClassTypeSig     ::= L [Package/] SimpleClassSig ( $SimpleClassSig )* ;
//! SimpleClassSig   ::= Identifier [TypeArguments]
//! TypeArguments    ::= < TypeArgument+ >
//! TypeArgument     ::= * | (+|-) ReferenceTypeSig
//! TypeVariableSig  ::= T Identifier ;
//! ArrayTypeSig     ::= [ KotlinTypeSig
//! ```

use std::collections::BTreeMap;
use std::fmt;

use crate::ir::ty::{ArgType, PrimitiveType};

mod parse;
mod substitute;

use parse::Parser;
use substitute::SignatureSubstitution;

/// A class-level generic signature: type parameters, parameterized super
/// class, parameterized interfaces.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassSignature {
    pub type_parameters: Vec<TypeParameter>,
    pub super_class: ClassTypeSignature,
    pub super_interfaces: Vec<ClassTypeSignature>,
}

/// A method-level generic signature: own type parameters, parameter types,
/// return type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodSignature {
    pub type_parameters: Vec<TypeParameter>,
    pub parameter_types: Vec<JvmTypeSignature>,
    pub return_type: JvmTypeSignature,
    pub throws: Vec<JvmTypeSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericMethodContract {
    pub signature: MethodSignature,
    pub owner: ClassTypeSignature,
    pub owner_parameters: Vec<TypeParameter>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericFieldContract {
    pub signature: JvmTypeSignature,
    pub owner: ClassTypeSignature,
}

impl GenericMethodContract {
    /// Builds the source contract retained by a constructor whose method-level
    /// generic signature is absent but whose declaring class is generic.
    /// Class type parameters still constrain a Kotlin constructor invocation,
    /// even though the bytecode descriptor contains only erased types.
    pub fn erased_constructor(
        owner: ClassTypeSignature,
        owner_parameters: Vec<TypeParameter>,
        parameter_types: &[ArgType],
        throws: &[ArgType],
    ) -> Option<Self> {
        if owner_parameters.is_empty() {
            return None;
        }
        Some(Self {
            signature: MethodSignature {
                type_parameters: Vec::new(),
                parameter_types: parameter_types
                    .iter()
                    .map(JvmTypeSignature::from_erased)
                    .collect::<Option<Vec<_>>>()?,
                return_type: JvmTypeSignature::BaseType(PrimitiveType::Void),
                throws: throws
                    .iter()
                    .map(JvmTypeSignature::from_erased)
                    .collect::<Option<Vec<_>>>()?,
            },
            owner,
            owner_parameters,
        })
    }

    pub fn owner_type_parameters(&self) -> impl Iterator<Item = &str> {
        self.owner
            .type_arguments
            .iter()
            .chain(
                self.owner
                    .inner_segments
                    .iter()
                    .flat_map(|segment| &segment.type_arguments),
            )
            .filter_map(|argument| match argument {
                TypeArgument::Exact(JvmTypeSignature::TypeVariable(name)) => Some(name.as_str()),
                TypeArgument::Unbounded
                | TypeArgument::Extends(_)
                | TypeArgument::Super(_)
                | TypeArgument::Exact(_) => None,
            })
    }

    pub fn owner_is_generic(&self) -> bool {
        self.owner_type_parameters().next().is_some()
    }
}

/// A single type-parameter declaration: `K extends Object` / `T extends Comparable<T>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParameter {
    pub name: String,
    /// First bound (always present; defaults to `Object`). Rendered as
    /// `extends Bound`.
    pub class_bound: Option<JvmTypeSignature>,
    /// Additional interface bounds, rendered as ` & Bound`.
    pub interface_bounds: Vec<JvmTypeSignature>,
}

/// A `JvmTypeSignature`: either a reference type (class/interface/type-var/
/// array) or an erased base type (`int`, `boolean`, …).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JvmTypeSignature {
    ClassType(ClassTypeSignature),
    TypeVariable(String),
    Array(Box<JvmTypeSignature>),
    /// Erased primitive — `V`/`I`/`Z`/etc.
    BaseType(PrimitiveType),
}

/// `Lpkg/Name<...>;` — a class/interface reference with optional type arguments
/// and optional inner-class suffix segments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassTypeSignature {
    /// Raw internal name (`com/example/Map$Entry`).
    pub raw_name: String,
    /// Top-level type arguments (empty when raw).
    pub type_arguments: Vec<TypeArgument>,
    /// Inner-class suffix segments, each with its own type arguments.
    pub inner_segments: Vec<InnerClassTypeSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InnerClassTypeSignature {
    pub simple_name: String,
    pub type_arguments: Vec<TypeArgument>,
}

/// One lexical owner in a possibly nested class type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassTypeScope<'a> {
    erased_name: String,
    type_arguments: &'a [TypeArgument],
}

impl<'a> ClassTypeScope<'a> {
    pub fn erased_name(&self) -> &str {
        &self.erased_name
    }

    pub fn type_arguments(&self) -> &'a [TypeArgument] {
        self.type_arguments
    }
}

/// Outer-to-inner traversal of the lexical owners encoded by a class type.
pub struct ClassTypeScopes<'a> {
    signature: &'a ClassTypeSignature,
    next: usize,
    erased_name: String,
}

impl<'a> Iterator for ClassTypeScopes<'a> {
    type Item = ClassTypeScope<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let type_arguments = if self.next == 0 {
            &self.signature.type_arguments
        } else {
            let segment = self.signature.inner_segments.get(self.next - 1)?;
            self.erased_name.push('$');
            self.erased_name.push_str(&segment.simple_name);
            &segment.type_arguments
        };
        self.next += 1;
        Some(ClassTypeScope {
            erased_name: self.erased_name.clone(),
            type_arguments,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = 1 + self.signature.inner_segments.len() - self.next;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for ClassTypeScopes<'_> {}

/// A single `TypeArgument` inside `<...>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeArgument {
    /// `*` (i.e. `?`)
    Unbounded,
    /// `+T` → `? extends T`
    Extends(JvmTypeSignature),
    /// `-T` → `? super T`
    Super(JvmTypeSignature),
    /// Plain reference type — `String`, `K`, `Map<K, V>`.
    Exact(JvmTypeSignature),
}

pub type TypeSubstitution = BTreeMap<String, TypeArgument>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureError {
    pub offset: usize,
    pub signature: String,
}

impl fmt::Display for SignatureError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "invalid generic signature {:?} at byte {}",
            self.signature, self.offset
        )
    }
}

impl std::error::Error for SignatureError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureSubstitutionError {
    MissingOperand(&'static str),
    ResultArity(usize),
    ExpectedType,
    ExpectedArgument,
    ChangedClassKind,
}

impl fmt::Display for SignatureSubstitutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingOperand(context) => {
                write!(formatter, "generic substitution is missing {context}")
            }
            Self::ResultArity(actual) => {
                write!(
                    formatter,
                    "generic substitution produced {actual} root values"
                )
            }
            Self::ExpectedType => formatter.write_str("expected a generic signature type"),
            Self::ExpectedArgument => formatter.write_str("expected a generic type argument"),
            Self::ChangedClassKind => {
                formatter.write_str("class substitution changed the signature kind")
            }
        }
    }
}

impl std::error::Error for SignatureSubstitutionError {}

/// Strict entry point for JVM generic-signature metadata.
pub struct GenericSignatures;

impl GenericSignatures {
    pub fn class(signature: &str) -> Result<ClassSignature, SignatureError> {
        let mut parser = Parser::new(signature);
        let value = parser.class_signature()?;
        parser.expect_end()?;
        Ok(value)
    }

    pub fn method(signature: &str) -> Result<MethodSignature, SignatureError> {
        let mut parser = Parser::new(signature);
        let value = parser.method_signature()?;
        parser.expect_end()?;
        Ok(value)
    }

    pub fn field(signature: &str) -> Result<JvmTypeSignature, SignatureError> {
        let mut parser = Parser::new(signature);
        let value = parser.field_signature()?;
        parser.expect_end()?;
        Ok(value)
    }
}

impl JvmTypeSignature {
    /// Lifts a concrete descriptor type into the corresponding raw source
    /// signature. Pseudo and unresolved IR types have no source signature.
    pub fn from_erased(ty: &ArgType) -> Option<Self> {
        match ty {
            ArgType::Primitive(PrimitiveType::Object | PrimitiveType::Array)
            | ArgType::Unknown(_) => None,
            ArgType::Primitive(primitive) => Some(Self::BaseType(*primitive)),
            ArgType::Object(name) => Some(Self::ClassType(ClassTypeSignature {
                raw_name: name.clone(),
                type_arguments: Vec::new(),
                inner_segments: Vec::new(),
            })),
            ArgType::Array(element) => {
                Self::from_erased(element).map(|element| Self::Array(Box::new(element)))
            }
        }
    }

    /// Returns the erased `ArgType` for this signature — used for import
    /// collection and as the erased form when no generic metadata is available.
    pub fn erased(&self) -> ArgType {
        let mut dimensions = 0;
        let mut element = self;
        let mut erased = loop {
            match element {
                JvmTypeSignature::Array(inner) => {
                    dimensions += 1;
                    element = inner;
                }
                JvmTypeSignature::ClassType(class) => {
                    break ArgType::object(&class.erased_name());
                }
                JvmTypeSignature::TypeVariable(_) => {
                    break ArgType::object("java/lang/Object");
                }
                JvmTypeSignature::BaseType(primitive) => {
                    break ArgType::Primitive(*primitive);
                }
            }
        };
        for _ in 0..dimensions {
            erased = ArgType::array(erased);
        }
        erased
    }

    pub fn substitute(
        &self,
        substitutions: &TypeSubstitution,
    ) -> Result<JvmTypeSignature, SignatureSubstitutionError> {
        SignatureSubstitution::new(substitutions).ty(self)
    }
}

impl ClassTypeSignature {
    /// `com/example/Map$Entry` (top) → `com/example/Map$Entry` (full erased name).
    pub fn erased_name(&self) -> String {
        let mut name = self.raw_name.clone();
        for inner in &self.inner_segments {
            name.push('$');
            name.push_str(&inner.simple_name);
        }
        name
    }

    pub fn owner_scopes(&self) -> ClassTypeScopes<'_> {
        ClassTypeScopes {
            signature: self,
            next: 0,
            erased_name: self.raw_name.clone(),
        }
    }

    pub fn substitute(
        &self,
        substitutions: &TypeSubstitution,
    ) -> Result<ClassTypeSignature, SignatureSubstitutionError> {
        SignatureSubstitution::new(substitutions).class(self)
    }
}

impl TypeArgument {
    pub fn substitute(
        &self,
        substitutions: &TypeSubstitution,
    ) -> Result<TypeArgument, SignatureSubstitutionError> {
        SignatureSubstitution::new(substitutions).argument(self)
    }
}

impl MethodSignature {
    pub fn parameter_erasures(&self) -> Vec<ArgType> {
        self.parameter_types
            .iter()
            .map(|ty| self.erase(ty, &mut std::collections::BTreeSet::new()))
            .collect()
    }

    /// Erases the return type using this method's declared type-variable
    /// bounds. `JvmTypeSignature::erased` cannot do this without the owning
    /// signature and therefore falls back to `Object` for a type variable.
    pub fn return_erasure(&self) -> ArgType {
        self.erase(&self.return_type, &mut std::collections::BTreeSet::new())
    }

    fn erase(
        &self,
        ty: &JvmTypeSignature,
        visiting: &mut std::collections::BTreeSet<String>,
    ) -> ArgType {
        match ty {
            JvmTypeSignature::Array(element) => ArgType::array(self.erase(element, visiting)),
            JvmTypeSignature::TypeVariable(name) => {
                if !visiting.insert(name.clone()) {
                    return ArgType::object("java/lang/Object");
                }
                let erased = self
                    .type_parameters
                    .iter()
                    .find(|parameter| parameter.name == *name)
                    .and_then(|parameter| {
                        parameter
                            .class_bound
                            .as_ref()
                            .or_else(|| parameter.interface_bounds.first())
                    })
                    .map(|bound| self.erase(bound, visiting))
                    .unwrap_or_else(|| ArgType::object("java/lang/Object"));
                visiting.remove(name);
                erased
            }
            JvmTypeSignature::ClassType(_) | JvmTypeSignature::BaseType(_) => ty.erased(),
        }
    }

    pub fn substitute(
        &self,
        substitutions: &TypeSubstitution,
    ) -> Result<MethodSignature, SignatureSubstitutionError> {
        let mut filtered = substitutions.clone();
        for type_parameter in &self.type_parameters {
            filtered.remove(&type_parameter.name);
        }
        Ok(MethodSignature {
            type_parameters: self
                .type_parameters
                .iter()
                .map(|type_parameter| type_parameter.substitute_bounds(&filtered))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: self
                .parameter_types
                .iter()
                .map(|parameter| parameter.substitute(&filtered))
                .collect::<Result<Vec<_>, _>>()?,
            return_type: self.return_type.substitute(&filtered)?,
            throws: self
                .throws
                .iter()
                .map(|exception| exception.substitute(&filtered))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

impl TypeParameter {
    pub fn substitute_bounds(
        &self,
        substitutions: &TypeSubstitution,
    ) -> Result<TypeParameter, SignatureSubstitutionError> {
        Ok(TypeParameter {
            name: self.name.clone(),
            class_bound: self
                .class_bound
                .as_ref()
                .map(|bound| bound.substitute(substitutions))
                .transpose()?,
            interface_bounds: self
                .interface_bounds
                .iter()
                .map(|bound| bound.substitute(substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substitution_preserves_wildcard_variance_in_type_arguments() {
        let variable = JvmTypeSignature::TypeVariable("E".to_string());
        let collection = ClassTypeSignature {
            raw_name: "java/util/Collection".to_string(),
            type_arguments: vec![TypeArgument::Exact(JvmTypeSignature::TypeVariable(
                "T".to_string(),
            ))],
            inner_segments: Vec::new(),
        };
        let substitutions =
            TypeSubstitution::from([("T".to_string(), TypeArgument::Extends(variable.clone()))]);

        let substituted = collection.substitute(&substitutions).unwrap();

        assert_eq!(
            substituted.type_arguments,
            vec![TypeArgument::Extends(variable)]
        );
    }

    #[test]
    fn parses_class_signature_with_two_type_parameters() {
        let sig = GenericSignatures::class(
            "<K:Ljava/lang/Object;V:Ljava/lang/Object;>Ljava/util/AbstractMap<TK;TV;>;Ljava/io/Serializable;",
        )
        .unwrap();
        assert_eq!(sig.type_parameters.len(), 2);
        assert_eq!(sig.type_parameters[0].name, "K");
        assert_eq!(sig.super_class.raw_name, "java/util/AbstractMap");
        assert_eq!(sig.super_class.type_arguments.len(), 2);
        assert_eq!(sig.super_interfaces.len(), 1);
        assert_eq!(sig.super_interfaces[0].raw_name, "java/io/Serializable");
    }

    #[test]
    fn traverses_nested_class_owners_with_local_arguments() {
        let JvmTypeSignature::ClassType(signature) = GenericSignatures::field(
            "Lcom/example/Outer<Ljava/lang/String;Ljava/lang/Integer;>.Inner<Ljava/lang/Long;>;",
        )
        .unwrap() else {
            panic!("expected class type");
        };
        let scopes = signature.owner_scopes().collect::<Vec<_>>();

        assert_eq!(scopes.len(), 2);
        assert_eq!(scopes[0].erased_name(), "com/example/Outer");
        assert_eq!(scopes[0].type_arguments().len(), 2);
        assert_eq!(scopes[1].erased_name(), "com/example/Outer$Inner");
        assert_eq!(scopes[1].type_arguments().len(), 1);
    }

    #[test]
    fn parses_method_signature_with_type_vars() {
        let sig = GenericSignatures::method("(TK;TV;)TV;").unwrap();
        assert!(sig.type_parameters.is_empty());
        assert_eq!(sig.parameter_types.len(), 2);
        assert!(matches!(
            sig.parameter_types[0],
            JvmTypeSignature::TypeVariable(_)
        ));
        assert!(matches!(sig.return_type, JvmTypeSignature::TypeVariable(_)));
    }

    #[test]
    fn parses_field_signature_with_inner_class() {
        let ty = GenericSignatures::field("Lcom/google/gson/internal/LinkedTreeMap$Node<TK;TV;>;")
            .unwrap();
        match ty {
            JvmTypeSignature::ClassType(c) => {
                assert_eq!(c.raw_name, "com/google/gson/internal/LinkedTreeMap");
                assert_eq!(c.inner_segments.len(), 1);
                assert_eq!(c.inner_segments[0].simple_name, "Node");
                assert_eq!(c.inner_segments[0].type_arguments.len(), 2);
            }
            _ => panic!("expected class type"),
        }
    }

    #[test]
    fn parses_wildcard_extends() {
        let ty = GenericSignatures::field("Ljava/util/List<+Ljava/lang/Number;>;").unwrap();
        match ty {
            JvmTypeSignature::ClassType(c) => {
                assert_eq!(c.type_arguments.len(), 1);
                assert!(matches!(c.type_arguments[0], TypeArgument::Extends(_)));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn parses_unbounded_wildcards() {
        let ty = GenericSignatures::field("Ljava/util/Map<**>;").unwrap();
        match ty {
            JvmTypeSignature::ClassType(c) => {
                assert_eq!(c.type_arguments.len(), 2);
                assert!(matches!(c.type_arguments[0], TypeArgument::Unbounded));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn erased_argtype_for_type_variable_is_object() {
        let ty = GenericSignatures::field("TK;").unwrap();
        assert_eq!(ty.erased(), ArgType::object("java/lang/Object"));
    }

    #[test]
    fn accepts_terminal_dex_field_type_variable_without_semicolon() {
        let ty = GenericSignatures::field("TV").unwrap();
        assert_eq!(ty, JvmTypeSignature::TypeVariable("V".to_string()));
    }

    #[test]
    fn parses_generic_method_with_own_type_parameter() {
        // `<T> T identity(T)` → signature `<T:Ljava/lang/Object;>(TT;)TT;`
        let sig = GenericSignatures::method("<T:Ljava/lang/Object;>(TT;)TT;").unwrap();
        assert_eq!(sig.type_parameters.len(), 1);
        assert_eq!(sig.type_parameters[0].name, "T");
        assert_eq!(sig.parameter_types.len(), 1);
    }

    #[test]
    fn method_return_erasure_uses_type_variable_bound() {
        let sig = GenericSignatures::method(
            "<T:Ljava/security/spec/KeySpec;>(Ljava/lang/Class<TT;>;)TT;",
        )
        .unwrap();

        assert_eq!(
            sig.return_erasure(),
            ArgType::object("java/security/spec/KeySpec")
        );
    }
}
