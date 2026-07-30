use std::collections::{BTreeMap, BTreeSet};

use crate::ir::ty::ArgType;
use crate::language::java::{
    JavaClassName, JavaClassType, JavaIdentifier, JavaPrimitiveType, JavaType, JavaTypeArgument,
    JavaTypeParameter,
};

use super::java_model::JavaClassModel;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JavaTypeNameError {
    Unresolved(ArgType),
    InvalidPrimitive(crate::ir::ty::PrimitiveType),
}

impl std::fmt::Display for JavaTypeNameError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unresolved(ty) => write!(formatter, "Java source type is unresolved: {ty}"),
            Self::InvalidPrimitive(primitive) => {
                write!(formatter, "{primitive:?} has no Java primitive source type")
            }
        }
    }
}

impl std::error::Error for JavaTypeNameError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Unresolved(_) | Self::InvalidPrimitive(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct JavaTypeNameResolver {
    imports: BTreeSet<String>,
    simple_names: BTreeMap<String, String>,
    declarations: DeclaredTypes,
    lexical_scope: JavaLexicalTypeScope,
}

impl JavaTypeNameResolver {
    pub(super) fn new(
        current_package: Option<&str>,
        current_type: Option<&ArgType>,
        types: impl IntoIterator<Item = ArgType>,
    ) -> Result<Self, JavaTypeNameError> {
        Self::build(
            current_package,
            current_type,
            types,
            DeclaredTypes::default(),
        )
    }

    pub(super) fn for_class(
        class: &JavaClassModel,
        current_package: Option<&str>,
        current_type: Option<&ArgType>,
        types: impl IntoIterator<Item = ArgType>,
    ) -> Result<Self, JavaTypeNameError> {
        Self::build(
            current_package,
            current_type,
            types,
            DeclaredTypes::collect(class),
        )
    }

    fn build(
        current_package: Option<&str>,
        current_type: Option<&ArgType>,
        types: impl IntoIterator<Item = ArgType>,
        declarations: DeclaredTypes,
    ) -> Result<Self, JavaTypeNameError> {
        let current_package = current_package
            .filter(|package| !package.is_empty())
            .map(ToOwned::to_owned);
        let lexical_scope =
            JavaLexicalTypeScope::new(current_type.and_then(Self::type_binary_name));
        let mut collector = JavaTypeImportCollector::default();
        for ty in types {
            collector.collect_type(&ty)?;
        }

        let simple_counts = collector.simple_counts();
        let mut imports = BTreeSet::new();
        let mut simple_names = BTreeMap::new();
        for binary_name in collector.into_binary_names() {
            if declarations.resolve(&binary_name).is_some() {
                continue;
            }
            let name = JavaTypeName::from_binary_name(&binary_name);
            let Some(name) = name.as_ref() else {
                simple_names.insert(binary_name.clone(), binary_name.clone());
                continue;
            };
            let has_conflicting_simple_name =
                simple_counts.get(&name.simple).copied().unwrap_or_default() > 1
                    || declarations.reserves(&name.simple);
            if has_conflicting_simple_name {
                simple_names.insert(binary_name, name.qualified_source_name());
                continue;
            }
            if name.package.as_deref() == Some("java.lang") || name.package == current_package {
                simple_names.insert(binary_name, name.source_name());
                continue;
            }
            imports.insert(name.import_name());
            simple_names.insert(binary_name, name.source_name());
        }

        Ok(Self {
            imports,
            simple_names,
            declarations,
            lexical_scope,
        })
    }

    pub(super) fn imports(&self) -> impl Iterator<Item = JavaClassName> + '_ {
        self.imports
            .iter()
            .map(|name| JavaClassName::from_source(name))
    }

    pub(super) fn resolve_type(&self, ty: &ArgType) -> Result<JavaType, JavaTypeNameError> {
        self.resolve_type_in(ty, false)
    }

    pub(super) fn resolve_header_type(&self, ty: &ArgType) -> Result<JavaType, JavaTypeNameError> {
        self.resolve_type_in(ty, true)
    }

    fn resolve_type_in(&self, ty: &ArgType, header: bool) -> Result<JavaType, JavaTypeNameError> {
        Ok(match ty {
            ArgType::Primitive(primitive) => JavaType::Primitive(primitive_type(*primitive)?),
            ArgType::Object(name) => JavaType::Class(self.resolve_object_type_in(name, header)),
            ArgType::Array(element) => JavaType::array(self.resolve_type_in(element, header)?),
            ArgType::Unknown(_) => return Err(JavaTypeNameError::Unresolved(ty.clone())),
        })
    }

    pub(super) fn resolve_generic_type(
        &self,
        signature: &crate::ir::generic_types::JvmTypeSignature,
    ) -> Result<JavaType, JavaTypeNameError> {
        GenericTypeResolver::new(self, false).resolve(signature)
    }

    pub(super) fn resolve_header_generic_type(
        &self,
        signature: &crate::ir::generic_types::JvmTypeSignature,
    ) -> Result<JavaType, JavaTypeNameError> {
        GenericTypeResolver::new(self, true).resolve(signature)
    }

    pub(super) fn source_signature(
        &self,
        ty: &JavaType,
    ) -> Option<crate::ir::generic_types::JvmTypeSignature> {
        use crate::ir::generic_types::JvmTypeSignature;
        Some(match ty {
            JavaType::Primitive(primitive) => JvmTypeSignature::BaseType(match primitive {
                JavaPrimitiveType::Void => crate::ir::PrimitiveType::Void,
                JavaPrimitiveType::Boolean => crate::ir::PrimitiveType::Boolean,
                JavaPrimitiveType::Byte => crate::ir::PrimitiveType::Byte,
                JavaPrimitiveType::Short => crate::ir::PrimitiveType::Short,
                JavaPrimitiveType::Char => crate::ir::PrimitiveType::Char,
                JavaPrimitiveType::Int => crate::ir::PrimitiveType::Int,
                JavaPrimitiveType::Long => crate::ir::PrimitiveType::Long,
                JavaPrimitiveType::Float => crate::ir::PrimitiveType::Float,
                JavaPrimitiveType::Double => crate::ir::PrimitiveType::Double,
            }),
            JavaType::Variable(name) => JvmTypeSignature::TypeVariable(name.to_string()),
            JavaType::Array(element) => {
                JvmTypeSignature::Array(Box::new(self.source_signature(element)?))
            }
            JavaType::Class(class) => {
                JvmTypeSignature::ClassType(self.source_class_signature(class)?)
            }
        })
    }

    pub(super) fn resolve_type_parameters(
        &self,
        parameters: &[crate::ir::generic_types::TypeParameter],
    ) -> Result<Vec<JavaTypeParameter>, JavaTypeNameError> {
        self.resolve_type_parameters_in(parameters, false)
    }

    pub(super) fn resolve_header_type_parameters(
        &self,
        parameters: &[crate::ir::generic_types::TypeParameter],
    ) -> Result<Vec<JavaTypeParameter>, JavaTypeNameError> {
        self.resolve_type_parameters_in(parameters, true)
    }

    fn resolve_type_parameters_in(
        &self,
        parameters: &[crate::ir::generic_types::TypeParameter],
        header: bool,
    ) -> Result<Vec<JavaTypeParameter>, JavaTypeNameError> {
        let resolver = GenericTypeResolver::new(self, header);
        parameters
            .iter()
            .map(|parameter| {
                let mut bounds = Vec::new();
                if let Some(bound) = &parameter.class_bound {
                    if !is_java_lang_object(bound) {
                        bounds.push(resolver.resolve(bound)?);
                    }
                }
                for bound in &parameter.interface_bounds {
                    if !is_java_lang_object(bound) {
                        bounds.push(resolver.resolve(bound)?);
                    }
                }
                Ok(JavaTypeParameter {
                    name: JavaIdentifier::from_dex(&parameter.name),
                    bounds,
                })
            })
            .collect()
    }

    fn resolve_object_type(&self, internal_name: &str) -> JavaClassType {
        self.resolve_object_type_in(internal_name, false)
    }

    fn resolve_object_type_in(&self, internal_name: &str, header: bool) -> JavaClassType {
        let full_name = JavaTypeName::internal_to_binary_name(internal_name);
        if header {
            if let Some(source_type) = self.declarations.header(&full_name) {
                return source_type.clone();
            }
        }
        if let Some(source_type) = self.declarations.resolve(&full_name) {
            return source_type.clone();
        }
        if let Some(relative_name) = self.lexical_scope.relative_name(&full_name) {
            return JavaClassType::from_source(&relative_name);
        }
        let source_name = self
            .simple_names
            .get(&full_name)
            .cloned()
            .unwrap_or_else(|| JavaTypeName::implicit_or_qualified_source_name(&full_name));
        JavaClassType::from_source(&source_name)
    }

    fn type_binary_name(ty: &ArgType) -> Option<String> {
        let ArgType::Object(name) = ty else {
            return None;
        };
        Some(JavaTypeName::internal_to_binary_name(
            name.strip_prefix('L')
                .and_then(|name| name.strip_suffix(';'))
                .unwrap_or(name),
        ))
    }

    fn source_class_signature(
        &self,
        class: &JavaClassType,
    ) -> Option<crate::ir::generic_types::ClassTypeSignature> {
        use crate::ir::generic_types::{ClassTypeSignature, InnerClassTypeSignature};

        let source_name = class.name().to_string();
        let binary_name = self
            .simple_names
            .iter()
            .find_map(|(binary, source)| (source == &source_name).then(|| binary.clone()))
            .or_else(|| {
                self.declarations
                    .source_names
                    .iter()
                    .chain(&self.declarations.header_names)
                    .find_map(|(binary, source)| {
                        (source.name().to_string() == source_name).then(|| binary.clone())
                    })
            })
            .or_else(|| {
                let candidates = self
                    .simple_names
                    .keys()
                    .chain(self.declarations.source_names.keys())
                    .chain(self.declarations.header_names.keys())
                    .filter(|binary| {
                        self.lexical_scope.relative_name(binary).as_deref()
                            == Some(source_name.as_str())
                    })
                    .cloned()
                    .collect::<BTreeSet<_>>();
                (candidates.len() == 1)
                    .then(|| candidates.into_iter().next())
                    .flatten()
            })
            .or_else(|| {
                self.simple_names
                    .keys()
                    .chain(self.declarations.source_names.keys())
                    .chain(self.declarations.header_names.keys())
                    .find_map(|binary| {
                        JavaTypeName::from_binary_name(binary)
                            .filter(|name| name.qualified_source_name() == source_name)
                            .map(|_| binary.clone())
                    })
            })?;
        let name = JavaTypeName::from_binary_name(&binary_name)?;
        let binary_segments = name.segment_count();
        let source_offset = binary_segments.checked_sub(class.segments.len())?;
        let source_segment = |binary_index: usize| {
            binary_index
                .checked_sub(source_offset)
                .and_then(|index| class.segments.get(index))
        };
        let raw_name = match &name.package {
            Some(package) => format!("{}/{}", package.replace('.', "/"), name.top_level),
            None => name.top_level.clone(),
        };
        let inner_segments = name
            .nested
            .iter()
            .enumerate()
            .map(|(index, simple_name)| {
                let arguments = source_segment(index + 1)
                    .map(|source| source.arguments.as_slice())
                    .unwrap_or_default();
                Some(InnerClassTypeSignature {
                    simple_name: simple_name.clone(),
                    type_arguments: arguments
                        .iter()
                        .map(|argument| self.source_type_argument(argument))
                        .collect::<Option<Vec<_>>>()?,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(ClassTypeSignature {
            raw_name,
            type_arguments: source_segment(0)
                .map(|source| source.arguments.as_slice())
                .unwrap_or_default()
                .iter()
                .map(|argument| self.source_type_argument(argument))
                .collect::<Option<Vec<_>>>()?,
            inner_segments,
        })
    }

    fn source_type_argument(
        &self,
        argument: &JavaTypeArgument,
    ) -> Option<crate::ir::generic_types::TypeArgument> {
        use crate::ir::generic_types::TypeArgument;
        Some(match argument {
            JavaTypeArgument::Any => TypeArgument::Unbounded,
            JavaTypeArgument::Exact(ty) => TypeArgument::Exact(self.source_signature(ty)?),
            JavaTypeArgument::Extends(ty) => TypeArgument::Extends(self.source_signature(ty)?),
            JavaTypeArgument::Super(ty) => TypeArgument::Super(self.source_signature(ty)?),
        })
    }
}

#[derive(Debug, Clone, Default)]
struct DeclaredTypes {
    source_names: BTreeMap<String, JavaClassType>,
    header_names: BTreeMap<String, JavaClassType>,
    simple_names: BTreeSet<JavaIdentifier>,
}

impl DeclaredTypes {
    fn collect(root: &JavaClassModel) -> Self {
        let mut declarations = Self::default();
        let mut pending = vec![(root, Vec::<JavaIdentifier>::new())];
        while let Some((class, mut path)) = pending.pop() {
            path.push(class.declaration.name.clone());
            if let Some(binary_name) = class
                .declaration
                .current_type()
                .as_ref()
                .and_then(JavaTypeNameResolver::type_binary_name)
            {
                let source_path = if path.len() == 1 {
                    path.clone()
                } else {
                    path[1..].to_vec()
                };
                if let Some(simple_name) = source_path.last() {
                    declarations.simple_names.insert(simple_name.clone());
                }
                declarations.source_names.insert(
                    binary_name.clone(),
                    JavaClassType::raw(JavaClassName::from_identifiers(source_path)),
                );
                if path.len() > 1 {
                    declarations.header_names.insert(
                        binary_name,
                        JavaClassType::raw(JavaClassName::from_identifiers(path.clone())),
                    );
                }
            }
            pending.extend(
                class
                    .nested
                    .iter()
                    .rev()
                    .map(|nested| (nested, path.clone())),
            );
        }
        Self::retain_injective_names(&mut declarations.source_names);
        Self::retain_injective_names(&mut declarations.header_names);
        declarations
    }

    fn retain_injective_names(names: &mut BTreeMap<String, JavaClassType>) {
        let mut multiplicity = BTreeMap::<String, usize>::new();
        for source_name in names.values() {
            *multiplicity.entry(source_name.to_string()).or_default() += 1;
        }
        names.retain(|_, source_name| {
            multiplicity
                .get(&source_name.to_string())
                .copied()
                .unwrap_or_default()
                == 1
        });
    }

    fn resolve(&self, binary_name: &str) -> Option<&JavaClassType> {
        self.source_names.get(binary_name)
    }

    fn header(&self, binary_name: &str) -> Option<&JavaClassType> {
        self.header_names.get(binary_name)
    }

    fn reserves(&self, simple_name: &str) -> bool {
        self.simple_names
            .contains(&JavaIdentifier::from_dex(simple_name))
    }
}

struct GenericTypeResolver<'a> {
    names: &'a JavaTypeNameResolver,
    header: bool,
}

impl<'a> GenericTypeResolver<'a> {
    fn new(names: &'a JavaTypeNameResolver, header: bool) -> Self {
        Self { names, header }
    }

    fn resolve(
        &self,
        signature: &'a crate::ir::generic_types::JvmTypeSignature,
    ) -> Result<JavaType, JavaTypeNameError> {
        use crate::ir::generic_types::JvmTypeSignature;

        Ok(match signature {
            JvmTypeSignature::Array(element) => JavaType::array(self.resolve(element)?),
            JvmTypeSignature::ClassType(class) => JavaType::Class(self.resolve_class(class)?),
            JvmTypeSignature::TypeVariable(name) => {
                JavaType::Variable(JavaIdentifier::from_dex(name))
            }
            JvmTypeSignature::BaseType(primitive) => {
                JavaType::Primitive(primitive_type(*primitive)?)
            }
        })
    }

    fn resolve_class(
        &self,
        class: &'a crate::ir::generic_types::ClassTypeSignature,
    ) -> Result<JavaClassType, JavaTypeNameError> {
        let mut resolved = self
            .names
            .resolve_object_type_in(&class.erased_name(), self.header);
        let mut segments = Vec::with_capacity(1 + class.inner_segments.len());
        segments.push((
            class.raw_name.rsplit('/').next().unwrap_or(&class.raw_name),
            class.type_arguments.as_slice(),
        ));
        segments.extend(
            class
                .inner_segments
                .iter()
                .map(|inner| (inner.simple_name.as_str(), inner.type_arguments.as_slice())),
        );

        let mut target = resolved.segments.len();
        for (segment, arguments) in segments.into_iter().rev() {
            let Some(index) = target.checked_sub(1) else {
                break;
            };
            let expected = JavaIdentifier::from_dex(&render_nested_segment(segment));
            if resolved.segments[index].name != expected {
                break;
            }
            resolved.segments[index].arguments = arguments
                .iter()
                .map(|argument| self.resolve_argument(argument))
                .collect::<Result<Vec<_>, _>>()?;
            target = index;
        }
        Ok(resolved)
    }

    fn resolve_argument(
        &self,
        argument: &'a crate::ir::generic_types::TypeArgument,
    ) -> Result<JavaTypeArgument, JavaTypeNameError> {
        use crate::ir::generic_types::TypeArgument;
        Ok(match argument {
            TypeArgument::Unbounded => JavaTypeArgument::Any,
            TypeArgument::Extends(ty) => JavaTypeArgument::Extends(self.resolve(ty)?),
            TypeArgument::Super(ty) => JavaTypeArgument::Super(self.resolve(ty)?),
            TypeArgument::Exact(ty) => JavaTypeArgument::Exact(self.resolve(ty)?),
        })
    }
}

#[derive(Debug, Clone, Default)]
struct JavaLexicalTypeScope {
    owner_chain: Vec<String>,
}

impl JavaLexicalTypeScope {
    fn new(current_type: Option<String>) -> Self {
        let owner_chain = current_type
            .as_deref()
            .map(owner_chain_from_binary_name)
            .unwrap_or_default();
        Self { owner_chain }
    }

    fn relative_name(&self, binary_name: &str) -> Option<String> {
        let target = JavaTypeName::from_binary_name(binary_name)?;
        for scope_binary_name in &self.owner_chain {
            let scope = JavaTypeName::from_binary_name(scope_binary_name)?;
            if !target.has_prefix(&scope) {
                continue;
            }
            let start_segment = if target.segment_count() == scope.segment_count() {
                scope.segment_count().saturating_sub(1)
            } else {
                scope.segment_count()
            };
            return Some(target.source_name_from_segment(start_segment));
        }
        None
    }
}

fn owner_chain_from_binary_name(binary_name: &str) -> Vec<String> {
    let Some(name) = JavaTypeName::from_binary_name(binary_name) else {
        return Vec::new();
    };
    (1..=name.segment_count())
        .rev()
        .map(|segment_count| name.binary_name_with_segments(segment_count))
        .collect()
}

#[derive(Default)]
struct JavaTypeImportCollector {
    binary_names: BTreeSet<String>,
}

impl JavaTypeImportCollector {
    fn collect_type(&mut self, ty: &ArgType) -> Result<(), JavaTypeNameError> {
        let mut ty = ty;
        loop {
            match ty {
                ArgType::Array(element) => ty = element,
                ArgType::Object(name) => {
                    self.binary_names
                        .insert(JavaTypeName::internal_to_binary_name(name));
                    return Ok(());
                }
                ArgType::Primitive(_) => return Ok(()),
                ArgType::Unknown(_) => {
                    return Err(JavaTypeNameError::Unresolved(ty.clone()));
                }
            }
        }
    }

    fn simple_counts(&self) -> BTreeMap<String, usize> {
        let mut counts = BTreeMap::new();
        for full_name in &self.binary_names {
            if let Some(name) = JavaTypeName::from_binary_name(full_name) {
                *counts.entry(name.simple).or_default() += 1;
            }
        }
        counts
    }

    fn into_binary_names(self) -> BTreeSet<String> {
        self.binary_names
    }
}

struct JavaTypeName {
    package: Option<String>,
    top_level: String,
    nested: Vec<String>,
    simple: String,
}

impl JavaTypeName {
    fn from_binary_name(full_name: &str) -> Option<Self> {
        let (package, name) = full_name
            .rsplit_once('.')
            .map(|(package, name)| (Some(package.to_string()), name.to_string()))
            .unwrap_or((None, full_name.to_string()));
        if name.is_empty() {
            return None;
        }
        let mut parts = name.split('$').map(ToOwned::to_owned).collect::<Vec<_>>();
        if parts.iter().any(|part| part.is_empty()) {
            return None;
        }
        if parts.iter().skip(1).any(|part| {
            !part.chars().all(|character| character.is_ascii_digit())
                && !is_source_nested_identifier(part)
        }) {
            parts = vec![name];
        }
        let top_level = parts.first()?.clone();
        let nested = parts.iter().skip(1).cloned().collect::<Vec<_>>();
        let simple = parts.last()?.clone();
        Some(Self {
            package,
            top_level,
            nested,
            simple,
        })
    }

    fn source_name(&self) -> String {
        self.source_name_from_segment(0)
    }

    fn qualified_source_name(&self) -> String {
        match &self.package {
            Some(package) => format!("{}.{}", package, self.source_name()),
            None => self.source_name(),
        }
    }

    fn import_name(&self) -> String {
        match &self.package {
            Some(package) => format!("{}.{}", package, self.top_level),
            None => self.top_level.clone(),
        }
    }

    fn segment_count(&self) -> usize {
        1 + self.nested.len()
    }

    fn segment(&self, idx: usize) -> Option<&str> {
        if idx == 0 {
            return Some(self.top_level.as_str());
        }
        self.nested.get(idx - 1).map(String::as_str)
    }

    fn source_name_from_segment(&self, start_segment: usize) -> String {
        let Some(first) = self.segment(start_segment) else {
            return self.source_name();
        };
        let mut name = render_nested_segment(first);
        for idx in start_segment + 1..self.segment_count() {
            let Some(part) = self.segment(idx) else {
                break;
            };
            let rendered = render_nested_segment(part);
            if is_source_nested_identifier(&rendered) {
                name.push('.');
            } else {
                name.push('$');
            }
            name.push_str(&rendered);
        }
        name
    }

    fn has_prefix(&self, prefix: &Self) -> bool {
        if self.package != prefix.package || self.segment_count() < prefix.segment_count() {
            return false;
        }
        (0..prefix.segment_count()).all(|idx| self.segment(idx) == prefix.segment(idx))
    }

    fn binary_name_with_segments(&self, segment_count: usize) -> String {
        let mut name = match &self.package {
            Some(package) => format!("{}.{}", package, self.top_level),
            None => self.top_level.clone(),
        };
        for idx in 1..segment_count {
            if let Some(segment) = self.segment(idx) {
                name.push('$');
                name.push_str(segment);
            }
        }
        name
    }

    fn internal_to_binary_name(internal_name: &str) -> String {
        internal_name.replace('/', ".")
    }

    fn implicit_or_qualified_source_name(binary_name: &str) -> String {
        Self::from_binary_name(binary_name)
            .map(|name| {
                if name.package.as_deref() == Some("java.lang") {
                    name.source_name()
                } else {
                    name.qualified_source_name()
                }
            })
            .unwrap_or_else(|| binary_name.to_string())
    }
}

fn render_nested_segment(part: &str) -> String {
    if part.chars().all(|c| c.is_ascii_digit()) && !part.is_empty() {
        format!("Anonymous{}", part)
    } else {
        part.to_string()
    }
}

fn is_source_nested_identifier(part: &str) -> bool {
    let mut chars = part.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first == '$' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch == '$' || ch.is_ascii_alphanumeric())
}

fn primitive_type(p: crate::ir::ty::PrimitiveType) -> Result<JavaPrimitiveType, JavaTypeNameError> {
    use crate::ir::ty::PrimitiveType;
    Ok(match p {
        PrimitiveType::Boolean => JavaPrimitiveType::Boolean,
        PrimitiveType::Byte => JavaPrimitiveType::Byte,
        PrimitiveType::Char => JavaPrimitiveType::Char,
        PrimitiveType::Short => JavaPrimitiveType::Short,
        PrimitiveType::Int => JavaPrimitiveType::Int,
        PrimitiveType::Long => JavaPrimitiveType::Long,
        PrimitiveType::Float => JavaPrimitiveType::Float,
        PrimitiveType::Double => JavaPrimitiveType::Double,
        PrimitiveType::Void => JavaPrimitiveType::Void,
        PrimitiveType::Object | PrimitiveType::Array => {
            return Err(JavaTypeNameError::InvalidPrimitive(p));
        }
    })
}

fn is_java_lang_object(signature: &crate::ir::generic_types::JvmTypeSignature) -> bool {
    matches!(
        signature,
        crate::ir::generic_types::JvmTypeSignature::ClassType(class)
            if class.erased_name() == "java/lang/Object"
    )
}

#[cfg(test)]
mod tests {
    use super::{ArgType, JavaIdentifier, JavaTypeNameResolver};
    use crate::analysis::java_backend::java_model::{JavaClassDeclaration, JavaClassModel};

    #[test]
    fn formats_named_inner_classes_with_source_member_separator() {
        let resolver =
            JavaTypeNameResolver::new(None, None, [ArgType::object("pkg/Outer$Inner")]).unwrap();

        assert_eq!(
            resolver
                .resolve_type(&ArgType::object("pkg/Outer$Inner"))
                .unwrap()
                .to_string(),
            "Outer.Inner"
        );
    }

    #[test]
    fn renders_numeric_synthetic_inner_classes_as_anonymous() {
        // Numeric synthetic inner classes (`Outer$1`, `Outer$2`) render as
        // `Outer.AnonymousN` so that references line up with the synthetic
        // declaration name produced by `simple_inner_class_name`.
        let resolver =
            JavaTypeNameResolver::new(None, None, [ArgType::object("pkg/Outer$1")]).unwrap();

        assert_eq!(
            resolver
                .resolve_type(&ArgType::object("pkg/Outer$1"))
                .unwrap()
                .to_string(),
            "Outer.Anonymous1"
        );
    }

    #[test]
    fn renders_switch_map_helper_as_anonymous_when_numeric() {
        // `ObjectTypeAdapter$2` is a numeric-named synthetic inner class; it
        // now renders as `ObjectTypeAdapter.Anonymous2` rather than the binary
        // `ObjectTypeAdapter$2` form, matching its declaration name.
        let resolver = JavaTypeNameResolver::new(
            None,
            None,
            [ArgType::object(
                "com/google/gson/internal/bind/ObjectTypeAdapter$2",
            )],
        )
        .unwrap();

        assert_eq!(
            resolver
                .resolve_type(&ArgType::object(
                    "com/google/gson/internal/bind/ObjectTypeAdapter$2",
                ))
                .unwrap()
                .to_string(),
            "ObjectTypeAdapter.Anonymous2"
        );
    }

    #[test]
    fn renders_outer_member_type_relative_to_top_level_scope() {
        let resolver = JavaTypeNameResolver::new(
            Some("pkg"),
            Some(&ArgType::object("pkg/Outer")),
            [ArgType::object("pkg/Outer$Node")],
        )
        .unwrap();

        assert_eq!(
            resolver
                .resolve_type(&ArgType::object("pkg/Outer$Node"))
                .unwrap()
                .to_string(),
            "Node"
        );
    }

    #[test]
    fn renders_sibling_member_type_relative_to_enclosing_outer_scope() {
        let resolver = JavaTypeNameResolver::new(
            Some("pkg"),
            Some(&ArgType::object("pkg/Outer$EntrySet")),
            [ArgType::object("pkg/Outer$LinkedTreeMapIterator")],
        )
        .unwrap();

        assert_eq!(
            resolver
                .resolve_type(&ArgType::object("pkg/Outer$LinkedTreeMapIterator"))
                .unwrap()
                .to_string(),
            "LinkedTreeMapIterator"
        );
    }

    #[test]
    fn relative_sibling_generic_type_round_trips_to_binary_signature() {
        let current = ArgType::object("pkg/Outer$Builder");
        let signature = crate::ir::generic_types::GenericSignatures::field(
            "Ljava/util/List<Lpkg/Outer$TypeMatcher;>;",
        )
        .expect("generic field signature");
        let resolver = JavaTypeNameResolver::new(
            Some("pkg"),
            Some(&current),
            [
                ArgType::object("java/util/List"),
                ArgType::object("pkg/Outer$TypeMatcher"),
            ],
        )
        .expect("type resolver");
        let source = resolver
            .resolve_generic_type(&signature)
            .expect("source generic type");

        assert_eq!(source.to_string(), "List<TypeMatcher>");
        assert_eq!(resolver.source_signature(&source), Some(signature));
    }

    #[test]
    fn renders_enclosing_outer_type_relative_to_nested_scope() {
        let resolver = JavaTypeNameResolver::new(
            Some("pkg"),
            Some(&ArgType::object("pkg/Outer$EntrySet")),
            [ArgType::object("pkg/Outer")],
        )
        .unwrap();

        assert_eq!(
            resolver
                .resolve_type(&ArgType::object("pkg/Outer"))
                .unwrap()
                .to_string(),
            "Outer"
        );
    }

    #[test]
    fn keeps_non_enclosing_nested_types_qualified() {
        let resolver = JavaTypeNameResolver::new(
            Some("pkg"),
            Some(&ArgType::object("pkg/Outer$EntrySet")),
            [ArgType::object("pkg/Other$Node")],
        )
        .unwrap();

        assert_eq!(
            resolver
                .resolve_type(&ArgType::object("pkg/Other$Node"))
                .unwrap()
                .to_string(),
            "Other.Node"
        );
    }

    #[test]
    fn resolves_metadata_inner_types_from_the_declaration_tree() {
        let nested = JavaClassModel {
            declaration: JavaClassDeclaration::new(JavaIdentifier::from_dex("Track"))
                .with_type_descriptor("Lcom/facebook/ads/redexgen/X/Vz;"),
            fields: Vec::new(),
            methods: Vec::new(),
            function_object: false,
            outer_instance: None,
            nested: Vec::new(),
        };
        let root = JavaClassModel {
            declaration: JavaClassDeclaration::new(JavaIdentifier::from_dex("MatroskaExtractor"))
                .with_type_descriptor("Lcom/google/MatroskaExtractor;"),
            fields: Vec::new(),
            methods: Vec::new(),
            function_object: false,
            outer_instance: None,
            nested: vec![nested],
        };
        let current_type = ArgType::object("com/google/MatroskaExtractor");
        let metadata_inner = ArgType::object("com/facebook/ads/redexgen/X/Vz");
        let resolver = JavaTypeNameResolver::for_class(
            &root,
            Some("com.google"),
            Some(&current_type),
            [metadata_inner.clone()],
        )
        .expect("type resolver");

        assert_eq!(
            resolver
                .resolve_type(&metadata_inner)
                .expect("metadata inner type")
                .to_string(),
            "Track"
        );
        assert!(resolver
            .imports()
            .all(|import| !import.to_string().ends_with(".Vz")));
    }
}
