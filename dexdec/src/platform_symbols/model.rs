use std::collections::BTreeMap;
use std::io;
use std::path::Path;

use super::DexSymbolsCodec;

/// Runtime family whose ABI a source artifact describes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum PlatformFamily {
    Java,
    Android,
    Library,
}

impl PlatformFamily {
    pub(crate) fn code(self) -> u8 {
        match self {
            Self::Java => 1,
            Self::Android => 2,
            Self::Library => 3,
        }
    }

    pub(crate) fn from_code(code: u8) -> io::Result<Self> {
        match code {
            1 => Ok(Self::Java),
            2 => Ok(Self::Android),
            3 => Ok(Self::Library),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid platform family",
            )),
        }
    }
}

/// Platform selection used to materialize one coherent ABI view.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PlatformTarget {
    pub family: PlatformFamily,
    pub version: u16,
}

impl PlatformTarget {
    pub const fn java(release: u16) -> Self {
        Self {
            family: PlatformFamily::Java,
            version: release,
        }
    }

    pub const fn android(api: u16) -> Self {
        Self {
            family: PlatformFamily::Android,
            version: api,
        }
    }
}

/// Provenance of a group of symbol snapshots.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolSource {
    pub name: String,
    pub family: PlatformFamily,
    /// Higher priority wins when two sources provide the same platform fact.
    pub priority: i16,
}

/// Inclusive platform-version interval for one ABI shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolAvailability {
    pub since: u16,
    pub until: u16,
}

impl SymbolAvailability {
    pub fn exact(version: u16) -> Self {
        Self {
            since: version,
            until: version,
        }
    }

    pub fn new(since: u16, until: u16) -> io::Result<Self> {
        if since > until {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "symbol availability starts after it ends",
            ));
        }
        Ok(Self { since, until })
    }

    pub fn contains(self, version: u16) -> bool {
        self.since <= version && version <= self.until
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PlatformAnnotation {
    pub descriptor: String,
    pub elements: BTreeMap<String, PlatformAnnotationValue>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlatformNullability {
    NonNull,
    Nullable,
}

impl PlatformAnnotation {
    fn explicit_nullability(&self) -> Option<PlatformNullability> {
        match self.descriptor.as_str() {
            "Ljavax/annotation/Nullable;"
            | "Ljavax/annotation/CheckForNull;"
            | "Ljakarta/annotation/Nullable;"
            | "Lorg/jetbrains/annotations/Nullable;"
            | "Landroidx/annotation/Nullable;"
            | "Landroidx/annotation/RecentlyNullable;"
            | "Landroid/annotation/Nullable;"
            | "Landroid/annotation/RecentlyNullable;"
            | "Lorg/jspecify/annotations/Nullable;"
            | "Lorg/checkerframework/checker/nullness/qual/Nullable;"
            | "Lorg/eclipse/jdt/annotation/Nullable;"
            | "Ledu/umd/cs/findbugs/annotations/Nullable;"
            | "Lorg/springframework/lang/Nullable;" => Some(PlatformNullability::Nullable),
            "Ljavax/annotation/Nonnull;"
            | "Ljakarta/annotation/Nonnull;"
            | "Lorg/jetbrains/annotations/NotNull;"
            | "Landroidx/annotation/NonNull;"
            | "Landroidx/annotation/RecentlyNonNull;"
            | "Landroid/annotation/NonNull;"
            | "Landroid/annotation/RecentlyNonNull;"
            | "Lorg/jspecify/annotations/NonNull;"
            | "Lorg/checkerframework/checker/nullness/qual/NonNull;"
            | "Lorg/eclipse/jdt/annotation/NonNull;"
            | "Ledu/umd/cs/findbugs/annotations/NonNull;" => Some(PlatformNullability::NonNull),
            _ => None,
        }
    }
}

fn annotation_nullability(annotations: &[PlatformAnnotation]) -> Option<PlatformNullability> {
    annotations
        .iter()
        .find_map(PlatformAnnotation::explicit_nullability)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum PlatformAnnotationValue {
    Boolean(bool),
    Integer(i64),
    Float(u32),
    Double(u64),
    String(String),
    Type(String),
    Enum {
        descriptor: String,
        constant: String,
    },
    Field(PlatformFieldReference),
    Annotation(Box<PlatformAnnotation>),
    Array(Vec<PlatformAnnotationValue>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlatformFieldReference {
    pub owner: String,
    pub name: String,
    pub descriptor: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PlatformConstantKind {
    Integer,
    Long,
    String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PlatformConstantMember {
    pub field: PlatformFieldReference,
    pub value: PlatformConstant,
}

/// A closed source-level value domain declared for one method parameter.
///
/// Domains come from ABI metadata such as Android's external `IntDef`,
/// `LongDef`, and `StringDef` annotations. They are keyed by the exact method
/// descriptor and parameter index; consumers must not infer them from names.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PlatformConstantDomain {
    pub kind: PlatformConstantKind,
    pub flags: bool,
    pub members: Vec<PlatformConstantMember>,
}

impl PlatformConstantDomain {
    const MAX_DECOMPOSITION_STATES: usize = 65_536;

    /// Resolves a literal to one unique, minimum-cardinality source spelling.
    ///
    /// A result is withheld when aliases or multiple equally small flag
    /// decompositions exist. This makes symbolic recovery deterministic and
    /// prevents metadata from changing program meaning.
    pub fn resolve(&self, value: &PlatformConstant) -> Option<Vec<&PlatformConstantMember>> {
        let exact = self
            .members
            .iter()
            .filter(|member| self.constants_equal(&member.value, value))
            .collect::<Vec<_>>();
        if exact.len() == 1 {
            return Some(exact);
        }
        if !exact.is_empty() || !self.flags {
            return None;
        }
        let target = self.integer_bits(value)?;
        if target == 0 {
            return None;
        }
        let candidates = self
            .members
            .iter()
            .enumerate()
            .filter_map(|(index, member)| {
                let bits = self.integer_bits(&member.value)?;
                (bits != 0 && bits & !target == 0).then_some((index, bits))
            })
            .collect::<Vec<_>>();
        let mut states = BTreeMap::from([(0u64, DomainSolution::unique(Vec::new()))]);
        for (index, bits) in candidates {
            let snapshot = states
                .iter()
                .map(|(covered, solution)| (*covered, solution.clone()))
                .collect::<Vec<_>>();
            for (covered, solution) in snapshot {
                let combined = covered | bits;
                if combined == covered {
                    continue;
                }
                let candidate = solution.with_term(index);
                match states.entry(combined) {
                    std::collections::btree_map::Entry::Vacant(entry) => {
                        entry.insert(candidate);
                    }
                    std::collections::btree_map::Entry::Occupied(mut entry) => {
                        entry.get_mut().merge(candidate);
                    }
                }
            }
            if states.len() > Self::MAX_DECOMPOSITION_STATES {
                return None;
            }
        }
        let solution = states.get(&target)?;
        if solution.ambiguous {
            return None;
        }
        Some(
            solution
                .terms
                .iter()
                .map(|index| &self.members[*index])
                .collect(),
        )
    }

    fn constants_equal(&self, left: &PlatformConstant, right: &PlatformConstant) -> bool {
        match self.kind {
            PlatformConstantKind::Integer => self
                .integer_bits(left)
                .zip(self.integer_bits(right))
                .is_some_and(|(left, right)| left == right),
            PlatformConstantKind::Long => left == right,
            PlatformConstantKind::String => left == right,
        }
    }

    fn integer_bits(&self, value: &PlatformConstant) -> Option<u64> {
        let PlatformConstant::Integer(value) = value else {
            return None;
        };
        Some(match self.kind {
            PlatformConstantKind::Integer => u64::from(*value as u32),
            PlatformConstantKind::Long => *value as u64,
            PlatformConstantKind::String => return None,
        })
    }
}

#[derive(Clone)]
struct DomainSolution {
    terms: Vec<usize>,
    ambiguous: bool,
}

impl DomainSolution {
    fn unique(terms: Vec<usize>) -> Self {
        Self {
            terms,
            ambiguous: false,
        }
    }

    fn with_term(mut self, term: usize) -> Self {
        self.terms.push(term);
        self
    }

    fn merge(&mut self, other: Self) {
        match other.terms.len().cmp(&self.terms.len()) {
            std::cmp::Ordering::Less => *self = other,
            std::cmp::Ordering::Equal => {
                if self.terms != other.terms || other.ambiguous {
                    self.ambiguous = true;
                }
            }
            std::cmp::Ordering::Greater => {}
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum PlatformConstant {
    Integer(i64),
    Float(u32),
    Double(u64),
    String(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlatformField {
    pub name: String,
    pub descriptor: String,
    pub signature: Option<String>,
    pub access_flags: u32,
    pub constant: Option<PlatformConstant>,
    pub annotations: Vec<PlatformAnnotation>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlatformMethod {
    pub name: String,
    pub descriptor: String,
    pub signature: Option<String>,
    pub access_flags: u32,
    pub exceptions: Vec<String>,
    pub parameter_names: Vec<Option<String>>,
    pub annotations: Vec<PlatformAnnotation>,
    pub parameter_annotations: Vec<Vec<PlatformAnnotation>>,
    pub parameter_domains: Vec<Option<PlatformConstantDomain>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlatformClass {
    pub descriptor: String,
    pub source: u32,
    pub availability: SymbolAvailability,
    pub access_flags: u32,
    pub super_class: Option<String>,
    pub interfaces: Vec<String>,
    pub signature: Option<String>,
    pub annotations: Vec<PlatformAnnotation>,
    pub fields: Vec<PlatformField>,
    pub methods: Vec<PlatformMethod>,
}

impl PlatformClass {
    pub fn method_return_nullability(
        &self,
        method: &PlatformMethod,
    ) -> Option<PlatformNullability> {
        annotation_nullability(&method.annotations).or_else(|| {
            self.has_non_null_default(false)
                .then_some(PlatformNullability::NonNull)
        })
    }

    pub fn method_parameter_nullability(
        &self,
        method: &PlatformMethod,
        parameter: usize,
    ) -> Option<PlatformNullability> {
        method
            .parameter_annotations
            .get(parameter)
            .and_then(|annotations| annotation_nullability(annotations))
            .or_else(|| {
                self.has_non_null_default(true)
                    .then_some(PlatformNullability::NonNull)
            })
    }

    fn has_non_null_default(&self, parameters: bool) -> bool {
        self.annotations.iter().any(|annotation| {
            matches!(
                annotation.descriptor.as_str(),
                "Lorg/jspecify/annotations/NullMarked;" | "Lorg/springframework/lang/NonNullApi;"
            ) || (parameters
                && matches!(
                    annotation.descriptor.as_str(),
                    "Ljavax/annotation/ParametersAreNonnullByDefault;"
                        | "Ljakarta/annotation/ParametersAreNonnullByDefault;"
                ))
        })
    }

    pub(crate) fn same_abi(&self, other: &Self) -> bool {
        self.descriptor == other.descriptor
            && self.source == other.source
            && self.access_flags == other.access_flags
            && self.super_class == other.super_class
            && self.interfaces == other.interfaces
            && self.signature == other.signature
            && self.annotations == other.annotations
            && self.fields == other.fields
            && self.methods == other.methods
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolDatabaseStats {
    pub sources: usize,
    pub class_variants: usize,
    pub selected_classes: usize,
    pub fields: usize,
    pub methods: usize,
}

/// Persistent collection of all source and version variants.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlatformSymbolDatabase {
    pub(crate) default_target: PlatformTarget,
    pub(crate) sources: Vec<SymbolSource>,
    pub(crate) classes: BTreeMap<String, Vec<PlatformClass>>,
}

impl PlatformSymbolDatabase {
    pub fn new(default_target: PlatformTarget) -> Self {
        Self {
            default_target,
            sources: Vec::new(),
            classes: BTreeMap::new(),
        }
    }

    pub fn default_target(&self) -> PlatformTarget {
        self.default_target
    }

    pub fn sources(&self) -> &[SymbolSource] {
        &self.sources
    }

    pub fn class_variants(&self, descriptor: &str) -> &[PlatformClass] {
        self.classes
            .get(descriptor)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn select(&self, target: PlatformTarget) -> PlatformSymbolSet {
        let classes = self
            .classes
            .iter()
            .filter_map(|(descriptor, variants)| {
                self.best_variant(variants, target)
                    .cloned()
                    .map(|class| (descriptor.clone(), class))
            })
            .collect();
        PlatformSymbolSet { target, classes }
    }

    pub fn stats(&self) -> SymbolDatabaseStats {
        let class_variants = self.classes.values().map(Vec::len).sum();
        let fields = self
            .classes
            .values()
            .flatten()
            .map(|class| class.fields.len())
            .sum();
        let methods = self
            .classes
            .values()
            .flatten()
            .map(|class| class.methods.len())
            .sum();
        SymbolDatabaseStats {
            sources: self.sources.len(),
            class_variants,
            selected_classes: self.select(self.default_target).classes.len(),
            fields,
            methods,
        }
    }

    pub fn from_bytes(bytes: &[u8]) -> io::Result<Self> {
        DexSymbolsCodec::decode(bytes)
    }

    pub fn to_bytes(&self) -> io::Result<Vec<u8>> {
        DexSymbolsCodec::encode(self)
    }

    pub fn read(path: impl AsRef<Path>) -> io::Result<Self> {
        let bytes = std::fs::read(path)?;
        Self::from_bytes(&bytes)
    }

    pub fn write(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let path = path.as_ref();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, self.to_bytes()?)
    }

    pub(crate) fn add_source(&mut self, source: SymbolSource) -> u32 {
        if let Some(index) = self
            .sources
            .iter()
            .position(|candidate| candidate == &source)
        {
            return index as u32;
        }
        let index = self.sources.len() as u32;
        self.sources.push(source);
        index
    }

    pub(crate) fn add_class(&mut self, mut class: PlatformClass) {
        let variants = self.classes.entry(class.descriptor.clone()).or_default();
        if let Some(existing) = variants.iter_mut().find(|existing| {
            existing.source == class.source
                && existing.same_abi(&class)
                && existing.availability.until.checked_add(1) == Some(class.availability.since)
        }) {
            existing.availability.until = class.availability.until;
            return;
        }
        if let Some(existing) = variants.iter_mut().find(|existing| {
            existing.source == class.source && existing.availability == class.availability
        }) {
            std::mem::swap(existing, &mut class);
            return;
        }
        variants.push(class);
        variants.sort_by_key(|variant| {
            (
                variant.source,
                variant.availability.since,
                variant.availability.until,
            )
        });
    }

    pub(crate) fn normalize(&mut self) {
        for variants in self.classes.values_mut() {
            variants.sort_by_key(|variant| {
                (
                    variant.source,
                    variant.availability.since,
                    variant.availability.until,
                )
            });
            let mut merged = Vec::<PlatformClass>::with_capacity(variants.len());
            for variant in std::mem::take(variants) {
                if let Some(previous) = merged.last_mut() {
                    if previous.same_abi(&variant)
                        && previous.availability.until.checked_add(1)
                            == Some(variant.availability.since)
                    {
                        previous.availability.until = variant.availability.until;
                        continue;
                    }
                }
                merged.push(variant);
            }
            *variants = merged;
        }
    }

    #[cfg(feature = "symbol-builder")]
    pub(crate) fn android_classes(&self, api: u16) -> Vec<&PlatformClass> {
        self.classes
            .values()
            .flatten()
            .filter(|class| class.availability.contains(api))
            .filter(|class| {
                self.sources
                    .get(class.source as usize)
                    .is_some_and(|source| source.family == PlatformFamily::Android)
            })
            .collect()
    }

    #[cfg(feature = "symbol-builder")]
    pub(crate) fn method_variant_mut(
        &mut self,
        api: u16,
        owner: &str,
        name: &str,
        descriptor: &str,
    ) -> Option<&mut PlatformMethod> {
        let sources = &self.sources;
        let class = self
            .classes
            .get_mut(owner)?
            .iter_mut()
            .max_by_key(|class| {
                let source = sources.get(class.source as usize);
                (
                    class.availability.contains(api)
                        && source.is_some_and(|source| source.family == PlatformFamily::Android),
                    source.map(|source| source.priority).unwrap_or(i16::MIN),
                )
            })?;
        let source = sources.get(class.source as usize)?;
        if !class.availability.contains(api) || source.family != PlatformFamily::Android {
            return None;
        }
        class
            .methods
            .iter_mut()
            .find(|method| method.name == name && method.descriptor == descriptor)
    }

    fn best_variant<'a>(
        &'a self,
        variants: &'a [PlatformClass],
        target: PlatformTarget,
    ) -> Option<&'a PlatformClass> {
        variants.iter().max_by_key(|variant| {
            let source = &self.sources[variant.source as usize];
            let family = match (target.family, source.family) {
                (expected, actual) if expected == actual => 3,
                (PlatformFamily::Android, PlatformFamily::Java) => 2,
                (_, PlatformFamily::Library) => 1,
                _ => 0,
            };
            let availability = if variant.availability.contains(target.version) {
                (3, 0)
            } else if variant.availability.until < target.version {
                (
                    2,
                    i32::from(variant.availability.until) - i32::from(target.version),
                )
            } else {
                (
                    1,
                    i32::from(target.version) - i32::from(variant.availability.since),
                )
            };
            (family, availability, source.priority)
        })
    }
}

/// One immutable, target-selected symbol view used by analyses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlatformSymbolSet {
    target: PlatformTarget,
    classes: BTreeMap<String, PlatformClass>,
}

impl PlatformSymbolSet {
    pub fn target(&self) -> PlatformTarget {
        self.target
    }

    pub fn classes(&self) -> impl Iterator<Item = &PlatformClass> {
        self.classes.values()
    }

    pub fn class(&self, descriptor: &str) -> Option<&PlatformClass> {
        self.classes.get(descriptor)
    }

    pub fn is_subtype(&self, subtype: &str, supertype: &str) -> bool {
        let mut pending = std::collections::VecDeque::from([subtype]);
        let mut seen = std::collections::BTreeSet::new();
        while let Some(candidate) = pending.pop_front() {
            if candidate == supertype {
                return true;
            }
            if !seen.insert(candidate) {
                continue;
            }
            let Some(class) = self.class(candidate) else {
                continue;
            };
            pending.extend(class.super_class.iter().map(String::as_str));
            pending.extend(class.interfaces.iter().map(String::as_str));
        }
        false
    }

    pub fn method(&self, owner: &str, name: &str, descriptor: &str) -> Option<&PlatformMethod> {
        self.resolve_method(owner, name, descriptor)
            .map(|(_, method)| method)
    }

    pub fn method_return_nullability(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
    ) -> Option<PlatformNullability> {
        let (class, method) = self.resolve_method(owner, name, descriptor)?;
        class.method_return_nullability(method)
    }

    pub fn method_parameter_nullability(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
        parameter: usize,
    ) -> Option<PlatformNullability> {
        let (class, method) = self.resolve_method(owner, name, descriptor)?;
        class.method_parameter_nullability(method, parameter)
    }

    pub fn field_nullability(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
    ) -> Option<PlatformNullability> {
        let class = self.class(owner)?;
        let field = class
            .fields
            .iter()
            .find(|field| field.name == name && field.descriptor == descriptor)?;
        annotation_nullability(&field.annotations)
            .or_else(|| {
                matches!(field.constant, Some(PlatformConstant::String(_)))
                    .then_some(PlatformNullability::NonNull)
            })
            .or_else(|| {
                class
                    .annotations
                    .iter()
                    .any(|annotation| {
                        annotation.descriptor == "Lorg/jspecify/annotations/NullMarked;"
                    })
                    .then_some(PlatformNullability::NonNull)
            })
    }

    pub fn resolve_method(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
    ) -> Option<(&PlatformClass, &PlatformMethod)> {
        let mut pending = std::collections::VecDeque::from([owner]);
        let mut seen = std::collections::BTreeSet::new();
        while let Some(owner) = pending.pop_front() {
            if !seen.insert(owner) {
                continue;
            }
            let Some(class) = self.class(owner) else {
                continue;
            };
            if let Some(method) = class
                .methods
                .iter()
                .find(|method| method.name == name && method.descriptor == descriptor)
            {
                return Some((class, method));
            }
            pending.extend(class.super_class.iter().map(String::as_str));
            pending.extend(class.interfaces.iter().map(String::as_str));
        }
        None
    }

    pub fn parameter_domain(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
        parameter: usize,
    ) -> Option<&PlatformConstantDomain> {
        self.method(owner, name, descriptor)?
            .parameter_domains
            .get(parameter)?
            .as_ref()
    }

    pub fn stats(&self) -> SymbolDatabaseStats {
        SymbolDatabaseStats {
            sources: 0,
            class_variants: self.classes.len(),
            selected_classes: self.classes.len(),
            fields: self.classes.values().map(|class| class.fields.len()).sum(),
            methods: self.classes.values().map(|class| class.methods.len()).sum(),
        }
    }
}

pub trait SymbolProvider {
    fn target(&self) -> PlatformTarget;
    fn class(&self, descriptor: &str) -> Option<&PlatformClass>;
}

impl SymbolProvider for PlatformSymbolSet {
    fn target(&self) -> PlatformTarget {
        self.target
    }

    fn class(&self, descriptor: &str) -> Option<&PlatformClass> {
        self.classes.get(descriptor)
    }
}
