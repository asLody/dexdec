//! DEX File Reader - Load and parse DEX files using rusty-dex
//!
//! This module provides the interface between rusty-dex and our IR,
//! loading DEX files and converting them into our internal representation.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::Path;

use super::{
    AccessInfo, AnalysisDiagnostic, AnnotationNode, ClassInfo, ClassInfoError, ClassMetadata,
    ClassNode, DebugInfo, DexValue, EnclosingInfo, ExceptionHandler, FieldInfo, FieldNode,
    InnerClassInfo, LocalVarInfo, MetadataConversionError, MethodCode, MethodInfo, MethodNode,
    TryCatchBlock,
};
use crate::ir::{ArgType, DescriptorParseError, FieldReference, MethodDescriptor, MethodReference};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AnalysisState {
    #[default]
    Dirty,
    Ready,
}

/// Error type for DEX reading operations
#[derive(Debug)]
pub enum DexError {
    /// IO error while reading file
    IoError(std::io::Error),
    /// Error parsing DEX format
    Parser(rusty_dex::error::DexError),
    ClassInfo(ClassInfoError),
    MalformedMethodPrototype(String),
    MissingDexForClass(String),
    InvalidMemberReference {
        reference: String,
        source: crate::ir::ReferenceParseError,
    },
    InvalidInvokeRegisters {
        offset: u32,
        expected: usize,
        actual: usize,
    },
    InvalidMetadata(MetadataConversionError),
    OverrideAnalysis(crate::analysis::method_override::OverrideAnalysisError),
    InvalidDescriptor {
        descriptor: String,
        source: DescriptorParseError,
    },
    /// Invalid class index
    InvalidClassIndex(u32),
    /// Invalid method index
    InvalidMethodIndex(u32),
    /// Invalid field index
    InvalidFieldIndex(u32),
    /// Invalid type index
    InvalidTypeIndex(u32),
    /// Invalid string index
    InvalidStringIndex(u32),
}

impl std::fmt::Display for DexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DexError::IoError(e) => write!(f, "IO error: {}", e),
            DexError::Parser(source) => write!(f, "DEX parser failed: {source}"),
            DexError::ClassInfo(source) => write!(f, "invalid class metadata: {source}"),
            DexError::MalformedMethodPrototype(proto) => {
                write!(f, "malformed method prototype {proto}")
            }
            DexError::MissingDexForClass(class) => {
                write!(f, "loaded class {class} has no owning DEX")
            }
            DexError::InvalidMemberReference { reference, source } => {
                write!(f, "invalid member reference {reference}: {source}")
            }
            DexError::InvalidInvokeRegisters {
                offset,
                expected,
                actual,
            } => write!(
                f,
                "invoke at {offset} uses {actual} register words, expected {expected}"
            ),
            DexError::InvalidMetadata(source) => {
                write!(f, "invalid DEX metadata: {source}")
            }
            DexError::OverrideAnalysis(source) => {
                write!(f, "method override analysis failed: {source}")
            }
            DexError::InvalidDescriptor { descriptor, source } => {
                write!(f, "Invalid descriptor {descriptor}: {source}")
            }
            DexError::InvalidClassIndex(i) => write!(f, "Invalid class index: {}", i),
            DexError::InvalidMethodIndex(i) => write!(f, "Invalid method index: {}", i),
            DexError::InvalidFieldIndex(i) => write!(f, "Invalid field index: {}", i),
            DexError::InvalidTypeIndex(i) => write!(f, "Invalid type index: {}", i),
            DexError::InvalidStringIndex(i) => write!(f, "Invalid string index: {}", i),
        }
    }
}

impl std::error::Error for DexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::IoError(source) => Some(source),
            Self::Parser(source) => Some(source),
            Self::ClassInfo(source) => Some(source),
            Self::InvalidMemberReference { source, .. } => Some(source),
            Self::InvalidMetadata(source) => Some(source),
            Self::OverrideAnalysis(source) => Some(source),
            Self::InvalidDescriptor { source, .. } => Some(source),
            _ => None,
        }
    }
}

impl From<std::io::Error> for DexError {
    fn from(e: std::io::Error) -> Self {
        DexError::IoError(e)
    }
}

impl From<crate::analysis::method_override::OverrideAnalysisError> for DexError {
    fn from(source: crate::analysis::method_override::OverrideAnalysisError) -> Self {
        Self::OverrideAnalysis(source)
    }
}

impl From<rusty_dex::error::DexError> for DexError {
    fn from(e: rusty_dex::error::DexError) -> Self {
        DexError::Parser(e)
    }
}

/// Result type for DEX operations
pub type DexResult<T> = Result<T, DexError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DexMemberDeclaration {
    pub owner: String,
    pub name: String,
    pub descriptor: String,
    pub kind: DexMemberKind,
    pub has_code: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DexMemberKind {
    Field,
    Method,
}

/// Load-order-independent lexical ownership recovered from DEX class metadata.
///
/// Dalvik `MemberClasses` does not enumerate local and anonymous classes, so
/// deriving children only from already-loaded parents loses compiler-generated
/// enum switch tables and local classes. Child-side enclosing metadata is the
/// authoritative relation; `MemberClasses` fills gaps for ordinary members.
#[derive(Default)]
struct NestedClassIndex {
    parents: BTreeMap<String, String>,
    children: BTreeMap<String, BTreeSet<String>>,
    simple_names: BTreeMap<String, String>,
}

impl NestedClassIndex {
    fn analyze(dex_files: &[rusty_dex::dex::file::DexFile]) -> Self {
        let definitions = dex_files
            .iter()
            .flat_map(|dex| dex.classes.items.iter())
            .collect::<Vec<_>>();
        let defined_names = definitions
            .iter()
            .map(|class| class.get_class_name().clone())
            .collect::<BTreeSet<_>>();
        let mut parents = BTreeMap::new();
        let mut simple_names = BTreeMap::new();

        // Child-side metadata identifies local and anonymous classes and wins
        // over a potentially incomplete parent-side member list.
        for class in &definitions {
            if let Some(parent) = Self::declared_parent(class) {
                parents.insert(class.get_class_name().clone(), parent);
            }
            if let Some(name) = class
                .get_inner_class_annotation()
                .and_then(|inner| inner.name.as_ref())
            {
                simple_names.insert(class.get_class_name().clone(), name.clone());
            }
        }
        for class in definitions {
            let parent = class.get_class_name().clone();
            for child in class
                .get_member_classes()
                .into_iter()
                .filter(|child| defined_names.contains(child.as_str()))
            {
                parents
                    .entry(child.clone())
                    .or_insert_with(|| parent.clone());
            }
        }

        let mut children = BTreeMap::<String, BTreeSet<String>>::new();
        for (child, parent) in &parents {
            children
                .entry(parent.clone())
                .or_default()
                .insert(child.clone());
        }
        Self {
            parents,
            children,
            simple_names,
        }
    }

    fn declared_parent(class: &rusty_dex::dex::classes::ClassDefItem) -> Option<String> {
        if let Some(parent) = class.get_enclosing_class() {
            return Some(parent.to_string());
        }
        if let Some(method) = class.get_enclosing_method() {
            return method
                .split_once("->")
                .map(|(declaring, _)| declaring.to_string());
        }
        let inner = class.get_inner_class_annotation()?;
        inner.name.as_ref()?;
        let descriptor = class.get_class_name().strip_suffix(';')?;
        let (outer, _) = descriptor.rsplit_once('$')?;
        Some(format!("{outer};"))
    }
}

/// DEX file reader - loads and manages DEX file data
pub struct DexFileReader {
    /// Underlying rusty-dex DexFile structures (one per DEX file in APK)
    dex_files: Vec<rusty_dex::dex::file::DexFile>,
    /// Loaded classes indexed by type descriptor
    classes: HashMap<String, ClassNode>,
    /// Immutable class directory used by every on-demand materialization.
    class_locations: HashMap<String, (usize, usize)>,
    /// Complete lexical ownership graph, independent of loaded class state.
    nested_classes: NestedClassIndex,
    /// Cached state for reader-level semantic analyses.
    override_analysis_state: AnalysisState,
    /// Non-fatal metadata defects discovered by semantic analyses.
    analysis_diagnostics: Vec<AnalysisDiagnostic>,
    /// Monotonic revision for loaded class graph and reader-derived analyses.
    loaded_classes_revision: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DexReferenceTarget {
    Class(String),
    Field(String),
    Method(String),
    FieldName {
        class: String,
        name: String,
    },
    MethodArity {
        class: String,
        name: String,
        arity: usize,
    },
    MethodParameters {
        class: String,
        name: String,
        parameters: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct DexReferenceLocation {
    pub class: String,
    pub method: String,
    pub descriptor: String,
    pub offset: u32,
}

impl DexFileReader {
    /// Load DEX file from path (supports both APK and raw DEX files)
    pub fn from_file<P: AsRef<Path>>(path: P) -> DexResult<Self> {
        let path_ref = path.as_ref();

        // Check if it's a raw DEX file
        if is_raw_dex(path_ref)? {
            let data = std::fs::read(path_ref)?;
            return Self::from_bytes(&data);
        }

        let path_str = path_ref.to_string_lossy().to_string();

        // Load all DEX files (assuming APK/Zip)
        let mut archive = rusty_dex::dex::reader::DexArchive::open(&path_str)?;
        let dex_files = crate::profile_scope!("frontend.apk.stream", {
            std::thread::scope(|scope| {
                let mut jobs = Vec::new();
                while let Some(reader) =
                    crate::profile_scope!("frontend.apk.extract_dex_entry", archive.next())
                {
                    let reader = reader?;
                    jobs.push(scope.spawn(move || {
                        crate::profile_scope!("frontend.apk.metadata_entry", {
                            rusty_dex::dex::file::DexFile::build_metadata(reader)
                        })
                    }));
                }
                jobs.into_iter()
                    .map(|job| match job.join() {
                        Ok(result) => result,
                        Err(payload) => std::panic::resume_unwind(payload),
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
        })?;

        Ok(crate::profile_scope!(
            "frontend.apk.index",
            Self::new(dex_files)
        ))
    }

    /// Load a raw DEX file (not inside an APK)
    pub fn from_raw_dex_file<P: AsRef<Path>>(path: P) -> DexResult<Self> {
        let path = path.as_ref().to_str().ok_or_else(|| {
            DexError::IoError(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "DEX path is not valid UTF-8",
            ))
        })?;
        let readers = rusty_dex::dex::reader::DexReader::build_from_file(path)?;
        let mut dex_files = Vec::new();
        for reader in readers {
            dex_files.push(rusty_dex::dex::file::DexFile::build_metadata(reader)?);
        }
        Ok(Self::new(dex_files))
    }

    /// Load DEX from raw bytes
    pub fn from_bytes(data: &[u8]) -> DexResult<Self> {
        let reader = rusty_dex::dex::reader::DexReader::build(data.to_vec())?;
        let dex = rusty_dex::dex::file::DexFile::build_metadata(reader)?;
        Ok(Self::new(vec![dex]))
    }

    /// Create from existing DexFile structures
    fn new(dex_files: Vec<rusty_dex::dex::file::DexFile>) -> Self {
        let mut class_locations = HashMap::new();
        for (dex_index, dex) in dex_files.iter().enumerate() {
            for (class_index, class) in dex.classes.items.iter().enumerate() {
                class_locations
                    .entry(class.get_class_name().clone())
                    .or_insert((dex_index, class_index));
            }
        }
        let nested_classes = NestedClassIndex::analyze(&dex_files);
        Self {
            dex_files,
            classes: HashMap::new(),
            class_locations,
            nested_classes,
            override_analysis_state: AnalysisState::Dirty,
            analysis_diagnostics: Vec::new(),
            loaded_classes_revision: 0,
        }
    }

    /// Get number of classes across all DEX files
    pub fn class_count(&self) -> usize {
        self.dex_files.iter().map(|d| d.classes.items.len()).sum()
    }

    /// Get all class names
    pub fn class_names(&self) -> Vec<String> {
        self.dex_files
            .iter()
            .flat_map(|d| d.get_classes_names().into_iter().cloned())
            .collect()
    }

    /// Visit member declaration tables without decoding method bytecode.
    pub(crate) fn visit_member_declarations(
        &self,
        mut visit: impl FnMut(DexMemberDeclaration),
    ) -> DexResult<()> {
        use rusty_dex::dex::declarations::{
            DexMemberDeclaration as RawMemberDeclaration, DexMemberKind as RawMemberKind,
            DexMemberScanner,
        };

        for dex in &self.dex_files {
            DexMemberScanner::new(dex).scan(&mut |declaration: RawMemberDeclaration<'_>| {
                let Some((_, member)) = declaration.reference.split_once("->") else {
                    return;
                };
                let (name, descriptor) = match declaration.kind {
                    RawMemberKind::Field => {
                        let Some(parts) = member.split_once(':') else {
                            return;
                        };
                        parts
                    }
                    RawMemberKind::Method => {
                        let Some(start) = member.find('(') else {
                            return;
                        };
                        (&member[..start], &member[start..])
                    }
                };
                visit(DexMemberDeclaration {
                    owner: declaration.owner.to_string(),
                    name: name.to_string(),
                    descriptor: descriptor.to_string(),
                    kind: match declaration.kind {
                        RawMemberKind::Field => DexMemberKind::Field,
                        RawMemberKind::Method => DexMemberKind::Method,
                    },
                    has_code: declaration.has_code,
                });
            })?;
        }
        Ok(())
    }

    /// Find code sites matching a DEX symbol query. The scan traverses
    /// encoded method tables directly and does not materialize class bodies.
    pub(crate) fn find_references(
        &self,
        target: &DexReferenceTarget,
    ) -> DexResult<Vec<DexReferenceLocation>> {
        use rusty_dex::dex::references::{DexCodeReference, DexReferenceScanner};

        let mut locations = BTreeSet::new();
        for dex in &self.dex_files {
            let candidates = reference_candidates(dex, target);
            let scanner = DexReferenceScanner::new(dex);
            scanner.scan(&mut |reference: DexCodeReference<'_>| {
                if !reference_matches(target, candidates.as_ref(), reference) {
                    return;
                }
                if let Some(location) = reference_location(reference) {
                    locations.insert(location);
                }
            })?;
        }
        Ok(locations.into_iter().collect())
    }

    /// Lexical owner recovered from DEX nested-class metadata without loading
    /// the class body.
    pub fn lexical_parent(&self, class_name: &str) -> Option<&str> {
        self.nested_classes
            .parents
            .get(class_name)
            .map(String::as_str)
    }

    /// Source-level nested name recovered from `InnerClass`, when present.
    pub fn lexical_simple_name(&self, class_name: &str) -> Option<&str> {
        self.nested_classes
            .simple_names
            .get(class_name)
            .map(String::as_str)
    }

    pub(crate) fn hierarchy_declarations(
        &self,
    ) -> impl Iterator<Item = (&str, Option<&str>, &[String], AccessInfo)> {
        self.dex_files
            .iter()
            .flat_map(|dex| dex.classes.items.iter())
            .map(|class| {
                (
                    class.get_class_name().as_str(),
                    class.get_superclass(),
                    class.get_interfaces(),
                    AccessInfo::for_class(class.get_access_flags_raw()),
                )
            })
    }

    /// Load all classes
    pub fn load_all_classes(&mut self) -> DexResult<()> {
        let mut changed = false;
        for dex_idx in 0..self.dex_files.len() {
            let class_count = self.dex_files[dex_idx].classes.items.len();
            for class_index in 0..class_count {
                let class_name = self.dex_files[dex_idx].classes.items[class_index]
                    .get_class_name()
                    .clone();
                self.dex_files[dex_idx].materialize_class(class_index)?;
                let class_node = {
                    let dex = &self.dex_files[dex_idx];
                    self.load_class_from_def(
                        class_index as u32,
                        &dex.classes.items[class_index],
                        dex,
                    )?
                };

                if let Some(existing) = self.classes.get(&class_name) {
                    let existing_insns: usize = existing
                        .methods()
                        .iter()
                        .filter_map(|m| m.code().map(|c| c.insns.len()))
                        .sum();
                    let new_insns: usize = class_node
                        .methods()
                        .iter()
                        .filter_map(|m| m.code().map(|c| c.insns.len()))
                        .sum();
                    if existing_insns >= new_insns {
                        continue;
                    }
                }
                self.classes.insert(class_name.clone(), class_node);
                changed = true;
            }
        }
        if changed {
            self.mark_override_analysis_dirty();
            self.link_inner_classes();
        }
        Ok(())
    }

    /// Load a single class by name
    pub fn load_class(&mut self, class_name: &str) -> DexResult<Option<&ClassNode>> {
        if self.classes.contains_key(class_name) {
            return Ok(self.classes.get(class_name));
        }

        let Some(&(dex_index, class_index)) = self.class_locations.get(class_name) else {
            return Ok(None);
        };
        self.dex_files[dex_index].materialize_class(class_index)?;
        let id = self.classes.len() as u32; // IDs are local to the loaded class set.
        let class_node = {
            let dex = &self.dex_files[dex_index];
            self.load_class_from_def(id, &dex.classes.items[class_index], dex)?
        };
        self.classes.insert(class_name.to_string(), class_node);
        self.mark_override_analysis_dirty();
        self.link_inner_classes();
        Ok(self.classes.get(class_name))
    }

    /// Load a class from ClassDefItem
    fn load_class_from_def(
        &self,
        id: u32,
        class_def: &rusty_dex::dex::classes::ClassDefItem,
        dex: &rusty_dex::dex::file::DexFile,
    ) -> DexResult<ClassNode> {
        let class_name = class_def.get_class_name().clone();
        let info = ClassInfo::from_type_descriptor(&class_name).map_err(DexError::ClassInfo)?;

        let raw_flags = class_def.get_access_flags_raw();
        let access_flags = AccessInfo::for_class(raw_flags);

        let mut class_node = ClassNode::new(id, info, access_flags);
        if let Some(superclass) = class_def.get_superclass() {
            class_node.set_super_class(parse_type(superclass)?);
        }
        for interface_descriptor in class_def.get_interfaces() {
            class_node.add_interface(parse_type(interface_descriptor)?);
        }
        class_node.source_file = class_def.get_source_file().map(str::to_string);
        class_node.signature = class_def.signature.clone();
        class_node.set_metadata(build_class_metadata(class_def));
        class_node.annotations = convert_annotations(&class_def.annotations)?;

        // Load fields
        let mut field_id = 0u32;
        for encoded_field in class_def.get_fields() {
            let field_node = self.load_field(field_id, encoded_field)?;
            class_node.add_field(field_node);
            field_id += 1;
        }

        // Load methods
        let mut method_id = 0u32;
        for encoded_method in class_def.get_methods() {
            if let Some(method_node) =
                self.load_method(method_id, &class_name, encoded_method, dex)?
            {
                class_node.add_method(method_node);
                method_id += 1;
            }
        }

        class_node.mark_loaded();
        Ok(class_node)
    }

    /// Load a field from EncodedField.
    fn load_field(
        &self,
        id: u32,
        encoded: &rusty_dex::dex::classes::EncodedField,
    ) -> DexResult<FieldNode> {
        let (declaring_class, name, field_type) = parse_field_ref(encoded.get_field())?;
        let info = FieldInfo::new(declaring_class, name, field_type);

        let raw_flags = encoded.get_access_flags_raw();
        let access_flags = AccessInfo::for_field(raw_flags);

        let mut field = FieldNode::new(id, info, access_flags);
        if let Some(value) = encoded.get_initial_value() {
            field = field
                .with_initial_value(DexValue::try_from(value).map_err(DexError::InvalidMetadata)?);
        }
        field.signature = encoded.signature.clone();
        field.annotations = convert_annotations(&encoded.annotations)?;
        Ok(field)
    }

    /// Load a method from EncodedMethod
    fn load_method(
        &self,
        id: u32,
        declaring_class: &str,
        encoded: &rusty_dex::dex::classes::EncodedMethod,
        dex: &rusty_dex::dex::file::DexFile,
    ) -> DexResult<Option<MethodNode>> {
        // Parse method prototype (e.g., "Lcom/example/Test;->methodName(II)V")
        let proto = &encoded.proto;

        // Extract method name and signature
        let (method_name, param_types, return_type) = parse_method_proto(proto)?;

        let info = MethodInfo::new(
            declaring_class.to_string(),
            method_name,
            param_types,
            return_type,
        );

        let raw_flags = encoded.get_access_flags_raw();
        let access_flags = AccessInfo::for_method(raw_flags);

        let throws = encoded
            .throws
            .iter()
            .map(|ty| parse_type(ty))
            .collect::<DexResult<Vec<_>>>()?;
        let mut method_node = MethodNode::new(id, info, access_flags)
            .with_throws(throws)
            .with_signature(encoded.signature.clone());
        method_node.annotations = convert_annotations(&encoded.annotations)?;
        method_node.parameter_annotations = encoded
            .parameter_annotations
            .iter()
            .map(|annotations| convert_annotations(annotations))
            .collect::<DexResult<Vec<_>>>()?;

        // Load code if present
        if let Some(code_item) = &encoded.code_item {
            let method_code = self.load_code_item(code_item)?;
            method_node = method_node.with_code(method_code);
        } else if let Some(code_item) = dex.decode_code_item(encoded)? {
            let method_code = self.load_code_item(&code_item)?;
            method_node = method_node.with_code(method_code);
        }

        Ok(Some(method_node))
    }

    /// Load code item (instructions and try-catch handlers)
    fn load_code_item(
        &self,
        code_item: &rusty_dex::dex::code_item::CodeItem,
    ) -> DexResult<MethodCode> {
        // Convert instructions to raw u16 words
        // NOTE: rusty_dex payload instructions (packed/sparse switch) return empty bytes(),
        // so we manually serialize their payload data here.
        let insns: Vec<u16> = if let Some(insns) = &code_item.insns {
            let mut words = Vec::new();
            for insn in insns {
                match insn {
                    rusty_dex::dex::instructions::Instructions::PackedSwitchPayload(payload) => {
                        words.push(0x0100);
                        words.push(payload.get_size() as u16);

                        let first_key = payload.get_first_key() as u32;
                        words.push((first_key & 0xFFFF) as u16);
                        words.push((first_key >> 16) as u16);

                        for &target in payload.get_targets() {
                            let target = target as u32;
                            words.push((target & 0xFFFF) as u16);
                            words.push((target >> 16) as u16);
                        }
                    }
                    rusty_dex::dex::instructions::Instructions::SparseSwitchPayload(payload) => {
                        words.push(0x0200);
                        words.push(payload.get_size() as u16);

                        for &key in payload.get_keys() {
                            let key = key as u32;
                            words.push((key & 0xFFFF) as u16);
                            words.push((key >> 16) as u16);
                        }

                        for &target in payload.get_targets() {
                            let target = target as u32;
                            words.push((target & 0xFFFF) as u16);
                            words.push((target >> 16) as u16);
                        }
                    }
                    rusty_dex::dex::instructions::Instructions::FillArrayDataPayload(payload) => {
                        words.push(0x0300);
                        words.push(payload.get_element_width());

                        let size = payload.get_size();
                        words.push((size & 0xFFFF) as u16);
                        words.push((size >> 16) as u16);

                        for chunk in payload.get_data().chunks(2) {
                            let low = chunk.first().copied().unwrap_or(0) as u16;
                            let high = chunk.get(1).copied().unwrap_or(0) as u16;
                            words.push(low | (high << 8));
                        }
                    }
                    _ => {
                        words.extend(insn.bytes().iter().copied());
                    }
                }
            }
            words
        } else {
            Vec::new()
        };

        // Load try-catch handlers
        let mut tries = Vec::new();
        if let Some(try_items) = &code_item.tries {
            // Get handlers list if available
            let handlers_list = code_item.handlers.as_ref();

            for try_item in try_items {
                let mut handlers = Vec::new();

                // Find the matching handler by offset
                if let Some(all_handlers) = handlers_list {
                    for handler in all_handlers {
                        if handler.offset == try_item.handler_off {
                            // Add typed handlers
                            for type_addr in &handler.handlers {
                                let exception_type = type_addr
                                    .decoded_type
                                    .parse::<ArgType>()
                                    .map_err(|source| DexError::InvalidDescriptor {
                                        descriptor: type_addr.decoded_type.clone(),
                                        source,
                                    })?;
                                handlers
                                    .push(ExceptionHandler::typed(exception_type, type_addr.addr));
                            }
                            // Add catch-all if present
                            if let Some(catch_all_addr) = handler.catch_all_addr {
                                handlers.push(ExceptionHandler::catch_all(catch_all_addr));
                            }
                            break;
                        }
                    }
                }

                let end_addr = try_item.start_addr + try_item.insn_count as u32;
                tries.push(TryCatchBlock {
                    start_addr: try_item.start_addr,
                    end_addr,
                    handlers,
                });
            }
        }

        Ok(MethodCode {
            registers_size: code_item.registers_size,
            ins_size: code_item.ins_size,
            outs_size: code_item.outs_size,
            insns,
            tries,
            debug_info: code_item
                .debug_info
                .as_ref()
                .map(convert_debug_info)
                .transpose()?,
        })
    }
}

/// Convert the rusty-dex `DebugInfo` (raw DEX form) into dexdec's
/// `frontend::DebugInfo` (typed via `ArgType`).
fn convert_debug_info(info: &rusty_dex::dex::debug_info::DebugInfo) -> DexResult<DebugInfo> {
    let local_vars = info
        .local_vars
        .iter()
        .map(|var| {
            Ok(LocalVarInfo {
                name: var.name.clone(),
                var_type: parse_type(&var.type_descriptor)?,
                start_addr: var.start_addr,
                end_addr: var.end_addr,
                register: var.register,
            })
        })
        .collect::<DexResult<Vec<_>>>()?;
    Ok(DebugInfo {
        line_numbers: info.line_numbers.clone(),
        local_vars,
        param_names: info.param_names.clone(),
    })
}

impl DexFileReader {
    // ==================== Access Methods ====================

    /// Get loaded class by type descriptor
    pub fn get_class(&self, type_desc: &str) -> Option<&ClassNode> {
        self.classes.get(type_desc)
    }

    /// Get mutable class by type descriptor
    pub(crate) fn get_class_mut(&mut self, type_desc: &str) -> Option<&mut ClassNode> {
        self.classes.get_mut(type_desc)
    }

    // get_class_by_id removed as IDs are ambiguous in multi-dex context

    /// Get all loaded classes
    pub fn classes(&self) -> impl Iterator<Item = &ClassNode> {
        self.classes.values()
    }

    /// Get class count
    pub fn loaded_class_count(&self) -> usize {
        self.classes.len()
    }

    /// Discard materialized frontend nodes while retaining parsed DEX metadata.
    ///
    /// Interactive requests use this to keep one class's dependency closure
    /// from expanding the analysis graph of every later request.
    pub fn clear_loaded_classes(&mut self) {
        if self.classes.is_empty() {
            return;
        }
        self.classes.clear();
        self.mark_override_analysis_dirty();
    }

    /// Get the index of the DEX file containing the class
    pub fn get_dex_index(&self, class_name: &str) -> Option<usize> {
        self.class_locations
            .get(class_name)
            .map(|(dex_index, _)| *dex_index)
    }

    pub fn override_analysis_state(&self) -> AnalysisState {
        self.override_analysis_state
    }

    pub fn mark_override_analysis_dirty(&mut self) {
        self.override_analysis_state = AnalysisState::Dirty;
        self.analysis_diagnostics.clear();
        self.loaded_classes_revision = self.loaded_classes_revision.wrapping_add(1);
    }

    pub fn mark_override_analysis_ready(&mut self) {
        self.override_analysis_state = AnalysisState::Ready;
    }

    pub fn loaded_classes_revision(&self) -> u64 {
        self.loaded_classes_revision
    }

    pub fn analysis_diagnostics(&self) -> &[AnalysisDiagnostic] {
        &self.analysis_diagnostics
    }

    pub(crate) fn replace_analysis_diagnostics(&mut self, diagnostics: Vec<AnalysisDiagnostic>) {
        self.analysis_diagnostics = diagnostics;
    }

    pub fn ensure_override_analysis(&mut self) -> DexResult<()> {
        if self.override_analysis_state == AnalysisState::Ready {
            return Ok(());
        }
        self.load_source_hierarchy_closure()?;
        self.load_hierarchy_member_types()?;
        self.load_source_hierarchy_closure()?;
        crate::analysis::method_override::analyze_loaded_method_overrides(self)?;
        self.mark_override_analysis_ready();
        Ok(())
    }

    /// Loads direct nested declarations of the current source hierarchy.
    /// Member type names participate in Kotlin inheritance and must therefore
    /// be present before source ABI and lexical name allocation are solved.
    /// Method bodies remain undecoded.
    fn load_hierarchy_member_types(&mut self) -> DexResult<()> {
        let members = self
            .classes
            .values()
            .flat_map(|class| class.inner_class_names().iter().cloned())
            .filter(|member| !self.classes.contains_key(member))
            .collect::<BTreeSet<_>>();
        for member in members {
            self.load_class(&member)?;
        }
        Ok(())
    }

    /// Load every superclass and interface that is available in the input DEX
    /// before deriving source-level override contracts.
    fn load_source_hierarchy_closure(&mut self) -> DexResult<()> {
        loop {
            let parents = self
                .classes
                .values()
                .flat_map(|class| {
                    class
                        .super_class
                        .iter()
                        .chain(&class.interfaces)
                        .map(ArgType::to_descriptor)
                })
                .filter(|descriptor| !self.classes.contains_key(descriptor))
                .collect::<BTreeSet<_>>();
            let mut loaded = false;
            for parent in parents {
                loaded |= self.load_class(&parent)?.is_some();
            }
            if !loaded {
                return Ok(());
            }
        }
    }

    fn link_inner_classes(&mut self) {
        let class_names = self.classes.keys().cloned().collect::<Vec<_>>();
        let enclosing_method_static = class_names
            .iter()
            .filter_map(|class_name| {
                let reference = self
                    .classes
                    .get(class_name)?
                    .metadata
                    .enclosing
                    .as_ref()?
                    .method_reference
                    .as_deref()?
                    .parse::<crate::ir::MethodReference>()
                    .ok()?;
                let owner = self.classes.get(&reference.owner.to_descriptor())?;
                let method = owner.methods().iter().find(|method| {
                    method.name() == reference.name
                        && method.param_types() == reference.descriptor.parameters
                        && method.return_type() == &reference.descriptor.return_type
                })?;
                Some((class_name.clone(), method.is_static()))
            })
            .collect::<BTreeMap<_, _>>();
        for class_name in &class_names {
            if let Some(class) = self.classes.get_mut(class_name) {
                class.clear_inner_classes();
                class.clear_parent_class();
                if let Some(enclosing) = class.metadata.enclosing.as_mut() {
                    enclosing.method_static = enclosing_method_static.get(class_name).copied();
                }
            }
        }

        for class_name in &class_names {
            if let Some(parent) = self.nested_classes.parents.get(class_name).cloned() {
                if let Some(class) = self.classes.get_mut(class_name) {
                    class.set_parent_class(parent);
                }
            }
            if let Some(children) = self.nested_classes.children.get(class_name).cloned() {
                if let Some(class) = self.classes.get_mut(class_name) {
                    for child in children {
                        class.add_inner_class(child);
                    }
                }
            }
        }

        for class_name in &class_names {
            if let Some(class) = self.classes.get_mut(class_name) {
                class.sort_inner_classes();
            }
        }
    }

    // ==================== Symbol Resolution ====================

    /// Get string by index
    pub fn get_string(
        &self,
        dex_idx: usize,
        idx: u32,
    ) -> Option<&rusty_dex::dex::strings::DexString> {
        if let Some(dex) = self.dex_files.get(dex_idx) {
            dex.strings.strings.get(idx as usize)
        } else {
            None
        }
    }

    /// Get type by index
    pub fn get_type(&self, dex_idx: usize, idx: u32) -> Option<&str> {
        if let Some(dex) = self.dex_files.get(dex_idx) {
            dex.types.items.get(idx as usize).map(|s| s.as_str())
        } else {
            None
        }
    }

    /// Get method reference by index (returns full signature like "Lcom/example/Test;->method(II)V")
    pub fn get_method(&self, dex_idx: usize, idx: u32) -> Option<&str> {
        if let Some(dex) = self.dex_files.get(dex_idx) {
            dex.methods.items.get(idx as usize).map(|s| s.as_str())
        } else {
            None
        }
    }

    /// Get field reference by index
    pub fn get_field(&self, dex_idx: usize, idx: u32) -> Option<&str> {
        if let Some(dex) = self.dex_files.get(dex_idx) {
            dex.fields.items.get(idx as usize).map(|s| s.as_str())
        } else {
            None
        }
    }
}

fn build_class_metadata(class_def: &rusty_dex::dex::classes::ClassDefItem) -> ClassMetadata {
    ClassMetadata {
        inner_class: class_def
            .get_inner_class_annotation()
            .map(|inner| InnerClassInfo {
                simple_name: inner.name.clone(),
                access_flags_raw: inner.access_flags,
            }),
        member_classes: class_def.get_member_classes().to_vec(),
        enclosing: if class_def.get_enclosing_class().is_some()
            || class_def.get_enclosing_method().is_some()
        {
            Some(EnclosingInfo {
                class_descriptor: class_def.get_enclosing_class().map(str::to_string),
                method_reference: class_def.get_enclosing_method().map(str::to_string),
                method_static: None,
            })
        } else {
            None
        },
    }
}

fn convert_annotations(
    annotations: &[rusty_dex::dex::classes::DexAnnotation],
) -> DexResult<Vec<AnnotationNode>> {
    let annotations = annotations
        .iter()
        .map(AnnotationNode::try_from)
        .collect::<Result<Vec<_>, MetadataConversionError>>()
        .map_err(DexError::InvalidMetadata)?;
    Ok(annotations
        .into_iter()
        .filter(AnnotationNode::is_java_source_annotation)
        .collect())
}

/// Parse access flags from string representation (e.g., "public static final")
#[cfg(test)]
fn parse_access_flags_string(flags_str: &str) -> u32 {
    use super::access_info::access_flags::*;

    let mut raw = 0u32;
    let lower = flags_str.to_lowercase();

    if lower.contains("public") {
        raw |= PUBLIC;
    }
    if lower.contains("private") {
        raw |= PRIVATE;
    }
    if lower.contains("protected") {
        raw |= PROTECTED;
    }
    if lower.contains("static") {
        raw |= STATIC;
    }
    if lower.contains("final") {
        raw |= FINAL;
    }
    if lower.contains("synchronized") {
        raw |= SYNCHRONIZED;
    }
    if lower.contains("volatile") {
        raw |= VOLATILE;
    }
    if lower.contains("bridge") {
        raw |= BRIDGE;
    }
    if lower.contains("transient") {
        raw |= TRANSIENT;
    }
    if lower.contains("varargs") {
        raw |= VARARGS;
    }
    if lower.contains("native") {
        raw |= NATIVE;
    }
    if lower.contains("interface") {
        raw |= INTERFACE;
    }
    if lower.contains("abstract") {
        raw |= ABSTRACT;
    }
    if lower.contains("strict") {
        raw |= STRICT;
    }
    if lower.contains("synthetic") {
        raw |= SYNTHETIC;
    }
    if lower.contains("annotation") {
        raw |= ANNOTATION;
    }
    if lower.contains("enum") {
        raw |= ENUM;
    }
    if lower.contains("constructor") {
        raw |= CONSTRUCTOR;
    }
    if lower.contains("declared_synchronized") || lower.contains("declared-synchronized") {
        raw |= DECLARED_SYNCHRONIZED;
    }

    raw
}

/// Parse field reference string.
/// Format: "Lcom/example/Test;->fieldName:I"
fn parse_field_ref(field_ref: &str) -> DexResult<(String, String, ArgType)> {
    let field =
        field_ref
            .parse::<FieldReference>()
            .map_err(|source| DexError::InvalidMemberReference {
                reference: field_ref.to_string(),
                source,
            })?;
    Ok((field.owner.to_descriptor(), field.name, field.field_type))
}

/// Parse method prototype string
/// Format: "Lcom/example/Test;->methodName(II)V" or "methodName(II)V"
fn parse_method_proto(proto: &str) -> DexResult<(String, Vec<ArgType>, ArgType)> {
    // Try to find -> separator
    let method_part = if let Some(idx) = proto.find("->") {
        &proto[idx + 2..]
    } else {
        proto
    };

    // Find the method name and its exact DEX descriptor.
    let paren_start = method_part
        .find('(')
        .ok_or_else(|| DexError::MalformedMethodPrototype(proto.to_string()))?;
    let method_name = method_part[..paren_start].to_string();
    let descriptor = method_part[paren_start..]
        .parse::<MethodDescriptor>()
        .map_err(|source| DexError::InvalidDescriptor {
            descriptor: method_part[paren_start..].to_string(),
            source,
        })?;
    Ok((method_name, descriptor.parameters, descriptor.return_type))
}

fn parse_type(descriptor: &str) -> DexResult<ArgType> {
    descriptor
        .parse::<ArgType>()
        .map_err(|source| DexError::InvalidDescriptor {
            descriptor: descriptor.to_string(),
            source,
        })
}

fn reference_matches(
    target: &DexReferenceTarget,
    candidates: Option<&BTreeSet<&str>>,
    reference: rusty_dex::dex::references::DexCodeReference<'_>,
) -> bool {
    use rusty_dex::dex::references::DexReferenceKind;

    match target {
        DexReferenceTarget::Field(field) => {
            reference.kind == DexReferenceKind::Field && reference.target == field
        }
        DexReferenceTarget::Method(method) => {
            reference.kind == DexReferenceKind::Method && reference.target == method
        }
        DexReferenceTarget::FieldName { .. } => {
            reference.kind == DexReferenceKind::Field
                && candidates.is_some_and(|targets| targets.contains(reference.target))
        }
        DexReferenceTarget::MethodArity { .. } => {
            reference.kind == DexReferenceKind::Method
                && candidates.is_some_and(|targets| targets.contains(reference.target))
        }
        DexReferenceTarget::MethodParameters { .. } => {
            reference.kind == DexReferenceKind::Method
                && candidates.is_some_and(|targets| targets.contains(reference.target))
        }
        DexReferenceTarget::Class(class) => match reference.kind {
            DexReferenceKind::Type => reference.target == class,
            DexReferenceKind::Field => {
                reference
                    .target
                    .parse::<FieldReference>()
                    .is_ok_and(|field| {
                        type_mentions_class(&field.owner, class)
                            || type_mentions_class(&field.field_type, class)
                    })
            }
            DexReferenceKind::Method => {
                reference
                    .target
                    .parse::<MethodReference>()
                    .is_ok_and(|method| {
                        type_mentions_class(&method.owner, class)
                            || method
                                .descriptor
                                .parameters
                                .iter()
                                .any(|parameter| type_mentions_class(parameter, class))
                            || type_mentions_class(&method.descriptor.return_type, class)
                    })
            }
        },
    }
}

fn reference_candidates<'a>(
    dex: &'a rusty_dex::dex::file::DexFile,
    target: &DexReferenceTarget,
) -> Option<BTreeSet<&'a str>> {
    match target {
        DexReferenceTarget::FieldName { class, name } => Some(
            dex.fields
                .items
                .iter()
                .map(String::as_str)
                .filter(|reference| field_name_matches(reference, class, name))
                .collect(),
        ),
        DexReferenceTarget::MethodArity { class, name, arity } => Some(
            dex.methods
                .items
                .iter()
                .map(String::as_str)
                .filter(|reference| method_arity_matches(reference, class, name, *arity))
                .collect(),
        ),
        DexReferenceTarget::MethodParameters {
            class,
            name,
            parameters,
        } => Some(
            dex.methods
                .items
                .iter()
                .map(String::as_str)
                .filter(|reference| method_parameters_match(reference, class, name, parameters))
                .collect(),
        ),
        _ => None,
    }
}

fn field_name_matches(reference: &str, class: &str, name: &str) -> bool {
    reference
        .strip_prefix(class)
        .and_then(|rest| rest.strip_prefix("->"))
        .and_then(|rest| rest.split_once(':'))
        .is_some_and(|(candidate, _)| candidate == name)
}

fn method_arity_matches(reference: &str, class: &str, name: &str, arity: usize) -> bool {
    method_descriptor(reference, class, name)
        .is_some_and(|descriptor| descriptor.parameters.len() == arity)
}

fn method_parameters_match(
    reference: &str,
    class: &str,
    name: &str,
    parameters: &[String],
) -> bool {
    method_descriptor(reference, class, name).is_some_and(|descriptor| {
        descriptor.parameters.len() == parameters.len()
            && descriptor
                .parameters
                .iter()
                .zip(parameters)
                .all(|(actual, expected)| actual.to_descriptor() == *expected)
    })
}

fn method_descriptor(reference: &str, class: &str, name: &str) -> Option<MethodDescriptor> {
    let Some(method) = reference
        .strip_prefix(class)
        .and_then(|rest| rest.strip_prefix("->"))
    else {
        return None;
    };
    let Some(descriptor_start) = method.find('(') else {
        return None;
    };
    (&method[..descriptor_start] == name)
        .then(|| method[descriptor_start..].parse::<MethodDescriptor>().ok())
        .flatten()
}

fn type_mentions_class(ty: &ArgType, class: &str) -> bool {
    match ty {
        ArgType::Object(_) => ty.to_descriptor() == class,
        ArgType::Array(element) => type_mentions_class(element, class),
        ArgType::Primitive(_) | ArgType::Unknown(_) => false,
    }
}

fn reference_location(
    reference: rusty_dex::dex::references::DexCodeReference<'_>,
) -> Option<DexReferenceLocation> {
    let (class, member) = reference.caller.split_once("->")?;
    let descriptor_start = member.find('(')?;
    Some(DexReferenceLocation {
        class: class.to_string(),
        method: member[..descriptor_start].to_string(),
        descriptor: member[descriptor_start..].to_string(),
        offset: reference.offset,
    })
}

/// Check if a file is a raw DEX file (not APK)
/// DEX files start with "dex\n" magic
fn is_raw_dex(path: &Path) -> DexResult<bool> {
    use std::io::Read;
    let mut file = std::fs::File::open(path)?;
    let mut magic = [0u8; 8];

    if file.read(&mut magic).unwrap_or(0) < 8 {
        return Ok(false);
    }

    // DEX magic: "dex\n" followed by version (e.g., "035\0")
    Ok(&magic[0..4] == b"dex\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_method_proto() {
        let (name, params, ret) = parse_method_proto("Lcom/example/Test;->add(II)I").unwrap();
        assert_eq!(name, "add");
        assert_eq!(params.len(), 2);
        assert_eq!(ret, ArgType::INT);
    }

    #[test]
    fn test_parse_field_ref() {
        let (declaring_class, name, field_type) =
            parse_field_ref("Lcom/example/Test;->lock:Ljava/lang/Object;").unwrap();
        assert_eq!(declaring_class, "Lcom/example/Test;");
        assert_eq!(name, "lock");
        assert_eq!(field_type, ArgType::object("java/lang/Object"));
    }

    #[test]
    fn test_parse_access_flags_string() {
        let flags = parse_access_flags_string("public static final");
        assert!(flags & 0x0001 != 0); // PUBLIC
        assert!(flags & 0x0008 != 0); // STATIC
        assert!(flags & 0x0010 != 0); // FINAL
    }
}
