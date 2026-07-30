//! High-level API for DEX decompilation
//!
//! This module provides a unified interface combining DEX file parsing
//! and bytecode-to-IR conversion.

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use crate::analysis::java_backend::{FunctionObjectClass, JavaSourceAbi, SourceSignatureInference};
use crate::analysis::kotlin_backend::KotlinSourceAbi;
use crate::analysis::{
    ClassMethodInput, JavaDecompiler, JavaDecompilerConfig, JavaDecompilerError, KotlinDecompiler,
    KotlinDecompilerConfig, KotlinDecompilerError, MethodRecoveryFailure, MethodRecoveryStage,
    NestedClassInput,
};
use crate::decoder::method_decoder::MethodDecoder;
use crate::frontend::{ClassNode, DexFileReader, DexResult, MethodCode};
use crate::ir::splitter::Splitter;
use crate::ir::{
    arg::InsnArg,
    cfg::{MethodContext, CFG},
    insn::{InsnNode, InsnType, InvokeType},
    ty::{ArgType, MethodDescriptor},
    FieldReference, MemberReference, MethodReference, Utf16String,
};

mod catalog;
mod decompiler;
mod references;

pub use catalog::{
    ArchiveCatalog, ArchiveMemberCatalog, ClassKind, ClassOutline, ClassSummary, FieldOutline,
    MemberKind, MemberSummary, MemberVisitor, MethodOutline,
};
pub use decompiler::{
    java_source_path, kotlin_source_path, source_path, BatchSummary, ClassBatch, ClassFailure,
    ClassSelector, DecompileOptions, Decompiler, MethodOutput, MethodRequest, SourceLanguage,
    SourceUnit,
};
pub use references::{ReferenceLocation, ReferenceResults, ReferenceTarget};

/// Decompiler context - holds state for decompilation
pub struct DecompilerContext {
    /// DEX file reader
    reader: DexFileReader,
    /// Cached method IRs (class_name -> method_name -> IR)
    method_irs: HashMap<String, HashMap<String, CFG>>,
    /// Revision of the loaded class graph captured by `method_irs`.
    method_cache_revision: u64,
    /// Immutable hierarchy facts shared by every method in one class-graph revision.
    type_hierarchy_cache: Option<(u64, Arc<crate::ir::analysis::ClassHierarchyIndex>)>,
    /// Immutable target-language ABI facts shared by one class-graph revision.
    java_source_abi_cache: Option<(u64, Arc<JavaSourceAbi>)>,
    kotlin_source_abi_cache: Option<(u64, Arc<KotlinSourceAbi>)>,
    kotlin_contract_roots: std::collections::BTreeSet<MethodReference>,
}

trait SourceBackend {
    type Config: Clone;

    fn prepare_context(context: &mut DecompilerContext) -> Result<(), DecompileError>;

    fn generate_method(
        context: &mut DecompilerContext,
        config: &Self::Config,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
        hierarchy: Arc<crate::ir::analysis::ClassHierarchyIndex>,
        class: &ClassNode,
        method: &crate::frontend::MethodNode,
        cfg: &mut CFG,
    ) -> Result<String, DecompileError>;

    fn generate_class(
        context: &mut DecompilerContext,
        config: &Self::Config,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
        hierarchy: Arc<crate::ir::analysis::ClassHierarchyIndex>,
        class: &ClassNode,
        methods: &mut Vec<ClassMethodInput>,
        nested: Vec<NestedClassInput>,
    ) -> Result<String, DecompileError>;
}

struct JavaSourceBackend;
struct KotlinSourceBackend;

impl SourceBackend for JavaSourceBackend {
    type Config = JavaDecompilerConfig;

    fn prepare_context(context: &mut DecompilerContext) -> Result<(), DecompileError> {
        context.prepare_java_source_abi()
    }

    fn generate_method(
        context: &mut DecompilerContext,
        config: &Self::Config,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
        hierarchy: Arc<crate::ir::analysis::ClassHierarchyIndex>,
        class: &ClassNode,
        method: &crate::frontend::MethodNode,
        cfg: &mut CFG,
    ) -> Result<String, DecompileError> {
        JavaDecompiler::new(config.clone())
            .with_shared_type_hierarchy(hierarchy)
            .with_source_abi(context.java_source_abi())
            .with_analysis_observer(observer)
            .generate_method_with_context(class, method, cfg)
            .map_err(DecompileError::from)
    }

    fn generate_class(
        context: &mut DecompilerContext,
        config: &Self::Config,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
        hierarchy: Arc<crate::ir::analysis::ClassHierarchyIndex>,
        class: &ClassNode,
        methods: &mut Vec<ClassMethodInput>,
        nested: Vec<NestedClassInput>,
    ) -> Result<String, DecompileError> {
        JavaDecompiler::new(config.clone())
            .with_shared_type_hierarchy(hierarchy)
            .with_source_abi(context.java_source_abi())
            .with_analysis_observer(observer)
            .generate_class_with_nested(class, methods, nested)
            .map_err(DecompileError::from)
    }
}

impl SourceBackend for KotlinSourceBackend {
    type Config = KotlinDecompilerConfig;

    fn prepare_context(context: &mut DecompilerContext) -> Result<(), DecompileError> {
        context.kotlin_source_abi().map(|_| ())
    }

    fn generate_method(
        context: &mut DecompilerContext,
        config: &Self::Config,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
        hierarchy: Arc<crate::ir::analysis::ClassHierarchyIndex>,
        class: &ClassNode,
        method: &crate::frontend::MethodNode,
        cfg: &mut CFG,
    ) -> Result<String, DecompileError> {
        KotlinDecompiler::new(config.clone())
            .with_shared_type_hierarchy(hierarchy)
            .with_source_abi(context.kotlin_source_abi()?)
            .with_analysis_observer(observer)
            .generate_method_with_context(class, method, cfg)
            .map_err(DecompileError::from)
    }

    fn generate_class(
        context: &mut DecompilerContext,
        config: &Self::Config,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
        hierarchy: Arc<crate::ir::analysis::ClassHierarchyIndex>,
        class: &ClassNode,
        methods: &mut Vec<ClassMethodInput>,
        nested: Vec<NestedClassInput>,
    ) -> Result<String, DecompileError> {
        KotlinDecompiler::new(config.clone())
            .with_shared_type_hierarchy(hierarchy)
            .with_source_abi(context.kotlin_source_abi()?)
            .with_analysis_observer(observer)
            .generate_class_with_nested(class, methods, nested)
            .map_err(DecompileError::from)
    }
}

impl DecompilerContext {
    /// Create a context from an already parsed reader.
    pub fn from_reader(reader: DexFileReader) -> Self {
        Self {
            reader,
            method_irs: HashMap::new(),
            method_cache_revision: 0,
            type_hierarchy_cache: None,
            java_source_abi_cache: None,
            kotlin_source_abi_cache: None,
            kotlin_contract_roots: std::collections::BTreeSet::new(),
        }
    }

    /// Whether a loaded class owns a source compilation unit. Only classes
    /// with explicit inner-class ownership are emitted through another source
    /// unit; implementation shape alone is not evidence of lexical ownership.
    pub fn class_is_compilation_unit(&self, class_name: &str) -> bool {
        self.reader
            .get_class(class_name)
            .is_some_and(|class| !class.is_inner())
    }

    /// Create a new decompiler context from a DEX file
    pub fn from_file<P: AsRef<Path>>(path: P) -> DexResult<Self> {
        let reader = std::thread::scope(|scope| {
            let platform = scope.spawn(crate::analysis::method_override::preload_platform_symbols);
            let reader = DexFileReader::from_file(path);
            match platform.join() {
                Ok(result) => result?,
                Err(payload) => std::panic::resume_unwind(payload),
            }
            reader
        })?;
        Ok(Self::from_reader(reader))
    }

    /// Get the underlying DEX file reader
    pub fn reader(&self) -> &DexFileReader {
        &self.reader
    }

    /// Get mutable DEX file reader
    pub fn reader_mut(&mut self) -> &mut DexFileReader {
        self.clear_method_cache();
        self.type_hierarchy_cache = None;
        self.java_source_abi_cache = None;
        self.kotlin_source_abi_cache = None;
        self.kotlin_contract_roots.clear();
        &mut self.reader
    }

    /// Load all classes from the DEX file
    pub fn load_all_classes(&mut self) -> DexResult<()> {
        self.reader.load_all_classes()?;
        self.reader.ensure_override_analysis()?;
        Ok(())
    }

    /// Load a specific class by name
    pub fn load_class(&mut self, class_name: &str) -> DexResult<Option<&ClassNode>> {
        self.reader.load_class(class_name)?;
        self.reader.ensure_override_analysis()?;
        Ok(self.reader.get_class(class_name))
    }

    fn load_class_deferred(&mut self, class_name: &str) -> DexResult<Option<&ClassNode>> {
        self.reader.load_class(class_name)
    }

    /// Load a set of classes and rebuild class-graph facts once for the batch.
    pub fn load_classes<'a>(
        &mut self,
        class_names: impl IntoIterator<Item = &'a str>,
    ) -> DexResult<()> {
        for class_name in class_names {
            self.reader.load_class(class_name)?;
        }
        self.reader.ensure_override_analysis()?;
        Ok(())
    }

    fn load_classes_deferred<'a>(
        &mut self,
        class_names: impl IntoIterator<Item = &'a str>,
    ) -> DexResult<()> {
        for class_name in class_names {
            self.reader.load_class(class_name)?;
        }
        Ok(())
    }

    /// Get all class names in the DEX file
    pub fn class_names(&self) -> Vec<String> {
        self.reader.class_names()
    }

    /// Get number of classes
    pub fn class_count(&self) -> usize {
        self.reader.class_count()
    }

    /// Get a loaded class
    pub fn get_class(&self, class_name: &str) -> Option<&ClassNode> {
        self.reader.get_class(class_name)
    }

    /// Clear cached method IRs to save memory
    pub fn clear_method_cache(&mut self) {
        self.method_irs.clear();
        self.method_cache_revision = self.reader.loaded_classes_revision();
    }

    /// Begin a fresh request-local class graph without reparsing DEX metadata.
    pub fn clear_analysis_scope(&mut self) {
        self.reader.clear_loaded_classes();
        self.clear_method_cache();
        self.type_hierarchy_cache = None;
        self.java_source_abi_cache = None;
        self.kotlin_source_abi_cache = None;
        self.kotlin_contract_roots.clear();
    }

    /// Decode a method's bytecode into IR
    ///
    /// This converts the raw Dalvik bytecode into our IR representation
    /// with basic blocks, control flow, and typed instructions.
    pub fn decode_method(
        &mut self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
    ) -> DexResult<Option<&CFG>> {
        if self.method_cache_revision != self.reader.loaded_classes_revision() {
            self.method_irs.clear();
            self.method_cache_revision = self.reader.loaded_classes_revision();
        }
        // Form a cache key that includes descriptor to handle overloading
        let cache_key = if let Some(desc) = descriptor {
            format!("{}{}", method_name, desc)
        } else {
            method_name.to_string()
        };

        // Check cache first
        if let Some(class_cache) = self.method_irs.get(class_name) {
            if class_cache.contains_key(&cache_key) {
                return Ok(self
                    .method_irs
                    .get(class_name)
                    .and_then(|c| c.get(&cache_key)));
            }
        }

        // Get the class and method
        let (method_code, owner, param_types, return_type, is_static, declared_synchronized) = {
            let class = match self.reader.get_class(class_name) {
                Some(c) => c,
                None => return Ok(None),
            };

            let method = match class.methods().iter().find(|m| {
                if m.info.name != method_name {
                    return false;
                }
                if let Some(desc) = descriptor {
                    m.info.descriptor() == normalize_descriptor(desc)
                } else {
                    true
                }
            }) {
                Some(m) => m,
                None => return Ok(None),
            };

            let param_types = method.info.param_types.clone();
            let return_type = method.info.return_type.clone();
            let is_static = method.access_flags.is_static();
            let declared_synchronized = method.access_flags.is_declared_synchronized();
            match method.code() {
                Some(code) => (
                    code.clone(),
                    class.class_type().clone(),
                    param_types,
                    return_type,
                    is_static,
                    declared_synchronized,
                ),
                None => return Ok(None), // Abstract or native method
            }
        };

        // Decode the method
        let mut ir = Self::decode_method_code(&method_code)?;

        // Update method name and signature
        ir.set_method(
            MethodContext::new(
                owner,
                method_name,
                MethodDescriptor {
                    parameters: param_types,
                    return_type,
                },
                is_static,
            )
            .with_declared_synchronization(declared_synchronized),
        );

        // Get DEX file index for symbol resolution
        let dex_idx = self
            .reader
            .get_dex_index(class_name)
            .ok_or_else(|| crate::frontend::DexError::MissingDexForClass(class_name.to_string()))?;

        // Resolve symbol references using DEX file tables
        self.resolve_symbols(&mut ir, dex_idx)?;

        // Cache and return
        let class_cache = self
            .method_irs
            .entry(class_name.to_string())
            .or_insert_with(HashMap::new);
        class_cache.insert(cache_key.clone(), ir);

        Ok(self
            .method_irs
            .get(class_name)
            .and_then(|c| c.get(&cache_key)))
    }

    /// Resolve symbol references in IR instructions
    fn resolve_symbols(&self, ir: &mut CFG, dex_idx: usize) -> DexResult<()> {
        for block in ir.blocks.values_mut() {
            for insn in &mut block.insns {
                // Resolve method references
                if let Some(method_idx) = insn.payload.method_index {
                    let raw = self
                        .reader
                        .get_method(dex_idx, method_idx)
                        .ok_or(crate::frontend::DexError::InvalidMethodIndex(method_idx))?
                        .to_string();
                    let method = raw.parse::<MethodReference>().map_err(|source| {
                        crate::frontend::DexError::InvalidMemberReference {
                            reference: raw,
                            source,
                        }
                    })?;
                    normalize_invoke_args(insn, &method)?;
                    apply_invoke_return_type(insn, &method);
                    insn.payload.reference = Some(MemberReference::Method(method));
                }

                // Resolve field references
                if let Some(field_idx) = insn.payload.field_index {
                    let raw = self
                        .reader
                        .get_field(dex_idx, field_idx)
                        .ok_or(crate::frontend::DexError::InvalidFieldIndex(field_idx))?
                        .to_string();
                    let field = raw.parse::<FieldReference>().map_err(|source| {
                        crate::frontend::DexError::InvalidMemberReference {
                            reference: raw,
                            source,
                        }
                    })?;
                    apply_field_type(insn, &field);
                    insn.payload.reference = Some(MemberReference::Field(field));
                }

                // Resolve string references
                if let Some(string_idx) = insn.payload.string_index {
                    if insn.payload.string_value.is_none() {
                        let string = self
                            .reader
                            .get_string(dex_idx, string_idx)
                            .ok_or(crate::frontend::DexError::InvalidStringIndex(string_idx))?;
                        insn.payload.string_value =
                            Some(Utf16String::from_utf16(string.utf16().to_vec()));
                    }
                }

                // Resolve type references
                if let Some(type_idx) = insn.payload.type_index {
                    if insn.payload.class_type.is_none() {
                        let descriptor = self
                            .reader
                            .get_type(dex_idx, type_idx)
                            .ok_or(crate::frontend::DexError::InvalidTypeIndex(type_idx))?;
                        insn.payload.class_type =
                            Some(descriptor.parse::<ArgType>().map_err(|source| {
                                crate::frontend::DexError::InvalidDescriptor {
                                    descriptor: descriptor.to_string(),
                                    source,
                                }
                            })?);
                    }
                }
            }
        }
        Ok(())
    }

    /// Decode all methods in a class
    pub fn decode_class_methods(&mut self, class_name: &str) -> DexResult<Vec<(&str, &CFG)>> {
        // First collect method names
        let methods: Vec<(String, String)> = {
            let class = match self.reader.get_class(class_name) {
                Some(c) => c,
                None => return Ok(Vec::new()),
            };
            class
                .methods()
                .iter()
                .filter(|m| m.code().is_some())
                .map(|m| (m.info.name.clone(), m.info.descriptor()))
                .collect()
        };

        // Decode each method
        for (method_name, descriptor) in &methods {
            self.decode_method(class_name, method_name, Some(descriptor))?;
        }

        Ok(self
            .method_irs
            .get(class_name)
            .into_iter()
            .flat_map(|methods| methods.iter())
            .map(|(name, cfg)| (name.as_str(), cfg))
            .collect())
    }

    /// Get cached method IR
    pub fn get_method_ir(
        &self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
    ) -> Option<&CFG> {
        let cache_key = if let Some(desc) = descriptor {
            format!("{}{}", method_name, desc)
        } else {
            method_name.to_string()
        };

        self.method_irs
            .get(class_name)
            .and_then(|c| c.get(&cache_key))
    }

    /// Return the immutable type hierarchy used by method decompilation for
    /// the current loaded-class revision.
    pub fn type_hierarchy(
        &mut self,
    ) -> Result<Arc<crate::ir::analysis::ClassHierarchyIndex>, DecompileError> {
        let revision = self.reader.loaded_classes_revision();
        if let Some((cached_revision, hierarchy)) = &self.type_hierarchy_cache {
            if *cached_revision == revision {
                return Ok(Arc::clone(hierarchy));
            }
        }
        let hierarchy = Arc::new(
            crate::analysis::method_override::type_hierarchy_index(&self.reader)
                .map_err(crate::frontend::DexError::from)?,
        );
        self.type_hierarchy_cache = Some((revision, Arc::clone(&hierarchy)));
        Ok(hierarchy)
    }

    fn kotlin_source_abi(&mut self) -> Result<Arc<KotlinSourceAbi>, DecompileError> {
        let revision = self.reader.loaded_classes_revision();
        if let Some((cached_revision, source_abi)) = &self.kotlin_source_abi_cache {
            if *cached_revision == revision {
                return Ok(Arc::clone(source_abi));
            }
        }
        let mut attempted = std::collections::BTreeSet::new();
        loop {
            let source_abi = Arc::new(KotlinSourceAbi::analyze(
                self.reader.classes(),
                &self.kotlin_contract_roots,
                |class, method_index| {
                    let dex_index = self.reader.get_dex_index(class.type_descriptor())?;
                    self.reader
                        .get_method(dex_index, method_index)?
                        .to_string()
                        .parse()
                        .ok()
                },
                |class, field_index| {
                    let dex_index = self.reader.get_dex_index(class.type_descriptor())?;
                    self.reader
                        .get_field(dex_index, field_index)?
                        .to_string()
                        .parse()
                        .ok()
                },
            ));
            let dependencies = source_abi
                .analysis_dependencies()
                .map(ArgType::to_descriptor)
                .filter(|owner| attempted.insert(owner.clone()))
                .collect::<Vec<_>>();
            let before = self.reader.loaded_classes_revision();
            for owner in dependencies {
                self.reader.load_class(&owner)?;
            }
            if self.reader.loaded_classes_revision() == before {
                let revision = self.reader.loaded_classes_revision();
                self.kotlin_source_abi_cache = Some((revision, Arc::clone(&source_abi)));
                return Ok(source_abi);
            }
        }
    }

    fn prepare_java_source_abi(&mut self) -> Result<(), DecompileError> {
        let revision = self.reader.loaded_classes_revision();
        if let Some((cached_revision, source_abi)) = &self.java_source_abi_cache {
            if *cached_revision == revision {
                return Ok(());
            }
        }
        let candidates = self
            .reader
            .classes()
            .filter(|class| FunctionObjectClass::analyze(class))
            .filter_map(|class| {
                let method = class.methods().iter().find(|method| {
                    !method.is_constructor() && !method.is_class_init() && !method.is_static()
                })?;
                method.code()?;
                Some((class.type_descriptor().to_string(), method.clone()))
            })
            .collect::<Vec<_>>();
        let mut methods = Vec::with_capacity(candidates.len());
        for (owner, method) in candidates {
            methods.push(self.decode_class_method(&owner, method));
        }
        let hierarchy = self.type_hierarchy()?;
        let signatures = SourceSignatureInference::analyze(hierarchy.as_ref(), &methods, &[]);
        let source_abi = Arc::new(JavaSourceAbi::analyze(self.reader.classes(), |method| {
            (
                signatures.body_parameter_types(method),
                signatures.return_type(method),
            )
        }));
        let revision = self.reader.loaded_classes_revision();
        self.java_source_abi_cache = Some((revision, Arc::clone(&source_abi)));
        Ok(())
    }

    fn java_source_abi(&mut self) -> Arc<JavaSourceAbi> {
        let revision = self.reader.loaded_classes_revision();
        if let Some((cached_revision, source_abi)) = &self.java_source_abi_cache {
            if *cached_revision == revision {
                return Arc::clone(source_abi);
            }
        }
        let source_abi = Arc::new(JavaSourceAbi::analyze(self.reader.classes(), |_| {
            (Vec::new(), None)
        }));
        self.java_source_abi_cache = Some((revision, Arc::clone(&source_abi)));
        source_abi
    }

    /// Decode method code directly
    pub fn decode_method_code(code: &MethodCode) -> DexResult<CFG> {
        let decoder = MethodDecoder::from_code(code);
        let result = decoder.decode();

        let mut cfg = Splitter::new("method")
            .instructions(result.insns)
            .handlers(result.handlers)
            .registers(result.registers)
            .ins(result.ins)
            .build();
        cfg.debug_info = code.debug_info.clone();

        Ok(cfg)
    }

    /// Decompile a method to Kotlin source with custom structured codegen config.
    ///
    /// This is retained as a focused method-level debugging entry point. The main
    /// Kotlin source output path is class-level `decompile_class`.
    pub fn decompile_method_with_config(
        &mut self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
        config: &KotlinDecompilerConfig,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_method_with_config_and_observer(
            class_name,
            method_name,
            descriptor,
            config,
            Arc::new(crate::ir::NullAnalysisObserver),
        )
    }

    /// Decompile one method with the same class and source-ABI context as the
    /// production path while exposing structured analysis events.
    pub fn decompile_method_with_config_and_observer(
        &mut self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
        config: &KotlinDecompilerConfig,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_method_with_backend::<KotlinSourceBackend>(
            class_name,
            method_name,
            descriptor,
            config,
            observer,
        )
    }

    pub fn decompile_java_method_with_config(
        &mut self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
        config: &JavaDecompilerConfig,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_java_method_with_config_and_observer(
            class_name,
            method_name,
            descriptor,
            config,
            Arc::new(crate::ir::NullAnalysisObserver),
        )
    }

    pub fn decompile_java_method_with_config_and_observer(
        &mut self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
        config: &JavaDecompilerConfig,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_method_with_backend::<JavaSourceBackend>(
            class_name,
            method_name,
            descriptor,
            config,
            observer,
        )
    }

    fn decompile_method_with_backend<B: SourceBackend>(
        &mut self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
        config: &B::Config,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<Option<String>, DecompileError> {
        self.reader.ensure_override_analysis()?;
        let (class_node, method_node) = {
            let class = match self.reader.get_class(class_name) {
                Some(class) => class,
                None => return Ok(None),
            };
            let method = match class.methods().iter().find(|m| {
                if m.info.name != method_name {
                    return false;
                }
                if let Some(desc) = descriptor {
                    m.info.descriptor() == normalize_descriptor(desc)
                } else {
                    true
                }
            }) {
                Some(method) => method,
                None => return Ok(None),
            };
            (class.clone(), method.clone())
        };

        // First decode the method if not already done
        self.decode_method(class_name, method_name, descriptor)?;

        // Form cache key
        let cache_key = if let Some(desc) = descriptor {
            format!("{}{}", method_name, desc)
        } else {
            method_name.to_string()
        };

        // Get the decoded IR (need mutable for structuring)
        let mut ir = match self
            .method_irs
            .get_mut(class_name)
            .and_then(|methods| methods.remove(&cache_key))
        {
            Some(ir) => ir,
            None => return Ok(None),
        };

        let mut source_dependencies = SourceAbiClosure::from_cfgs(std::iter::once(&ir));
        source_dependencies.include_class(&class_node);
        source_dependencies.load(&mut self.reader, observer.as_ref())?;
        self.set_kotlin_contract_roots(contract_roots(std::iter::once(&ir)));
        let termination = self.method_termination(vec![ir.clone()], observer.as_ref())?;
        termination.apply(&mut ir);
        self.prepare_source_backend::<B>()?;
        let hierarchy = self.type_hierarchy()?;
        let output = B::generate_method(
            self,
            config,
            observer,
            hierarchy,
            &class_node,
            &method_node,
            &mut ir,
        )?;

        Ok(Some(output))
    }

    /// Decompile a single method to Kotlin source.
    ///
    /// This is a high-level method that handles all steps:
    /// 1. Loads the class if not already loaded
    /// 2. Decodes the method bytecode to IR
    /// 3. Resolves symbol references
    /// 4. Structures the control flow
    /// 5. Generates readable Kotlin method code
    pub fn decompile_method(
        &mut self,
        class_name: &str,
        method_name: &str,
        descriptor: Option<&str>,
    ) -> Result<Option<String>, DecompileError> {
        // Load class if needed
        if self.reader.get_class(class_name).is_none() {
            self.load_class(class_name)?;
        }

        self.decompile_method_with_config(
            class_name,
            method_name,
            descriptor,
            &KotlinDecompilerConfig::default(),
        )
    }

    /// Decompile a class to typed Kotlin source.
    pub fn decompile_class(&mut self, class_name: &str) -> Result<Option<String>, DecompileError> {
        self.decompile_class_with_config(class_name, &KotlinDecompilerConfig::default())
    }

    /// Decompile a class to typed Kotlin source with backend configuration.
    pub fn decompile_class_with_config(
        &mut self,
        class_name: &str,
        config: &KotlinDecompilerConfig,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_class_with_inner(class_name, config, true)
    }

    /// Decompile `class_name` together with any nested inner classes,
    /// rendering them as a single source file. When `include_inner` is `false`,
    /// only the explicitly requested class is rendered.
    pub fn decompile_class_with_inner(
        &mut self,
        class_name: &str,
        config: &KotlinDecompilerConfig,
        include_inner: bool,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_class_observed(
            class_name,
            config,
            include_inner,
            Arc::new(crate::ir::NullAnalysisObserver),
        )
    }

    pub(super) fn decompile_class_observed(
        &mut self,
        class_name: &str,
        config: &KotlinDecompilerConfig,
        include_inner: bool,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<Option<String>, DecompileError> {
        crate::profile_scope!("api.decompile_class", {
            self.decompile_class_with_backend::<KotlinSourceBackend>(
                class_name,
                config,
                include_inner,
                observer,
            )
        })
    }

    pub fn decompile_java_class_with_inner(
        &mut self,
        class_name: &str,
        config: &JavaDecompilerConfig,
        include_inner: bool,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_java_class_observed(
            class_name,
            config,
            include_inner,
            Arc::new(crate::ir::NullAnalysisObserver),
        )
    }

    pub(super) fn decompile_java_class_observed(
        &mut self,
        class_name: &str,
        config: &JavaDecompilerConfig,
        include_inner: bool,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<Option<String>, DecompileError> {
        self.decompile_class_with_backend::<JavaSourceBackend>(
            class_name,
            config,
            include_inner,
            observer,
        )
    }

    fn decompile_class_with_backend<B: SourceBackend>(
        &mut self,
        class_name: &str,
        config: &B::Config,
        include_inner: bool,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<Option<String>, DecompileError> {
        observer.checkpoint()?;
        // Load class if needed
        crate::profile_scope!("api.load_class", {
            if self.reader.get_class(class_name).is_none() {
                self.reader.load_class(class_name)?;
            }
            Ok::<(), DecompileError>(())
        })?;
        observer.checkpoint()?;

        // Collect class metadata and methods before mutating the decode cache.
        let Some((mut class_node, methods)): Option<(ClassNode, Vec<crate::frontend::MethodNode>)> =
            crate::profile_scope!("api.collect_class_methods", {
                let class = match self.reader.get_class(class_name) {
                    Some(c) => c,
                    None => return None,
                };
                let methods = class
                    .methods()
                    .iter()
                    .filter(|m| m.code().is_some())
                    .cloned()
                    .collect();
                Some((class.clone(), methods))
            })
        else {
            return Ok(None);
        };
        observer.checkpoint()?;

        let mut method_models = crate::profile_scope!("api.decode_methods", {
            let mut method_models = Vec::new();
            for method in methods {
                observer.checkpoint()?;
                method_models.push(self.decode_class_method(class_name, method));
            }
            Ok::<_, DecompileError>(method_models)
        })?;
        observer.checkpoint()?;

        // Discover and decompile inner classes nested under this one using
        // frontend metadata recovered from Dalvik inner/enclosing annotations.
        let mut inner: Vec<NestedClassInput> = Vec::new();
        if include_inner {
            inner = crate::profile_scope!("api.collect_nested_class_inputs", {
                self.collect_nested_class_inputs(&class_node)
            })?;
            // Order inner classes deterministically: named classes before
            // anonymous, then by descriptor.
            crate::profile_scope!("api.sort_nested_inputs", sort_nested_inputs(&mut inner));
        }
        observer.checkpoint()?;

        sort_nested_input_tree(&mut inner);
        crate::profile_scope!("api.source_dependencies", {
            let source_dependencies = crate::profile_scope!("api.source_dependencies.collect", {
                let mut source_dependencies = SourceAbiClosure::from_cfgs(
                    method_models.iter().filter_map(|method| method.cfg()),
                );
                source_dependencies.include_class(&class_node);
                source_dependencies.include_nested(&inner);
                source_dependencies
            });
            crate::profile_scope!(
                "api.source_dependencies.load",
                source_dependencies.load(&mut self.reader, observer.as_ref())
            )?;
            crate::profile_scope!(
                "api.source_dependencies.overrides",
                self.reader.ensure_override_analysis()
            )?;
            Ok::<(), DecompileError>(())
        })?;
        observer.checkpoint()?;
        let mut termination_roots = method_models
            .iter()
            .filter_map(|method| method.cfg().cloned())
            .collect::<Vec<_>>();
        collect_nested_cfgs(&inner, &mut termination_roots);
        self.set_kotlin_contract_roots(contract_roots(termination_roots.iter()));
        let termination = crate::profile_scope!("api.method_termination", {
            self.method_termination(termination_roots, observer.as_ref())
        })?;
        for method in &mut method_models {
            if let Some(cfg) = method.cfg_mut() {
                termination.apply(cfg);
            }
        }
        apply_nested_termination(&termination, &mut inner);
        self.prepare_source_backend::<B>()?;
        observer.checkpoint()?;
        if let Some(current) = self.reader.get_class(class_name) {
            class_node = current.clone();
        }
        Self::refresh_method_nodes(&self.reader, class_name, &mut method_models);
        Self::refresh_nested_class_nodes(&self.reader, &mut inner);
        let hierarchy =
            crate::profile_scope!("api.source_context.hierarchy", { self.type_hierarchy() })?;
        observer.checkpoint()?;
        let source = B::generate_class(
            self,
            config,
            observer,
            hierarchy,
            &class_node,
            &mut method_models,
            inner,
        )?;
        Ok(Some(source))
    }

    /// Recovers exact calls that cannot complete normally without decoding the
    /// entire archive. The reachable call graph is closed transitively from
    /// the current source unit, then solved as one interprocedural fixed point.
    fn method_termination(
        &mut self,
        roots: Vec<CFG>,
        observer: &dyn crate::ir::AnalysisObserver,
    ) -> Result<crate::ir::analysis::MethodTermination, DecompileError> {
        let mut methods = roots
            .into_iter()
            .map(|cfg| (cfg_method_reference(&cfg), cfg))
            .collect::<std::collections::BTreeMap<_, _>>();
        let mut pending = methods
            .values()
            .flat_map(exact_call_targets)
            .collect::<std::collections::BTreeSet<_>>();
        let mut visited = std::collections::BTreeSet::new();

        while let Some(target) = pending.pop_first() {
            observer.checkpoint()?;
            if methods.contains_key(&target) || !visited.insert(target.clone()) {
                continue;
            }
            let owner = target.owner.to_descriptor();
            if self.reader.load_class(&owner).is_err() {
                continue;
            }
            let Some(class) = self.reader.get_class(&owner) else {
                continue;
            };
            let descriptor = target.descriptor.to_string();
            let available = class.methods().iter().any(|method| {
                method.name() == target.name
                    && method.info.descriptor() == descriptor
                    && method.code().is_some()
            });
            if !available {
                continue;
            }
            if self
                .decode_method(&owner, &target.name, Some(&descriptor))
                .is_err()
            {
                continue;
            }
            let key = format!("{}{}", target.name, descriptor);
            let Some(cfg) = self
                .method_irs
                .get(&owner)
                .and_then(|class| class.get(&key))
                .cloned()
            else {
                continue;
            };
            pending.extend(exact_call_targets(&cfg).filter(|callee| !methods.contains_key(callee)));
            methods.insert(target, cfg);
        }

        Ok(crate::ir::analysis::MethodTermination::analyze(
            methods.values(),
        ))
    }

    fn prepare_source_backend<B: SourceBackend>(&mut self) -> Result<(), DecompileError> {
        loop {
            let revision = self.reader.loaded_classes_revision();
            self.reader.ensure_override_analysis()?;
            B::prepare_context(self)?;
            if self.reader.loaded_classes_revision() == revision {
                return Ok(());
            }
        }
    }

    fn set_kotlin_contract_roots(&mut self, roots: std::collections::BTreeSet<MethodReference>) {
        if self.kotlin_contract_roots != roots {
            self.kotlin_contract_roots = roots;
            self.kotlin_source_abi_cache = None;
        }
    }

    fn refresh_nested_class_nodes(reader: &DexFileReader, inputs: &mut [NestedClassInput]) {
        let mut pending = inputs.iter_mut().collect::<Vec<_>>();
        while let Some(input) = pending.pop() {
            let descriptor = input.class.type_descriptor().to_string();
            Self::refresh_method_nodes(reader, &descriptor, &mut input.methods);
            if let Some(current) = reader.get_class(&descriptor) {
                input.class = current.clone();
            }
            pending.extend(input.nested.iter_mut());
        }
    }

    fn refresh_method_nodes(
        reader: &DexFileReader,
        class_name: &str,
        methods: &mut [ClassMethodInput],
    ) {
        let Some(class) = reader.get_class(class_name) else {
            return;
        };
        for input in methods {
            let method = input.method_mut();
            let descriptor = method.info.descriptor();
            if let Some(current) = class.methods().iter().find(|current| {
                current.info.name == method.info.name && current.info.descriptor() == descriptor
            }) {
                *method = current.clone();
            }
        }
    }

    fn load_inner_class(&mut self, class_name: &str) -> Result<(), DecompileError> {
        if self.reader.get_class(class_name).is_none() {
            self.reader.load_class(class_name)?;
        }
        Ok(())
    }

    fn decode_class_method(
        &mut self,
        class_name: &str,
        method: crate::frontend::MethodNode,
    ) -> ClassMethodInput {
        let method_name = method.info.name.clone();
        let descriptor = method.info.descriptor();
        if let Err(error) = self.decode_method(class_name, &method_name, Some(&descriptor)) {
            return ClassMethodInput::failed(
                method,
                MethodRecoveryFailure::new(MethodRecoveryStage::Decode, error),
            );
        }
        let cache_key = format!("{}{}", method_name, descriptor);
        match self
            .method_irs
            .get_mut(class_name)
            .and_then(|class_cache| class_cache.remove(&cache_key))
        {
            Some(cfg) => ClassMethodInput::decoded(method, cfg),
            None => ClassMethodInput::failed(
                method,
                MethodRecoveryFailure::new(
                    MethodRecoveryStage::Decode,
                    "decoded CFG is unavailable",
                ),
            ),
        }
    }

    fn collect_class_input(
        &mut self,
        class_name: &str,
    ) -> Result<NestedClassInput, DecompileError> {
        let class = self.reader.get_class(class_name).cloned().ok_or_else(|| {
            DecompileError::from(KotlinDecompilerError::MissingNestedClass(
                class_name.to_string(),
            ))
        })?;
        let mut methods = Vec::new();
        for method in class
            .methods()
            .iter()
            .filter(|method| method.code().is_some())
            .cloned()
        {
            methods.push(self.decode_class_method(class_name, method));
        }
        Ok(NestedClassInput {
            class,
            methods,
            nested: Vec::new(),
        })
    }

    fn collect_nested_class_inputs(
        &mut self,
        outer: &ClassNode,
    ) -> Result<Vec<NestedClassInput>, DecompileError> {
        let root_names = outer
            .inner_class_names()
            .iter()
            .map(|name| (*name).to_string())
            .collect::<Vec<_>>();
        let root_count = root_names.len();
        let mut seen = std::collections::BTreeSet::from([outer.type_descriptor().to_string()]);
        let mut pending = root_names
            .into_iter()
            .rev()
            .map(NestedInputTask::Load)
            .collect::<Vec<_>>();
        let mut results = Vec::<NestedClassInput>::new();

        while let Some(task) = pending.pop() {
            match task {
                NestedInputTask::Load(class_name) => {
                    if !seen.insert(class_name.clone()) {
                        return Err(DecompileError::from(
                            KotlinDecompilerError::NestedClassCycle(class_name),
                        ));
                    }
                    self.load_inner_class(&class_name)?;
                    let class_node =
                        self.reader.get_class(&class_name).cloned().ok_or_else(|| {
                            DecompileError::from(KotlinDecompilerError::MissingNestedClass(
                                class_name.clone(),
                            ))
                        })?;
                    let mut methods = Vec::new();
                    for method in class_node
                        .methods()
                        .iter()
                        .filter(|method| method.code().is_some())
                        .cloned()
                    {
                        methods.push(self.decode_class_method(&class_name, method));
                    }
                    let child_names = class_node
                        .inner_class_names()
                        .iter()
                        .map(|name| (*name).to_string())
                        .collect::<Vec<_>>();
                    let child_count = child_names.len();
                    pending.push(NestedInputTask::Finish {
                        class: class_node,
                        methods,
                        child_count,
                    });
                    pending.extend(child_names.into_iter().rev().map(NestedInputTask::Load));
                }
                NestedInputTask::Finish {
                    class,
                    methods,
                    child_count,
                } => {
                    let start = results.len().checked_sub(child_count).ok_or_else(|| {
                        DecompileError::from(KotlinDecompilerError::MalformedNestedClassStack {
                            expected: child_count,
                            actual: results.len(),
                        })
                    })?;
                    let mut nested = results.drain(start..).collect::<Vec<_>>();
                    sort_nested_inputs(&mut nested);
                    results.push(NestedClassInput {
                        class,
                        methods,
                        nested,
                    });
                }
            }
        }

        if results.len() != root_count {
            return Err(DecompileError::from(
                KotlinDecompilerError::MalformedNestedClassStack {
                    expected: root_count,
                    actual: results.len(),
                },
            ));
        }
        let mut nested = results;
        sort_nested_inputs(&mut nested);
        Ok(nested)
    }
}

fn cfg_method_reference(cfg: &CFG) -> MethodReference {
    MethodReference {
        owner: cfg.method().owner().clone(),
        name: cfg.method().name().to_string(),
        descriptor: cfg.method().descriptor().clone(),
    }
}

fn exact_call_targets(cfg: &CFG) -> impl Iterator<Item = MethodReference> + '_ {
    cfg.blocks
        .values()
        .flat_map(|block| &block.insns)
        .filter(|instruction| {
            instruction.insn_type == InsnType::Invoke
                && matches!(
                    instruction.payload.invoke_type,
                    Some(InvokeType::Static | InvokeType::Direct | InvokeType::Super)
                )
        })
        .filter_map(|instruction| match instruction.payload.reference.as_ref() {
            Some(MemberReference::Method(method)) => Some(method.clone()),
            _ => None,
        })
}

fn contract_roots<'a>(
    cfgs: impl IntoIterator<Item = &'a CFG>,
) -> std::collections::BTreeSet<MethodReference> {
    let mut roots = std::collections::BTreeSet::new();
    for cfg in cfgs {
        roots.insert(cfg_method_reference(cfg));
        roots.extend(
            cfg.blocks
                .values()
                .flat_map(|block| &block.insns)
                .filter_map(|instruction| match instruction.payload.reference.as_ref() {
                    Some(MemberReference::Method(method)) => Some(method.clone()),
                    _ => None,
                }),
        );
    }
    roots
}

fn collect_nested_cfgs(inputs: &[NestedClassInput], output: &mut Vec<CFG>) {
    for input in inputs {
        output.extend(
            input
                .methods
                .iter()
                .filter_map(|method| method.cfg().cloned()),
        );
        collect_nested_cfgs(&input.nested, output);
    }
}

fn apply_nested_termination(
    termination: &crate::ir::analysis::MethodTermination,
    inputs: &mut [NestedClassInput],
) {
    for input in inputs {
        for method in &mut input.methods {
            if let Some(cfg) = method.cfg_mut() {
                termination.apply(cfg);
            }
        }
        apply_nested_termination(termination, &mut input.nested);
    }
}

#[derive(Default)]
struct SourceAbiClosure {
    pending: std::collections::BTreeSet<String>,
}

impl SourceAbiClosure {
    fn from_cfgs<'a>(cfgs: impl IntoIterator<Item = &'a CFG>) -> Self {
        let mut closure = Self::default();
        closure.include_cfgs(cfgs);
        closure
    }

    fn include_cfgs<'a>(&mut self, cfgs: impl IntoIterator<Item = &'a CFG>) {
        for reference in cfgs
            .into_iter()
            .flat_map(|cfg| cfg.blocks.values())
            .flat_map(|block| &block.insns)
            .filter_map(|instruction| instruction.payload.reference.as_ref())
        {
            match reference {
                MemberReference::Field(field) => {
                    self.include_type(&field.owner);
                    self.include_type(&field.field_type);
                }
                MemberReference::Method(method) => {
                    self.include_type(&method.owner);
                    for parameter in &method.descriptor.parameters {
                        self.include_type(parameter);
                    }
                    self.include_type(&method.descriptor.return_type);
                }
            }
        }
    }

    fn include_type(&mut self, ty: &ArgType) {
        match ty {
            ArgType::Object(_) => {
                self.pending.insert(ty.to_descriptor());
            }
            ArgType::Array(element) => self.include_type(element),
            ArgType::Primitive(_) | ArgType::Unknown(_) => {}
        }
    }

    fn include_class(&mut self, class: &ClassNode) {
        self.include_type(class.class_type());
        self.include_hierarchy(class);
        self.include_annotations(&class.annotations);
        for field in class.fields() {
            self.include_type(field.field_type());
            self.include_annotations(&field.annotations);
        }
        for method in class.methods() {
            for parameter in method.param_types() {
                self.include_type(parameter);
            }
            self.include_type(method.return_type());
            self.include_annotations(&method.annotations);
            for annotations in &method.parameter_annotations {
                self.include_annotations(annotations);
            }
        }
    }

    fn include_hierarchy(&mut self, class: &ClassNode) {
        if let Some(super_class) = &class.super_class {
            self.include_type(super_class);
        }
        for interface in &class.interfaces {
            self.include_type(interface);
        }
    }

    fn include_annotations(&mut self, annotations: &[crate::frontend::AnnotationNode]) {
        for annotation in annotations {
            self.include_type(&annotation.annotation_type);
            for element in &annotation.elements {
                self.include_annotation_value(&element.value);
            }
        }
    }

    fn include_annotation_value(&mut self, value: &crate::frontend::DexValue) {
        use crate::frontend::DexValue;
        match value {
            DexValue::Type(ty) => self.include_type(ty),
            DexValue::Field(field) | DexValue::Enum(field) => {
                self.include_type(&field.owner);
                self.include_type(&field.field_type);
            }
            DexValue::Method(method) => {
                self.include_type(&method.owner);
                for parameter in &method.descriptor.parameters {
                    self.include_type(parameter);
                }
                self.include_type(&method.descriptor.return_type);
            }
            DexValue::MethodType(descriptor) => {
                for parameter in &descriptor.parameters {
                    self.include_type(parameter);
                }
                self.include_type(&descriptor.return_type);
            }
            DexValue::Array(values) => {
                for value in values {
                    self.include_annotation_value(value);
                }
            }
            DexValue::Annotation(annotation) => {
                self.include_annotations(std::slice::from_ref(annotation));
            }
            DexValue::Null
            | DexValue::Boolean(_)
            | DexValue::Byte(_)
            | DexValue::Short(_)
            | DexValue::Char(_)
            | DexValue::Int(_)
            | DexValue::Long(_)
            | DexValue::Float(_)
            | DexValue::Double(_)
            | DexValue::String(_)
            | DexValue::Unsupported { .. } => {}
        }
    }

    fn include_nested(&mut self, inputs: &[NestedClassInput]) {
        let mut pending = inputs.iter().collect::<Vec<_>>();
        while let Some(input) = pending.pop() {
            self.include_class(&input.class);
            self.include_cfgs(input.methods.iter().filter_map(|method| method.cfg()));
            pending.extend(&input.nested);
        }
    }

    fn load(
        mut self,
        reader: &mut DexFileReader,
        observer: &dyn crate::ir::AnalysisObserver,
    ) -> Result<(), DecompileError> {
        let mut visited = std::collections::BTreeSet::new();
        while let Some(owner) = self.pending.pop_first() {
            observer.checkpoint()?;
            if !visited.insert(owner.clone()) {
                continue;
            }
            reader.load_class(&owner)?;
            let Some(class) = reader.get_class(&owner) else {
                continue;
            };
            self.include_hierarchy(class);
        }
        Ok(())
    }
}

enum NestedInputTask {
    Load(String),
    Finish {
        class: ClassNode,
        methods: Vec<ClassMethodInput>,
        child_count: usize,
    },
}

fn sort_nested_inputs(inputs: &mut [NestedClassInput]) {
    inputs.sort_by_key(|input| {
        let descriptor = input.class.type_descriptor().to_string();
        (input.class.is_anonymous(), descriptor)
    });
}

fn sort_nested_input_tree(inputs: &mut [NestedClassInput]) {
    sort_nested_inputs(inputs);
    for input in inputs {
        sort_nested_input_tree(&mut input.nested);
    }
}

fn normalize_descriptor(descriptor: &str) -> String {
    descriptor
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

fn normalize_invoke_args(insn: &mut InsnNode, method: &MethodReference) -> DexResult<()> {
    if insn.insn_type != InsnType::Invoke {
        return Ok(());
    }

    let types = invoke_arg_types(insn.payload.invoke_type, method);
    if types.is_empty() && insn.args.is_empty() {
        return Ok(());
    }

    let slot_count: usize = types.iter().map(type_slots).sum();
    if insn.args.len() == types.len() {
        for (arg, ty) in insn.args.iter_mut().zip(types) {
            set_arg_type(arg, ty);
        }
        return Ok(());
    }
    if insn.args.len() != slot_count {
        return Err(crate::frontend::DexError::InvalidInvokeRegisters {
            offset: insn.offset,
            expected: slot_count,
            actual: insn.args.len(),
        });
    }

    let raw_args = std::mem::take(&mut insn.args);
    let mut logical_args = Vec::with_capacity(types.len());
    let mut cursor = 0;
    for ty in types {
        let mut arg = raw_args.get(cursor).cloned().ok_or(
            crate::frontend::DexError::InvalidInvokeRegisters {
                offset: insn.offset,
                expected: slot_count,
                actual: raw_args.len(),
            },
        )?;
        let width = type_slots(&ty);
        set_arg_type(&mut arg, ty);
        logical_args.push(arg);
        cursor += width;
    }

    insn.args = logical_args;
    Ok(())
}

fn invoke_arg_types(invoke_type: Option<InvokeType>, method: &MethodReference) -> Vec<ArgType> {
    let mut types = Vec::new();

    if !matches!(invoke_type, Some(InvokeType::Static)) {
        types.push(method.owner.clone());
    }

    types.extend(method.descriptor.parameters.iter().cloned());
    types
}

fn apply_invoke_return_type(insn: &mut InsnNode, method: &MethodReference) {
    if insn.insn_type != InsnType::Invoke {
        return;
    }

    let return_type = method.descriptor.return_type.clone();
    if return_type == ArgType::VOID {
        return;
    }
    if let Some(result) = insn.result.as_mut() {
        result.ty = return_type;
    }
}

fn type_slots(ty: &ArgType) -> usize {
    if ty.is_wide() {
        2
    } else {
        1
    }
}

fn set_arg_type(arg: &mut InsnArg, ty: ArgType) {
    match arg {
        InsnArg::Reg(reg) => reg.ty = ty,
        InsnArg::Lit(lit) => lit.ty = ty,
        InsnArg::Wrapped(insn) => {
            if let Some(result) = std::sync::Arc::make_mut(insn).result.as_mut() {
                result.ty = ty;
            }
        }
    }
}

fn apply_field_type(insn: &mut InsnNode, field: &FieldReference) {
    let ty = field.field_type.clone();
    match insn.insn_type {
        InsnType::Iget | InsnType::Sget => {
            if let Some(result) = insn.result.as_mut() {
                result.ty = ty;
            }
        }
        InsnType::Iput | InsnType::Sput => {
            if let Some(arg) = insn.args.first_mut() {
                set_arg_type(arg, ty);
            }
        }
        _ => {}
    }
}

// ==================== Error Types ====================

/// Errors that can occur during decompilation
#[derive(Debug)]
#[non_exhaustive]
pub enum DecompileError {
    /// The caller superseded this analysis request.
    Cancelled(crate::ir::AnalysisCancelled),
    /// DEX file operation failed
    DexError(crate::frontend::DexError),
    /// Java semantic recovery or source generation failed.
    Java(JavaDecompilerError),
    /// Kotlin semantic recovery or source generation failed.
    Kotlin(KotlinDecompilerError),
    /// A requested class is not present in the input.
    ClassNotFound(String),
    /// A requested method is not present in its declaring class.
    MethodNotFound {
        class: String,
        method: String,
        descriptor: Option<String>,
    },
    /// A method name identifies more than one overload and needs a descriptor.
    AmbiguousMethod {
        class: String,
        method: String,
        descriptors: Vec<String>,
    },
}

impl std::fmt::Display for DecompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cancelled(error) => error.fmt(f),
            Self::DexError(e) => write!(f, "DEX error: {}", e),
            Self::Java(e) => write!(f, "Java generation failed: {e}"),
            Self::Kotlin(e) => write!(f, "Kotlin generation failed: {e}"),
            Self::ClassNotFound(class) => write!(f, "class not found: {class}"),
            Self::MethodNotFound {
                class,
                method,
                descriptor,
            } => {
                write!(f, "method not found: {class}->{method}")?;
                if let Some(descriptor) = descriptor {
                    write!(f, "{descriptor}")?;
                }
                Ok(())
            }
            Self::AmbiguousMethod {
                class,
                method,
                descriptors,
            } => write!(
                f,
                "method {class}->{method} is overloaded; choose one of {}",
                descriptors.join(", ")
            ),
        }
    }
}

impl std::error::Error for DecompileError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Cancelled(source) => Some(source),
            Self::DexError(source) => Some(source),
            Self::Java(source) => Some(source),
            Self::Kotlin(source) => Some(source),
            Self::ClassNotFound(_) | Self::MethodNotFound { .. } | Self::AmbiguousMethod { .. } => {
                None
            }
        }
    }
}

impl From<crate::frontend::DexError> for DecompileError {
    fn from(e: crate::frontend::DexError) -> Self {
        Self::DexError(e)
    }
}

impl From<crate::ir::AnalysisCancelled> for DecompileError {
    fn from(error: crate::ir::AnalysisCancelled) -> Self {
        Self::Cancelled(error)
    }
}

impl From<KotlinDecompilerError> for DecompileError {
    fn from(e: KotlinDecompilerError) -> Self {
        Self::Kotlin(e)
    }
}

impl From<JavaDecompilerError> for DecompileError {
    fn from(e: JavaDecompilerError) -> Self {
        Self::Java(e)
    }
}

/// Result of decoding a method
#[derive(Debug)]
pub struct DecodedMethod {
    /// Method name
    pub name: String,
    /// Declaring class
    pub declaring_class: String,
    /// Method IR
    pub ir: CFG,
}

impl DecodedMethod {
    /// Create a new decoded method
    pub fn new(name: String, declaring_class: String, ir: CFG) -> Self {
        Self {
            name,
            declaring_class,
            ir,
        }
    }

    /// Get number of basic blocks
    pub fn block_count(&self) -> usize {
        self.ir.blocks.len()
    }

    /// Get number of instructions
    pub fn insn_count(&self) -> usize {
        self.ir.blocks.values().map(|b| b.insns.len()).sum()
    }
}

// ==================== Convenience Functions ====================

/// Load a DEX file and return the decompiler context
pub fn load_dex<P: AsRef<Path>>(path: P) -> DexResult<DecompilerContext> {
    DecompilerContext::from_file(path)
}

/// Decode a single method code into IR
pub fn decode_method(code: &MethodCode) -> DexResult<CFG> {
    DecompilerContext::decode_method_code(code)
}

// ==================== Tests ====================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{AccessInfo, ClassInfo, FieldInfo, FieldNode, MethodCode};

    #[test]
    fn test_decode_simple_method() {
        // Simple method: const/4 v0, 0; return v0
        let code = MethodCode {
            registers_size: 1,
            ins_size: 0,
            outs_size: 0,
            insns: vec![
                0x0012, // const/4 v0, #int 0
                0x000f, // return v0
            ],
            tries: Vec::new(),
            debug_info: None,
        };

        let ir = decode_method(&code).expect("Should decode");

        assert_eq!(ir.blocks.len(), 1);
        let block = ir.entry_block().expect("Should have entry block");
        assert_eq!(block.insns.len(), 2);
    }

    #[test]
    fn test_decode_with_branch() {
        // Method with branch:
        // if-eqz v0, :target
        // const/4 v0, 1
        // :target
        // return v0
        let code = MethodCode {
            registers_size: 1,
            ins_size: 1,
            outs_size: 0,
            insns: vec![
                0x0038, // if-eqz v0, +2 (opcode: 0x38, reg: v0)
                0x0002, // offset: +2
                0x1012, // const/4 v0, #int 1
                0x000f, // return v0
            ],
            tries: Vec::new(),
            debug_info: None,
        };

        let ir = decode_method(&code).expect("Should decode");

        // Should have multiple blocks due to branch
        assert!(ir.blocks.len() >= 2);
    }

    #[test]
    fn test_invoke_arg_normalization_drops_wide_high_slot() {
        let mut insn = InsnNode::invoke(
            InvokeType::Static,
            0,
            vec![
                InsnArg::reg(6, ArgType::unknown()),
                InsnArg::reg(7, ArgType::unknown()),
            ],
        );

        let method = "Ljava/lang/Long;->valueOf(J)Ljava/lang/Long;"
            .parse()
            .unwrap();
        normalize_invoke_args(&mut insn, &method).unwrap();

        assert_eq!(insn.args.len(), 1);
        assert_eq!(insn.args[0].reg_num(), Some(6));
        assert_eq!(insn.args[0].declared_type(), Some(&ArgType::LONG));
    }

    #[test]
    fn test_invoke_result_gets_prototype_return_type() {
        let mut insn = InsnNode::invoke(InvokeType::Virtual, 0, vec![]);
        insn.set_result(crate::ir::arg::RegisterArg::new(0, ArgType::unknown()));

        let method = "LReader;->hasNext()Z".parse().unwrap();
        apply_invoke_return_type(&mut insn, &method);

        assert_eq!(insn.result.as_ref().unwrap().ty, ArgType::BOOLEAN);
    }

    #[test]
    fn dependency_hierarchy_does_not_expand_member_types() {
        let mut class = ClassNode::new(
            0,
            ClassInfo::from_type_descriptor("LDependency;").unwrap(),
            AccessInfo::for_class(0),
        );
        class.set_super_class("LParent;".parse().unwrap());
        class.add_interface("LContract;".parse().unwrap());
        class.add_field(FieldNode::new(
            0,
            FieldInfo::new(
                "LDependency;".to_string(),
                "payload".to_string(),
                "LUnrelatedPayload;".parse().unwrap(),
            ),
            AccessInfo::for_field(0),
        ));

        let mut root_closure = SourceAbiClosure::default();
        root_closure.include_class(&class);
        assert!(root_closure.pending.contains("LUnrelatedPayload;"));

        let mut dependency_closure = SourceAbiClosure::default();
        dependency_closure.include_hierarchy(&class);
        assert!(dependency_closure.pending.contains("LParent;"));
        assert!(dependency_closure.pending.contains("LContract;"));
        assert!(!dependency_closure.pending.contains("LUnrelatedPayload;"));
    }
}
