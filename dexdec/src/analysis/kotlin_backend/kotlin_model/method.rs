use crate::frontend::{AccessInfo, AnnotationNode, ClassNode, MethodNode};
use crate::ir::{ty::ArgType, CFG};
use crate::language::kotlin::{
    AggregateInitializer, DefiniteAssignment, KotlinAstNormalizer, KotlinAstTransform,
    KotlinIdentifier, KotlinInitializerExitLowering, KotlinLowerer, KotlinModifier, KotlinType,
    LexicalDeclarationPlacement,
};

use super::super::method_pipeline::MethodBodyAnalysis;
use super::super::type_names::KotlinTypeNameResolver;
use super::super::KotlinDecompilerError;
use super::class::declaration_name;
use super::source_abi::{
    EnclosingInstanceAbi, FunctionObjectClass, OuterInstanceField, SyntheticConstructorBridge,
};
use crate::analysis::MethodRecoveryFailure;

#[derive(Debug, Clone)]
pub(in crate::analysis::kotlin_backend) struct KotlinMethodModel {
    pub declaration: KotlinMethodDeclaration,
    pub body: Option<KotlinMethodBody>,
    pub failure: Option<MethodRecoveryFailure>,
}

#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::kotlin_backend) struct KotlinMethodParameter {
    pub annotations: Vec<AnnotationNode>,
    pub ty: ArgType,
    pub name: Option<KotlinIdentifier>,
    pub hidden: bool,
    pub varargs: bool,
}

#[derive(Debug, Clone)]
pub(in crate::analysis::kotlin_backend) struct KotlinMethodBody {
    semantic: crate::ir::SemanticMethod<crate::ir::SourceSyntaxSemantics>,
    is_static: bool,
    this_code_var: Option<u32>,
    parameter_code_vars: Vec<Option<u32>>,
    type_uses: std::collections::BTreeSet<ArgType>,
    current_type: Option<ArgType>,
    return_type: Option<ArgType>,
    outer_instance: Option<crate::language::kotlin::OuterInstanceBinding>,
}

impl KotlinMethodModel {
    pub fn from_body_analysis_with_options(
        declaration: KotlinMethodDeclaration,
        analysis: MethodBodyAnalysis,
        options: MethodBodyOptions,
    ) -> Result<Self, KotlinDecompilerError> {
        let body = KotlinMethodBody::from_analysis(analysis, options);
        Ok(Self {
            declaration,
            body: Some(body),
            failure: None,
        })
    }

    pub fn from_declaration(declaration: KotlinMethodDeclaration) -> Self {
        Self {
            declaration,
            body: None,
            failure: None,
        }
    }

    pub fn from_failure(
        class: &ClassNode,
        method: &MethodNode,
        failure: MethodRecoveryFailure,
    ) -> Self {
        let mut declaration = KotlinMethodDeclaration::from_method_node_erased(class, method);
        declaration.discard_source_metadata();
        Self {
            declaration,
            body: None,
            failure: Some(failure),
        }
    }

    pub fn with_failure(mut self, failure: MethodRecoveryFailure) -> Self {
        self.declaration.discard_source_metadata();
        self.body = None;
        self.failure = Some(failure);
        self
    }

    pub fn is_default_constructor(
        &self,
        class_name: &KotlinIdentifier,
        class_modifiers: &[KotlinModifier],
        body: &crate::language::kotlin::KotlinMethodBody,
    ) -> bool {
        self.declaration.kind == KotlinMethodDeclarationKind::Constructor
            && &self.declaration.name == class_name
            && self.declaration.visible_parameters().next().is_none()
            && Self::access_modifier(&self.declaration.modifiers)
                == Self::access_modifier(class_modifiers)
            && KotlinMethodBody::is_empty(body)
    }

    fn access_modifier(modifiers: &[KotlinModifier]) -> Option<KotlinModifier> {
        modifiers.iter().copied().find(|modifier| {
            matches!(
                modifier,
                KotlinModifier::Public | KotlinModifier::Protected | KotlinModifier::Private
            )
        })
    }
}

impl KotlinMethodBody {
    pub fn from_analysis(analysis: MethodBodyAnalysis, options: MethodBodyOptions) -> Self {
        let outer_instance = options.enclosing_instance.map(|enclosing| {
            let parameter = options
                .outer_parameter
                .and_then(|index| analysis.parameter_code_vars.get(index).copied().flatten());
            crate::language::kotlin::OuterInstanceBinding::new(
                enclosing.outer_type,
                options.outer_instance.map(|outer| outer.reference),
                parameter,
            )
        });
        Self {
            semantic: analysis.semantic,
            is_static: analysis.is_static,
            this_code_var: analysis.this_code_var,
            parameter_code_vars: analysis.parameter_code_vars,
            type_uses: analysis.type_uses,
            current_type: options.current_type,
            return_type: options.return_type,
            outer_instance,
        }
    }

    pub(in crate::analysis::kotlin_backend) fn method_references(
        &self,
    ) -> std::collections::BTreeSet<crate::ir::MethodReference> {
        let mut collector = MemberReferenceCollector::default();
        crate::ir::SemanticVisitor::visit_node(&mut collector, self.semantic.body());
        collector.methods
    }

    pub(in crate::analysis::kotlin_backend) fn field_references(
        &self,
    ) -> std::collections::BTreeSet<crate::ir::FieldReference> {
        let mut collector = MemberReferenceCollector::default();
        crate::ir::SemanticVisitor::visit_node(&mut collector, self.semantic.body());
        collector.fields
    }

    pub(in crate::analysis::kotlin_backend) fn outer_instance_field(
        &self,
    ) -> Option<(&crate::ir::FieldReference, &ArgType)> {
        let binding = self.outer_instance.as_ref()?;
        Some((binding.field()?, binding.outer_type()))
    }

    pub fn lower(
        &self,
        parameter_names: &[KotlinIdentifier],
        type_names: &KotlinTypeNameResolver,
        member_names: std::sync::Arc<crate::language::kotlin::KotlinMemberNames>,
        source_field_types: std::sync::Arc<
            std::collections::BTreeMap<crate::ir::FieldReference, KotlinType>,
        >,
        generic_fields: std::sync::Arc<
            std::collections::BTreeMap<
                crate::ir::FieldReference,
                crate::ir::generic_types::GenericFieldContract,
            >,
        >,
        generic_methods: std::sync::Arc<
            std::collections::BTreeMap<
                crate::ir::MethodReference,
                crate::ir::generic_types::GenericMethodContract,
            >,
        >,
        method_nullability: std::sync::Arc<
            std::collections::BTreeMap<
                crate::ir::MethodReference,
                crate::language::kotlin::KotlinMethodNullability,
            >,
        >,
        extension_receivers: std::sync::Arc<
            std::collections::BTreeMap<crate::ir::MethodReference, usize>,
        >,
        default_calls: std::sync::Arc<
            std::collections::BTreeMap<
                crate::ir::MethodReference,
                crate::language::kotlin::KotlinDefaultCallContract,
            >,
        >,
        vararg_parameters: std::sync::Arc<
            std::collections::BTreeMap<
                crate::ir::MethodReference,
                std::collections::BTreeSet<usize>,
            >,
        >,
        platform_symbols: Option<std::sync::Arc<crate::platform_symbols::PlatformSymbolSet>>,
        non_null_fields: std::sync::Arc<std::collections::BTreeSet<crate::ir::FieldReference>>,
        singleton_types: std::sync::Arc<std::collections::BTreeSet<ArgType>>,
        singleton_instances: std::sync::Arc<std::collections::BTreeSet<crate::ir::FieldReference>>,
        source_object_types: std::sync::Arc<std::collections::BTreeMap<ArgType, KotlinType>>,
        generic_type_projection: std::sync::Arc<dyn crate::language::kotlin::GenericTypeProjection>,
        source_current_type: Option<KotlinType>,
        source_super_type: Option<KotlinType>,
        source_parameter_types: &[Option<KotlinType>],
        source_return_type: Option<KotlinType>,
        source_type_erasures: std::collections::BTreeMap<KotlinIdentifier, ArgType>,
        source_type_bounds: std::collections::BTreeMap<KotlinIdentifier, KotlinType>,
        generic_throw_types: Vec<crate::language::kotlin::KotlinSourceErasure>,
        outer_instances: std::collections::BTreeMap<crate::ir::FieldReference, KotlinType>,
        reserved_local_names: std::collections::BTreeSet<KotlinIdentifier>,
        class_initializer: bool,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<crate::language::kotlin::KotlinMethodBody, KotlinDecompilerError> {
        let (source_field_types, source_types) =
            crate::profile_scope!("kotlin_backend.method_lower.types", {
                let source_field_types = if outer_instances.is_empty() {
                    source_field_types
                } else {
                    let mut fields = source_field_types.as_ref().clone();
                    fields.extend(outer_instances.clone());
                    std::sync::Arc::new(fields)
                };
                let mut used_types = self.type_uses.clone();
                used_types.extend(self.current_type.iter().cloned());
                used_types.extend(self.return_type.iter().cloned());
                used_types.insert(ArgType::object("java/lang/Object"));
                let mut generic_uses = Vec::new();
                for contract in generic_fields.values() {
                    super::super::type_uses::GenericTypeUses::field_contract(
                        contract,
                        &mut generic_uses,
                    );
                }
                for contract in generic_methods.values() {
                    super::super::type_uses::GenericTypeUses::method_contract(
                        contract,
                        &mut generic_uses,
                    );
                }
                used_types.extend(generic_uses);
                let source_types = used_types
                    .iter()
                    .map(|ty| Ok((ty.clone(), type_names.resolve_type(ty)?)))
                    .collect::<Result<std::collections::BTreeMap<_, _>, KotlinDecompilerError>>()?;
                Ok::<_, KotlinDecompilerError>((source_field_types, source_types))
            })?;
        let semantic_names = crate::profile_scope!("kotlin_backend.method_lower.names", {
            super::super::semantic_naming::SemanticNameRecovery::new(type_names).recover(
                self.semantic.body(),
                self.semantic.state().types(),
                parameter_names,
                &self.parameter_code_vars,
                self.this_code_var,
            )
        });
        let dialect = crate::profile_scope!("kotlin_backend.method_lower.dialect", {
            crate::language::kotlin::DexKotlinDialect::new(
                self.is_static,
                self.this_code_var,
                &self.parameter_code_vars,
                parameter_names,
                self.semantic.state().types(),
                source_types,
                member_names,
            )
            .map(|dialect| {
                dialect
                    .with_source_field_types(source_field_types)
                    .with_generic_fields(generic_fields)
                    .with_generic_methods(generic_methods)
                    .with_method_nullability(method_nullability)
                    .with_extension_receivers(extension_receivers)
                    .with_default_calls(default_calls)
                    .with_vararg_parameters(vararg_parameters)
                    .with_platform_symbols(platform_symbols)
                    .with_non_null_fields(non_null_fields)
                    .with_singleton_types(singleton_types)
                    .with_singleton_instances(singleton_instances)
                    .with_source_object_types(source_object_types)
                    .with_generic_type_projection(generic_type_projection)
                    .with_source_parameter_types(&self.parameter_code_vars, source_parameter_types)
                    .with_current_type(self.current_type.clone())
                    .with_source_current_type(source_current_type)
                    .with_source_super_type(source_super_type)
                    .with_return_type(self.return_type.clone())
                    .with_source_return_type(source_return_type)
                    .with_source_type_erasures(source_type_erasures)
                    .with_source_type_bounds(source_type_bounds)
                    .with_generic_throw_types(generic_throw_types)
                    .with_outer_instance(self.outer_instance.clone())
                    .with_outer_instance_fields(outer_instances)
                    .with_reserved_local_names(reserved_local_names)
                    .with_analysis_observer(observer)
                    .with_semantic_names(semantic_names)
            })
        })?;
        let mut ast = crate::profile_scope!("kotlin_backend.method_lower.ast", {
            KotlinLowerer::new(dialect)
                .lower(self.semantic.body())
                .map_err(KotlinDecompilerError::Kotlin)
        })?;
        let mut declarations = LexicalDeclarationPlacement;
        crate::profile_scope!("kotlin_backend.method_lower.declarations", {
            declarations
                .apply(&mut ast)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)
        })?;
        let mut structural_normalizer = KotlinAstNormalizer;
        crate::profile_scope!("kotlin_backend.method_lower.normalize", {
            structural_normalizer
                .apply(&mut ast)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)
        })?;
        if class_initializer {
            let mut exits = KotlinInitializerExitLowering;
            crate::profile_scope!("kotlin_backend.method_lower.initializer", {
                exits
                    .apply(&mut ast)
                    .map_err(crate::language::kotlin::KotlinLoweringError::from)
            })?;
        }
        let mut aggregates = AggregateInitializer::default();
        crate::profile_scope!("kotlin_backend.method_lower.aggregates", {
            aggregates
                .apply(&mut ast)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)
        })?;
        let mut assignment = DefiniteAssignment;
        crate::profile_scope!("kotlin_backend.method_lower.assignment", {
            assignment
                .apply(&mut ast)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)
        })?;
        let mut normalizer = KotlinAstNormalizer;
        crate::profile_scope!("kotlin_backend.method_lower.finalize", {
            normalizer
                .apply(&mut ast)
                .map_err(crate::language::kotlin::KotlinLoweringError::from)
        })?;
        Ok(ast)
    }

    pub fn type_uses(&self) -> impl Iterator<Item = &ArgType> {
        self.type_uses.iter()
    }

    pub fn is_empty(body: &crate::language::kotlin::KotlinMethodBody) -> bool {
        match &body.root {
            crate::language::kotlin::KotlinStmt::Empty => true,
            crate::language::kotlin::KotlinStmt::Block(statements) => {
                statements.is_empty()
                    || matches!(
                        statements.as_slice(),
                        [crate::language::kotlin::KotlinStmt::ConstructorInvocation {
                            target: crate::language::kotlin::KotlinConstructorTarget::Super,
                            args,
                        }] if args.is_empty()
                    )
            }
            _ => false,
        }
    }
}

#[derive(Default)]
struct MemberReferenceCollector {
    methods: std::collections::BTreeSet<crate::ir::MethodReference>,
    fields: std::collections::BTreeSet<crate::ir::FieldReference>,
}

impl crate::ir::SemanticVisitor for MemberReferenceCollector {
    fn enter_operation(&mut self, operation: &crate::ir::SemanticOperation) {
        match operation.payload.reference.as_ref() {
            Some(crate::ir::MemberReference::Method(method)) => {
                self.methods.insert(method.clone());
            }
            Some(crate::ir::MemberReference::Field(field)) => {
                self.fields.insert(field.clone());
            }
            None => {}
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(in crate::analysis::kotlin_backend) struct MethodBodyOptions {
    pub(in crate::analysis::kotlin_backend) current_type: Option<ArgType>,
    pub(in crate::analysis::kotlin_backend) return_type: Option<ArgType>,
    pub(in crate::analysis::kotlin_backend) enclosing_instance: Option<EnclosingInstanceAbi>,
    pub(in crate::analysis::kotlin_backend) outer_instance: Option<OuterInstanceField>,
    pub(in crate::analysis::kotlin_backend) outer_parameter: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::kotlin_backend) struct KotlinMethodDeclaration {
    pub annotations: Vec<AnnotationNode>,
    pub override_semantics: Option<crate::frontend::MethodOverrideSemantics>,
    pub is_interface_default: bool,
    pub modifiers: Vec<KotlinModifier>,
    pub access_flags: AccessInfo,
    pub source_bridge: bool,
    pub kind: KotlinMethodDeclarationKind,
    pub return_type: Option<ArgType>,
    pub source_return_type: Option<ArgType>,
    pub function_interface: Option<crate::ir::generic_types::JvmTypeSignature>,
    pub name: KotlinIdentifier,
    pub parameters: Vec<KotlinMethodParameter>,
    pub source_parameter_types: Vec<Option<ArgType>>,
    pub throws: Vec<ArgType>,
    /// Parsed JVM generic method signature, when the method carries a
    /// `Ldalvik/annotation/Signature;` annotation.
    pub signature: Option<crate::ir::generic_types::MethodSignature>,
}

impl KotlinMethodDeclaration {
    fn discard_source_metadata(&mut self) {
        self.annotations.clear();
        self.override_semantics = None;
        self.source_return_type = None;
        self.function_interface = None;
        self.source_parameter_types.fill(None);
        self.signature = None;
        for parameter in &mut self.parameters {
            parameter.annotations.clear();
        }
    }

    pub fn from_cfg(cfg: &CFG) -> Self {
        let param_names = extract_param_debug_names(cfg);
        Self {
            annotations: Vec::new(),
            override_semantics: None,
            is_interface_default: false,
            modifiers: if cfg.method().is_static() {
                vec![KotlinModifier::Static]
            } else {
                Vec::new()
            },
            access_flags: AccessInfo::for_method(0),
            source_bridge: false,
            kind: KotlinMethodDeclarationKind::Method,
            return_type: Some(cfg.method().descriptor().return_type.clone()),
            source_return_type: None,
            function_interface: None,
            name: KotlinIdentifier::from_dex(cfg.method().name()),
            parameters: cfg
                .method()
                .descriptor()
                .parameters
                .iter()
                .enumerate()
                .map(|(idx, ty)| KotlinMethodParameter {
                    annotations: Vec::new(),
                    ty: ty.clone(),
                    name: param_names
                        .get(idx)
                        .and_then(|name| name.as_deref())
                        .map(KotlinIdentifier::from_dex),
                    hidden: false,
                    varargs: false,
                })
                .collect(),
            source_parameter_types: vec![None; cfg.method().descriptor().parameters.len()],
            throws: Vec::new(),
            signature: None,
        }
    }

    pub fn from_method_node(
        class: &ClassNode,
        method: &MethodNode,
    ) -> Result<Self, crate::ir::generic_types::SignatureError> {
        let mut declaration = Self::from_method_node_erased(class, method);
        let (signature, source_return_type) = match method.signature.as_deref() {
            Some(signature) => (
                Some(crate::ir::generic_types::GenericSignatures::method(
                    signature,
                )?),
                None,
            ),
            None => {
                let inherited = method
                    .override_semantics
                    .as_ref()
                    .and_then(|semantics| semantics.inherited_signature.clone());
                let covariant_return = inherited
                    .as_ref()
                    .is_some_and(|signature| signature.return_erasure() != *method.return_type())
                    .then(|| method.return_type().clone());
                (inherited, covariant_return)
            }
        };
        declaration.throws = if !method.throws().is_empty() {
            method.throws().to_vec()
        } else if let Some(inherited) = (method.access_flags.is_synthetic()
            || FunctionObjectClass::analyze(class))
        .then(|| {
            method
                .override_semantics
                .as_ref()
                .map(|semantics| &semantics.inherited_throws)
        })
        .flatten()
        .filter(|throws| !throws.is_empty())
        {
            inherited.clone()
        } else {
            signature
                .as_ref()
                .map(|signature| {
                    signature
                        .throws
                        .iter()
                        .map(crate::ir::generic_types::JvmTypeSignature::erased)
                        .collect()
                })
                .unwrap_or_default()
        };
        declaration.source_return_type = source_return_type;
        declaration.signature = signature;
        Ok(declaration)
    }

    pub fn from_method_node_erased(class: &ClassNode, method: &MethodNode) -> Self {
        let kind = if method.is_class_init() {
            KotlinMethodDeclarationKind::ClassInitializer
        } else if method.is_constructor() {
            KotlinMethodDeclarationKind::Constructor
        } else {
            KotlinMethodDeclarationKind::Method
        };

        let enclosing_instance = EnclosingInstanceAbi::analyze(class);
        let source_bridge = SyntheticConstructorBridge::analyze(class, method);
        let mut parameters = method
            .param_types()
            .iter()
            .cloned()
            .enumerate()
            .map(|(idx, ty)| KotlinMethodParameter {
                annotations: method
                    .parameter_annotations
                    .get(idx)
                    .cloned()
                    .unwrap_or_default(),
                ty,
                name: None,
                hidden: false,
                varargs: method.access_flags.is_varargs() && idx + 1 == method.param_types().len(),
            })
            .collect::<Vec<_>>();
        if kind == KotlinMethodDeclarationKind::Constructor {
            if let Some(bridge) = source_bridge {
                parameters[bridge.marker_parameter()].hidden = true;
            }
            if let Some(parameter) = enclosing_instance
                .as_ref()
                .and_then(|enclosing| enclosing.constructor_parameter(method))
            {
                parameters[parameter].hidden = true;
            }
            if class.is_enum()
                && parameters
                    .first()
                    .is_some_and(|parameter| parameter.ty == ArgType::string())
                && parameters
                    .get(1)
                    .is_some_and(|parameter| parameter.ty == ArgType::INT)
            {
                parameters[0].hidden = true;
                parameters[1].hidden = true;
            }
        }
        let source_parameter_types = vec![None; parameters.len()];
        let mut modifiers = method_modifiers(&method.access_flags, kind, class.is_interface());
        if kind == KotlinMethodDeclarationKind::Method
            && method.override_semantics.is_some()
            && !method.access_flags.is_static()
        {
            modifiers.retain(|modifier| *modifier != KotlinModifier::Open);
            modifiers.push(KotlinModifier::Override);
        }
        Self {
            annotations: method.annotations.clone(),
            override_semantics: method.override_semantics.clone(),
            is_interface_default: class.is_interface()
                && method.code().is_some()
                && !method.access_flags.is_static(),
            modifiers,
            access_flags: method.access_flags,
            source_bridge: source_bridge.is_some(),
            kind,
            return_type: if kind == KotlinMethodDeclarationKind::Method {
                Some(method.return_type().clone())
            } else {
                None
            },
            source_return_type: None,
            function_interface: None,
            name: if kind == KotlinMethodDeclarationKind::Constructor {
                declaration_name(class)
            } else {
                KotlinIdentifier::from_dex(method.name())
            },
            parameters,
            source_parameter_types,
            throws: method.throws().to_vec(),
            signature: None,
        }
    }

    pub(in crate::analysis::kotlin_backend) fn visible_parameters(
        &self,
    ) -> impl Iterator<Item = &KotlinMethodParameter> {
        self.parameters.iter().filter(|param| !param.hidden)
    }

    pub(in crate::analysis::kotlin_backend) fn body_options(
        &self,
        class: Option<&ClassNode>,
    ) -> MethodBodyOptions {
        let enclosing_instance = class.and_then(EnclosingInstanceAbi::analyze);
        let outer_instance = class.and_then(OuterInstanceField::analyze);
        MethodBodyOptions {
            current_type: class.map(|class| class.class_type().clone()),
            return_type: self.return_type.clone(),
            outer_parameter: enclosing_instance.as_ref().and_then(|_| {
                self.kind
                    .is_constructor()
                    .then(|| {
                        self.parameters
                            .iter()
                            .position(|parameter| parameter.hidden)
                    })
                    .flatten()
            }),
            enclosing_instance,
            outer_instance,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::kotlin_backend) enum KotlinMethodDeclarationKind {
    Method,
    Constructor,
    ClassInitializer,
}

impl KotlinMethodDeclarationKind {
    pub(in crate::analysis::kotlin_backend) fn is_constructor(self) -> bool {
        self == Self::Constructor
    }

    pub(in crate::analysis::kotlin_backend) fn is_class_initializer(self) -> bool {
        self == Self::ClassInitializer
    }
}

fn method_modifiers(
    access: &AccessInfo,
    kind: KotlinMethodDeclarationKind,
    owner_is_interface: bool,
) -> Vec<KotlinModifier> {
    if kind == KotlinMethodDeclarationKind::ClassInitializer {
        return Vec::new();
    }

    let mut modifiers = Vec::new();
    if access.is_public() && !owner_is_interface {
        modifiers.push(KotlinModifier::Public);
    } else if access.is_private() {
        modifiers.push(KotlinModifier::Private);
    } else if access.is_protected() {
        modifiers.push(KotlinModifier::Protected);
    }

    if kind == KotlinMethodDeclarationKind::Constructor {
        return modifiers;
    }

    if access.is_static() {
        modifiers.push(KotlinModifier::Static);
    }
    if access.is_final() {
        modifiers.push(KotlinModifier::Final);
    }
    if access.is_abstract() && !owner_is_interface {
        modifiers.push(KotlinModifier::Abstract);
    }
    if !owner_is_interface
        && !access.is_static()
        && !access.is_private()
        && !access.is_final()
        && !access.is_abstract()
    {
        modifiers.push(KotlinModifier::Open);
    }
    if access.is_native() {
        modifiers.push(KotlinModifier::Native);
    }
    if access.is_synchronized() || access.is_declared_synchronized() {
        modifiers.push(KotlinModifier::Synchronized);
    }
    if access.is_strict() {
        modifiers.push(KotlinModifier::StrictFp);
    }
    if owner_is_interface && !access.is_static() && !access.is_abstract() {
        modifiers.push(KotlinModifier::Default);
    }

    modifiers
}

/// Pull per-parameter names from the CFG's debug info, in declaration order.
/// Returns `None` for each parameter that has no recorded name.
///
/// Parameter names can come from two places in the DEX debug info:
///   1. The header `parameter_names` table (`uleb128p1` string ids).
///   2. `DBG_START_LOCAL` entries that cover parameter registers from address
///      0 — `d8`/`dx` frequently emit them this way and leave the header table
///      populated with `NO_INDEX`.
pub(in crate::analysis::kotlin_backend) fn collect_param_debug_names(
    cfg: &CFG,
) -> Vec<Option<String>> {
    let Some(debug_info) = cfg.debug_info.as_ref() else {
        return Vec::new();
    };

    // DEX parameter locations are word-based; wide values consume two words.
    let first_input = cfg.registers.saturating_sub(cfg.ins);
    let has_this = !cfg.method().is_static();

    // Build a register → debug-name table from the header table and from any
    // `DBG_START_LOCAL` entry that begins at address 0 (i.e. covers a parameter
    // from method entry).
    let mut register_name: std::collections::BTreeMap<u32, String> =
        std::collections::BTreeMap::new();
    for var in &debug_info.local_vars {
        if var.start_addr == 0 && is_meaningful_param_name(&var.name) {
            register_name
                .entry(var.register)
                .or_insert_with(|| var.name.clone());
        }
    }

    let mut register = first_input + u32::from(has_this);
    cfg.method()
        .descriptor()
        .parameters
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            let parameter_register = register;
            register += if ty.is_wide() { 2 } else { 1 };
            // Header table first.
            if let Some(Some(name)) = debug_info.param_names.get(idx) {
                if is_meaningful_param_name(name) {
                    return Some(name.clone());
                }
            }
            // Fall back to a `DBG_START_LOCAL` entry on this parameter's
            // register.
            if parameter_register < cfg.registers {
                if let Some(name) = register_name.get(&parameter_register) {
                    return Some(name.clone());
                }
            }
            None
        })
        .collect()
}

fn extract_param_debug_names(cfg: &CFG) -> Vec<Option<String>> {
    collect_param_debug_names(cfg)
}

fn is_meaningful_param_name(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    let mut chars = name.chars();
    let first = match chars.next() {
        Some(c) => c,
        None => return false,
    };
    if !(first.is_ascii_alphabetic() || first == '_' || first == '$') {
        return false;
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}
