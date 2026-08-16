use crate::frontend::{AccessInfo, AnnotationNode, ClassNode, MethodNode};
use crate::ir::{ty::ArgType, CFG};
use crate::language::java::{
    AggregateInitializer, DefiniteAssignment, JavaAstNormalizer, JavaAstTransform, JavaIdentifier,
    JavaInitializerExitLowering, JavaLowerer, JavaMethodCompletion, JavaModifier, JavaType,
    JavaVoidTailLinearizer, LexicalDeclarationPlacement,
};

use super::super::method_pipeline::MethodBodyAnalysis;
use super::super::type_names::JavaTypeNameResolver;
use super::super::JavaDecompilerError;
use super::class::declaration_name;
use super::source_abi::{
    EnclosingInstanceAbi, FunctionObjectClass, OuterInstanceField, SyntheticConstructorBridge,
};
use crate::analysis::MethodRecoveryFailure;

#[derive(Debug, Clone)]
pub(in crate::analysis::java_backend) struct JavaMethodModel {
    pub declaration: JavaMethodDeclaration,
    pub body: Option<JavaMethodBody>,
    pub failure: Option<MethodRecoveryFailure>,
}

#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::java_backend) struct JavaMethodParameter {
    pub annotations: Vec<AnnotationNode>,
    pub ty: ArgType,
    pub name: Option<JavaIdentifier>,
    pub hidden: bool,
    pub varargs: bool,
}

#[derive(Debug, Clone)]
pub(in crate::analysis::java_backend) struct JavaMethodBody {
    semantic: crate::ir::SemanticMethod<crate::ir::SourceSyntaxSemantics>,
    is_static: bool,
    this_code_var: Option<u32>,
    parameter_code_vars: Vec<Option<u32>>,
    type_uses: std::collections::BTreeSet<ArgType>,
    current_type: Option<ArgType>,
    return_type: Option<ArgType>,
    outer_instance: Option<crate::language::java::OuterInstanceBinding>,
}

impl JavaMethodModel {
    pub fn from_body_analysis_with_options(
        declaration: JavaMethodDeclaration,
        analysis: MethodBodyAnalysis,
        options: MethodBodyOptions,
    ) -> Result<Self, JavaDecompilerError> {
        let body = JavaMethodBody::from_analysis(analysis, options);
        Ok(Self {
            declaration,
            body: Some(body),
            failure: None,
        })
    }

    pub fn from_declaration(declaration: JavaMethodDeclaration) -> Self {
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
        let mut declaration = JavaMethodDeclaration::from_method_node_erased(class, method);
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
        class_name: &JavaIdentifier,
        class_modifiers: &[JavaModifier],
        body: &crate::language::java::JavaMethodBody,
    ) -> bool {
        self.declaration.kind == JavaMethodDeclarationKind::Constructor
            && &self.declaration.name == class_name
            && self.declaration.visible_parameters().next().is_none()
            && Self::access_modifier(&self.declaration.modifiers)
                == Self::access_modifier(class_modifiers)
            && JavaMethodBody::is_empty(body)
    }

    fn access_modifier(modifiers: &[JavaModifier]) -> Option<JavaModifier> {
        modifiers.iter().copied().find(|modifier| {
            matches!(
                modifier,
                JavaModifier::Public | JavaModifier::Protected | JavaModifier::Private
            )
        })
    }
}

impl JavaMethodBody {
    pub fn from_analysis(analysis: MethodBodyAnalysis, options: MethodBodyOptions) -> Self {
        let outer_instance = options.enclosing_instance.map(|enclosing| {
            let parameter = options
                .outer_parameter
                .and_then(|index| analysis.parameter_code_vars.get(index).copied().flatten());
            crate::language::java::OuterInstanceBinding::new(
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

    pub(in crate::analysis::java_backend) fn method_references(
        &self,
    ) -> std::collections::BTreeSet<crate::ir::MethodReference> {
        let mut collector = MemberReferenceCollector::default();
        crate::ir::SemanticVisitor::visit_node(&mut collector, self.semantic.body());
        collector.methods
    }

    pub(in crate::analysis::java_backend) fn field_references(
        &self,
    ) -> std::collections::BTreeSet<crate::ir::FieldReference> {
        let mut collector = MemberReferenceCollector::default();
        crate::ir::SemanticVisitor::visit_node(&mut collector, self.semantic.body());
        collector.fields
    }

    pub(in crate::analysis::java_backend) fn static_owner_types(
        &self,
    ) -> std::collections::BTreeSet<ArgType> {
        let mut collector = MemberReferenceCollector::default();
        crate::ir::SemanticVisitor::visit_node(&mut collector, self.semantic.body());
        collector.static_owners
    }

    pub(in crate::analysis::java_backend) fn outer_instance_field(
        &self,
    ) -> Option<(&crate::ir::FieldReference, &ArgType)> {
        let binding = self.outer_instance.as_ref()?;
        Some((binding.field()?, binding.outer_type()))
    }

    pub fn lower(
        &self,
        parameter_names: &[JavaIdentifier],
        type_names: &JavaTypeNameResolver,
        member_names: std::sync::Arc<crate::language::java::JavaMemberNames>,
        source_field_types: std::sync::Arc<
            std::collections::BTreeMap<crate::ir::FieldReference, JavaType>,
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
        source_object_types: std::sync::Arc<std::collections::BTreeMap<ArgType, JavaType>>,
        generic_type_projection: std::sync::Arc<dyn crate::language::java::GenericTypeProjection>,
        source_current_type: Option<JavaType>,
        source_super_type: Option<JavaType>,
        source_parameter_types: &[Option<JavaType>],
        source_return_type: Option<JavaType>,
        source_type_erasures: std::collections::BTreeMap<JavaIdentifier, ArgType>,
        source_type_bounds: std::collections::BTreeMap<JavaIdentifier, JavaType>,
        generic_throw_types: Vec<crate::language::java::JavaSourceErasure>,
        outer_instances: std::collections::BTreeMap<crate::ir::FieldReference, JavaType>,
        reserved_local_names: std::collections::BTreeSet<JavaIdentifier>,
        class_initializer: bool,
        observer: std::sync::Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Result<crate::language::java::JavaMethodBody, JavaDecompilerError> {
        let semantically_terminal = self
            .return_type
            .as_ref()
            .is_some_and(|return_type| return_type != &ArgType::VOID)
            && !crate::ir::semantic::SemanticCompletion::analyze(self.semantic.body())
                .can_complete_normally();
        let completion_type = source_return_type.clone();
        let (source_field_types, source_types) =
            crate::profile_scope!("java_backend.method_lower.types", {
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
                    .collect::<Result<std::collections::BTreeMap<_, _>, JavaDecompilerError>>()?;
                Ok::<_, JavaDecompilerError>((source_field_types, source_types))
            })?;
        let semantic_names = crate::profile_scope!("java_backend.method_lower.names", {
            super::super::semantic_naming::SemanticNameRecovery::new(type_names).recover(
                self.semantic.body(),
                self.semantic.state().types(),
                parameter_names,
                &self.parameter_code_vars,
                self.this_code_var,
            )
        });
        let dialect = crate::profile_scope!("java_backend.method_lower.dialect", {
            crate::language::java::DexJavaDialect::new(
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
        let mut ast = crate::profile_scope!("java_backend.method_lower.ast", {
            JavaLowerer::new(dialect)
                .lower(self.semantic.body())
                .map_err(JavaDecompilerError::Java)
        })?;
        let mut declarations = LexicalDeclarationPlacement;
        crate::profile_scope!("java_backend.method_lower.declarations", {
            declarations
                .apply(&mut ast)
                .map_err(crate::language::java::JavaLoweringError::from)
        })?;
        let mut structural_normalizer = JavaAstNormalizer;
        crate::profile_scope!("java_backend.method_lower.normalize", {
            structural_normalizer
                .apply(&mut ast)
                .map_err(crate::language::java::JavaLoweringError::from)
        })?;
        if class_initializer {
            let mut exits = JavaInitializerExitLowering;
            crate::profile_scope!("java_backend.method_lower.initializer", {
                exits
                    .apply(&mut ast)
                    .map_err(crate::language::java::JavaLoweringError::from)
            })?;
        }
        let mut aggregates = AggregateInitializer::default();
        crate::profile_scope!("java_backend.method_lower.aggregates", {
            aggregates
                .apply(&mut ast)
                .map_err(crate::language::java::JavaLoweringError::from)
        })?;
        let mut assignment = DefiniteAssignment;
        crate::profile_scope!("java_backend.method_lower.assignment", {
            assignment
                .apply(&mut ast)
                .map_err(crate::language::java::JavaLoweringError::from)
        })?;
        let mut normalizer = JavaAstNormalizer;
        crate::profile_scope!("java_backend.method_lower.finalize", {
            normalizer
                .apply(&mut ast)
                .map_err(crate::language::java::JavaLoweringError::from)
        })?;
        if !class_initializer && self.return_type.as_ref() == Some(&ArgType::VOID) {
            let mut tail = JavaVoidTailLinearizer;
            crate::profile_scope!("java_backend.method_lower.void_tail", {
                match tail.apply(&mut ast) {
                    Ok(_) => {}
                    Err(never) => match never {},
                }
            });
        }
        if semantically_terminal {
            if let Some(return_type) = completion_type {
                let mut completion = JavaMethodCompletion::new(return_type);
                crate::profile_scope!("java_backend.method_lower.completion", {
                    match completion.apply(&mut ast) {
                        Ok(_) => {}
                        Err(never) => match never {},
                    }
                });
            }
        }
        Ok(ast)
    }

    pub fn type_uses(&self) -> impl Iterator<Item = &ArgType> {
        self.type_uses.iter()
    }

    pub fn is_empty(body: &crate::language::java::JavaMethodBody) -> bool {
        match &body.root {
            crate::language::java::JavaStmt::Empty => true,
            crate::language::java::JavaStmt::Block(statements) => {
                statements.is_empty()
                    || matches!(
                        statements.as_slice(),
                        [crate::language::java::JavaStmt::ConstructorInvocation {
                            target: crate::language::java::JavaConstructorTarget::Super,
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
    static_owners: std::collections::BTreeSet<ArgType>,
}

impl crate::ir::SemanticVisitor for MemberReferenceCollector {
    fn enter_operation(&mut self, operation: &crate::ir::SemanticOperation) {
        match operation.payload.reference.as_ref() {
            Some(crate::ir::MemberReference::Method(method)) => {
                if operation.payload.invoke_type == Some(crate::ir::InvokeType::Static) {
                    self.static_owners.insert(method.owner.clone());
                }
                self.methods.insert(method.clone());
            }
            Some(crate::ir::MemberReference::Field(field)) => {
                if matches!(
                    operation.insn_type,
                    crate::ir::InsnType::Sget | crate::ir::InsnType::Sput
                ) {
                    self.static_owners.insert(field.owner.clone());
                }
                self.fields.insert(field.clone());
            }
            None => {}
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(in crate::analysis::java_backend) struct MethodBodyOptions {
    pub(in crate::analysis::java_backend) current_type: Option<ArgType>,
    pub(in crate::analysis::java_backend) return_type: Option<ArgType>,
    pub(in crate::analysis::java_backend) enclosing_instance: Option<EnclosingInstanceAbi>,
    pub(in crate::analysis::java_backend) outer_instance: Option<OuterInstanceField>,
    pub(in crate::analysis::java_backend) outer_parameter: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::java_backend) struct JavaMethodDeclaration {
    pub annotations: Vec<AnnotationNode>,
    pub override_semantics: Option<crate::frontend::MethodOverrideSemantics>,
    pub is_interface_default: bool,
    pub modifiers: Vec<JavaModifier>,
    pub access_flags: AccessInfo,
    pub source_bridge: bool,
    pub kind: JavaMethodDeclarationKind,
    pub return_type: Option<ArgType>,
    pub source_return_type: Option<ArgType>,
    pub function_interface: Option<crate::ir::generic_types::JvmTypeSignature>,
    pub name: JavaIdentifier,
    pub parameters: Vec<JavaMethodParameter>,
    pub source_parameter_types: Vec<Option<ArgType>>,
    pub throws: Vec<ArgType>,
    /// Parsed JVM generic method signature, when the method carries a
    /// `Ldalvik/annotation/Signature;` annotation.
    pub signature: Option<crate::ir::generic_types::MethodSignature>,
}

impl JavaMethodDeclaration {
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
                vec![JavaModifier::Static]
            } else {
                Vec::new()
            },
            access_flags: AccessInfo::for_method(0),
            source_bridge: false,
            kind: JavaMethodDeclarationKind::Method,
            return_type: Some(cfg.method().descriptor().return_type.clone()),
            source_return_type: None,
            function_interface: None,
            name: JavaIdentifier::from_dex(cfg.method().name()),
            parameters: cfg
                .method()
                .descriptor()
                .parameters
                .iter()
                .enumerate()
                .map(|(idx, ty)| JavaMethodParameter {
                    annotations: Vec::new(),
                    ty: ty.clone(),
                    name: param_names
                        .get(idx)
                        .and_then(|name| name.as_deref())
                        .map(JavaIdentifier::from_dex),
                    hidden: false,
                    varargs: false,
                })
                .collect(),
            source_parameter_types: vec![None; cfg.method().descriptor().parameters.len()],
            throws: Vec::new(),
            signature: None,
        }
    }

    pub fn from_method_node<'a>(
        class: &ClassNode,
        method: &MethodNode,
        lexical_type_variables: impl IntoIterator<Item = &'a str>,
        inherited_declaration_signature: Option<crate::ir::generic_types::MethodSignature>,
    ) -> Result<Self, crate::ir::generic_types::SignatureError> {
        let mut declaration = Self::from_method_node_erased(class, method);
        let parsed_signature = method
            .signature
            .as_deref()
            .map(crate::ir::generic_types::GenericSignatures::method)
            .transpose()?;
        // Local and anonymous classes can legitimately retain variables from
        // an enclosing generic method even when incomplete DEX enclosing
        // metadata keeps them out of the reconstructed lexical scope. Java
        // enums and annotations cannot declare fallback type parameters at
        // all, so only those declaration kinds must reject an orphaned method
        // variable here.
        let rejects_fallback_type_parameters =
            class.access_flags.is_enum() || class.access_flags.is_annotation();
        let has_unbound_variables = rejects_fallback_type_parameters
            && parsed_signature.as_ref().is_some_and(|signature| {
                signature.has_unbound_type_variables(lexical_type_variables)
            });
        let explicit_signature = parsed_signature.filter(|signature| {
            !has_unbound_variables && method_signature_is_java_denotable(signature)
        });
        let (signature, source_return_type) = match explicit_signature {
            Some(signature) => (Some(signature), None),
            None => {
                let inherited = method
                    .override_semantics
                    .as_ref()
                    .and_then(|semantics| semantics.inherited_signature.clone())
                    .or_else(|| {
                        has_unbound_variables
                            .then_some(inherited_declaration_signature)
                            .flatten()
                    });
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
            JavaMethodDeclarationKind::ClassInitializer
        } else if method.is_constructor() {
            JavaMethodDeclarationKind::Constructor
        } else {
            JavaMethodDeclarationKind::Method
        };

        let enclosing_instance = EnclosingInstanceAbi::analyze(class);
        let source_bridge = SyntheticConstructorBridge::analyze(class, method);
        let mut parameters = method
            .param_types()
            .iter()
            .cloned()
            .enumerate()
            .map(|(idx, ty)| JavaMethodParameter {
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
        if kind == JavaMethodDeclarationKind::Constructor {
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
        Self {
            annotations: method.annotations.clone(),
            override_semantics: method.override_semantics.clone(),
            is_interface_default: class.is_interface()
                && method.code().is_some()
                && !method.access_flags.is_static(),
            modifiers: method_modifiers(&method.access_flags, kind, class.is_interface()),
            access_flags: method.access_flags,
            source_bridge: source_bridge.is_some(),
            kind,
            return_type: if kind == JavaMethodDeclarationKind::Method {
                Some(method.return_type().clone())
            } else {
                None
            },
            source_return_type: None,
            function_interface: None,
            name: if kind == JavaMethodDeclarationKind::Constructor {
                declaration_name(class)
            } else {
                JavaIdentifier::from_dex(method.name())
            },
            parameters,
            source_parameter_types,
            throws: method.throws().to_vec(),
            signature: None,
        }
    }

    pub(in crate::analysis::java_backend) fn visible_parameters(
        &self,
    ) -> impl Iterator<Item = &JavaMethodParameter> {
        self.parameters.iter().filter(|param| !param.hidden)
    }

    pub(in crate::analysis::java_backend) fn body_options(
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

fn method_signature_is_java_denotable(
    signature: &crate::ir::generic_types::MethodSignature,
) -> bool {
    signature.type_parameters.iter().all(|parameter| {
        parameter
            .class_bound
            .iter()
            .chain(&parameter.interface_bounds)
            .all(|bound| {
                !matches!(
                    bound,
                    crate::ir::generic_types::JvmTypeSignature::Array(_)
                        | crate::ir::generic_types::JvmTypeSignature::BaseType(_)
                )
            })
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::java_backend) enum JavaMethodDeclarationKind {
    Method,
    Constructor,
    ClassInitializer,
}

impl JavaMethodDeclarationKind {
    pub(in crate::analysis::java_backend) fn is_constructor(self) -> bool {
        self == Self::Constructor
    }

    pub(in crate::analysis::java_backend) fn is_class_initializer(self) -> bool {
        self == Self::ClassInitializer
    }
}

fn method_modifiers(
    access: &AccessInfo,
    kind: JavaMethodDeclarationKind,
    owner_is_interface: bool,
) -> Vec<JavaModifier> {
    if kind == JavaMethodDeclarationKind::ClassInitializer {
        return Vec::new();
    }

    let mut modifiers = Vec::new();
    if access.is_public() && !owner_is_interface {
        modifiers.push(JavaModifier::Public);
    } else if access.is_private() {
        modifiers.push(JavaModifier::Private);
    } else if access.is_protected() {
        modifiers.push(JavaModifier::Protected);
    }

    if kind == JavaMethodDeclarationKind::Constructor {
        return modifiers;
    }

    if access.is_static() {
        modifiers.push(JavaModifier::Static);
    }
    if access.is_final() {
        modifiers.push(JavaModifier::Final);
    }
    if access.is_abstract() && !owner_is_interface {
        modifiers.push(JavaModifier::Abstract);
    }
    if access.is_native() {
        modifiers.push(JavaModifier::Native);
    }
    if access.is_synchronized() || access.is_declared_synchronized() {
        modifiers.push(JavaModifier::Synchronized);
    }
    if access.is_strict() {
        modifiers.push(JavaModifier::StrictFp);
    }
    if owner_is_interface && !access.is_static() && !access.is_abstract() {
        modifiers.push(JavaModifier::Default);
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
pub(in crate::analysis::java_backend) fn collect_param_debug_names(
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

#[cfg(test)]
mod tests {
    use crate::ir::generic_types::GenericSignatures;

    use super::method_signature_is_java_denotable;

    #[test]
    fn rejects_an_array_type_parameter_bound_in_a_method_signature() {
        let signature = GenericSignatures::method(
            "<C:[Ljava/lang/Object;:TR;R:Ljava/lang/Object;>\
             (TC;Lkotlin/jvm/functions/Function0<+TR;>;)TR;",
        )
        .expect("Kotlin array intersection signature");

        assert!(!method_signature_is_java_denotable(&signature));
    }

    #[test]
    fn accepts_a_java_denotable_method_signature() {
        let signature =
            GenericSignatures::method("<T:Ljava/lang/Object;>(Ljava/util/List<+TT;>;)TT;")
                .expect("ordinary generic method signature");

        assert!(method_signature_is_java_denotable(&signature));
    }
}
