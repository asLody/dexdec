use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use crate::ir::analysis::{SourceTypeEnvironment, TypeConstraintError};
use crate::ir::generic_types::{
    ClassTypeSignature, GenericFieldContract, GenericMethodContract, JvmTypeSignature,
    TypeParameter,
};
use crate::ir::{
    ArgType, ArithOp, CmpBias, FieldReference, IfOp, InsnType, InstructionId, InvokeType,
    MemberReference, MethodReference, PrimitiveType, RegisterArg, SemanticBindingKind,
    SemanticExpression, SemanticOperation, SemanticPredicate, SemanticStatement,
    SemanticStatementKind, SemanticVisitor,
};

use super::ast::{
    KotlinAssignOp, KotlinBinaryOp, KotlinCallArguments, KotlinConstructorTarget, KotlinExpr,
    KotlinIdentifier, KotlinLiteral, KotlinNameScope, KotlinPrimitiveType, KotlinStmt, KotlinType,
    KotlinTypeArgument, KotlinUnaryOp,
};
use super::declarations::{DeclarationAnalysis, DeclarationError, SourceVariable};
use super::jvm_calls::KotlinJvmCallSyntax;
use super::lower::{KotlinCatchBinding, KotlinDialect, KotlinStructuralError};
use super::syntax::primitives::PrimitiveOperationDomain;
use super::KotlinJvmBuiltins;

mod input;

use super::members::KotlinMemberNames;
use super::source_types::{
    invocation_expression_signature, GenericInvocationCompatibility, GenericTypeEvidence,
    GenericTypeProjection, GenericTypeRelation, GenericTypeSolver, KotlinTypeRelations,
    SourceTypeFlow,
};
use input::KotlinInputVerifier;

#[derive(Debug, Clone, Default)]
pub struct KotlinMethodNullability {
    parameters: Vec<bool>,
    return_non_null: bool,
}

impl KotlinMethodNullability {
    pub fn new(parameters: Vec<bool>, return_non_null: bool) -> Self {
        Self {
            parameters,
            return_non_null,
        }
    }

    pub fn parameter_is_non_null(&self, parameter: usize) -> bool {
        self.parameters.get(parameter).copied().unwrap_or(false)
    }

    pub fn return_is_non_null(&self) -> bool {
        self.return_non_null
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KotlinDefaultMask {
    parameter: usize,
    word: usize,
    bit: u32,
}

impl KotlinDefaultMask {
    pub fn new(parameter: usize, word: usize, bit: u32) -> Self {
        Self {
            parameter,
            word,
            bit,
        }
    }

    pub fn parameter(self) -> usize {
        self.parameter
    }

    pub fn word(self) -> usize {
        self.word
    }

    pub fn bit(self) -> u32 {
        self.bit
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KotlinDefaultCallContract {
    target: MethodReference,
    masks: Vec<KotlinDefaultMask>,
    mask_count: usize,
    parameter_names: BTreeMap<usize, KotlinIdentifier>,
    varargs: BTreeSet<usize>,
    kind: KotlinDefaultCallKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KotlinDefaultCallKind {
    Function {
        target_static: bool,
        extension_receiver: Option<usize>,
    },
    Constructor,
}

impl KotlinDefaultCallContract {
    pub fn function(
        target: MethodReference,
        masks: Vec<KotlinDefaultMask>,
        mask_count: usize,
        target_static: bool,
        extension_receiver: Option<usize>,
        parameter_names: BTreeMap<usize, KotlinIdentifier>,
        varargs: BTreeSet<usize>,
    ) -> Self {
        Self {
            target,
            masks,
            mask_count,
            parameter_names,
            varargs,
            kind: KotlinDefaultCallKind::Function {
                target_static,
                extension_receiver,
            },
        }
    }

    pub fn constructor(
        target: MethodReference,
        masks: Vec<KotlinDefaultMask>,
        mask_count: usize,
        parameter_names: BTreeMap<usize, KotlinIdentifier>,
        varargs: BTreeSet<usize>,
    ) -> Self {
        Self {
            target,
            masks,
            mask_count,
            parameter_names,
            varargs,
            kind: KotlinDefaultCallKind::Constructor,
        }
    }

    pub fn target(&self) -> &MethodReference {
        &self.target
    }

    pub fn masks(&self) -> &[KotlinDefaultMask] {
        &self.masks
    }

    pub fn mask_count(&self) -> usize {
        self.mask_count
    }

    fn target_is_static(&self) -> Option<bool> {
        match self.kind {
            KotlinDefaultCallKind::Function { target_static, .. } => Some(target_static),
            KotlinDefaultCallKind::Constructor => None,
        }
    }

    pub fn extension_receiver(&self) -> Option<usize> {
        match self.kind {
            KotlinDefaultCallKind::Function {
                extension_receiver, ..
            } => extension_receiver,
            KotlinDefaultCallKind::Constructor => None,
        }
    }

    fn parameter_name(&self, parameter: usize) -> Option<&KotlinIdentifier> {
        self.parameter_names.get(&parameter)
    }

    fn parameter_is_vararg(&self, parameter: usize) -> bool {
        self.varargs.contains(&parameter)
    }

    fn is_constructor(&self) -> bool {
        self.kind == KotlinDefaultCallKind::Constructor
    }
}

struct RecoveredArguments {
    values: Vec<KotlinExpr>,
    parameters: Vec<usize>,
    omitted: BTreeSet<usize>,
}

impl RecoveredArguments {
    fn is_positional(&self, parameter_count: usize, extension: Option<usize>) -> bool {
        let source = (0..parameter_count)
            .filter(|parameter| Some(*parameter) != extension)
            .collect::<Vec<_>>();
        let Some(first) = source
            .iter()
            .position(|parameter| self.omitted.contains(parameter))
        else {
            return false;
        };
        source[first..]
            .iter()
            .all(|parameter| self.omitted.contains(parameter))
    }
}

struct DefaultArguments<'a> {
    contract: &'a KotlinDefaultCallContract,
    arguments: &'a [KotlinExpr],
    dispatch_count: usize,
}

impl<'a> DefaultArguments<'a> {
    fn new(
        contract: &'a KotlinDefaultCallContract,
        arguments: &'a [KotlinExpr],
        dispatch_count: usize,
    ) -> Self {
        Self {
            contract,
            arguments,
            dispatch_count,
        }
    }

    fn recover(&self) -> Option<RecoveredArguments> {
        let parameter_count = self.contract.target().descriptor.parameters.len();
        let mask_start = self.dispatch_count + parameter_count;
        let marker = mask_start + self.contract.mask_count();
        if self.arguments.len() != marker + 1 || !Self::is_null(&self.arguments[marker]) {
            return None;
        }
        let words = self.arguments[mask_start..marker]
            .iter()
            .map(Self::integer)
            .collect::<Option<Vec<_>>>()?;
        let mut allowed = vec![0u32; self.contract.mask_count()];
        let mut omitted = BTreeSet::new();
        for mask in self.contract.masks() {
            let word = allowed.get_mut(mask.word())?;
            *word |= mask.bit();
            if words
                .get(mask.word())
                .is_some_and(|word| word & mask.bit() != 0)
            {
                omitted.insert(mask.parameter());
            }
        }
        if words
            .iter()
            .zip(&allowed)
            .any(|(word, allowed)| word & !allowed != 0)
        {
            return None;
        }
        let target_arguments = &self.arguments[self.dispatch_count..mask_start];
        if omitted.iter().any(|parameter| {
            target_arguments
                .get(*parameter)
                .is_none_or(|argument| !Self::is_passive(argument))
        }) {
            return None;
        }
        Some(RecoveredArguments {
            parameters: (0..parameter_count)
                .filter(|parameter| !omitted.contains(parameter))
                .collect(),
            values: target_arguments
                .iter()
                .enumerate()
                .filter(|(parameter, _)| !omitted.contains(parameter))
                .map(|(_, argument)| argument.clone())
                .collect(),
            omitted,
        })
    }

    fn integer(expression: &KotlinExpr) -> Option<u32> {
        match expression {
            KotlinExpr::Literal(KotlinLiteral::Integer(value)) => Some(*value as u32),
            KotlinExpr::Cast { value, .. } | KotlinExpr::SmartCast(value) => Self::integer(value),
            _ => None,
        }
    }

    fn is_null(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::Literal(KotlinLiteral::Null) => true,
            KotlinExpr::Cast { value, .. } | KotlinExpr::SmartCast(value) => Self::is_null(value),
            _ => false,
        }
    }

    fn is_passive(expression: &KotlinExpr) -> bool {
        match expression {
            KotlinExpr::Literal(_) => true,
            KotlinExpr::Cast { value, .. } | KotlinExpr::SmartCast(value) => {
                Self::is_passive(value)
            }
            _ => false,
        }
    }
}

struct DefaultCall<'a> {
    contract: &'a KotlinDefaultCallContract,
    arguments: &'a [KotlinExpr],
    dispatch_owner: Option<ArgType>,
}

impl<'a> DefaultCall<'a> {
    fn new(
        contract: &'a KotlinDefaultCallContract,
        arguments: &'a [KotlinExpr],
        dispatch_owner: Option<ArgType>,
    ) -> Self {
        Self {
            contract,
            arguments,
            dispatch_owner,
        }
    }

    fn lower(&self, dialect: &DexKotlinDialect) -> Result<Option<KotlinExpr>, KotlinLoweringError> {
        let target = self.contract.target();
        let Some(target_static) = self.contract.target_is_static() else {
            return Ok(None);
        };
        let dispatch_count = usize::from(!target_static);
        let Some(recovered) =
            DefaultArguments::new(self.contract, self.arguments, dispatch_count).recover()
        else {
            return Ok(None);
        };
        let mut arguments = recovered.values;
        let mut parameters = recovered.parameters;
        let omitted = recovered.omitted;
        let (receiver, owner) = match (target_static, self.contract.extension_receiver()) {
            (true, Some(extension)) => {
                let Some(extension) = Self::retained_index(extension, &omitted) else {
                    return Ok(None);
                };
                if extension >= arguments.len() {
                    return Ok(None);
                }
                parameters.remove(extension);
                (Some(Box::new(arguments.remove(extension))), None)
            }
            (true, None) => (None, Some(dialect.static_owner_type(&target.owner)?)),
            (false, Some(extension)) => {
                if !matches!(self.arguments.first(), Some(KotlinExpr::This)) {
                    return Ok(None);
                }
                let Some(extension) = Self::retained_index(extension, &omitted) else {
                    return Ok(None);
                };
                if extension >= arguments.len() {
                    return Ok(None);
                }
                parameters.remove(extension);
                (Some(Box::new(arguments.remove(extension))), None)
            }
            (false, None) => {
                if let Some(owner) = self.dispatch_owner.as_ref() {
                    (None, Some(dialect.static_owner_type(owner)?))
                } else {
                    let Some(dispatch) = self.arguments.first() else {
                        return Ok(None);
                    };
                    (Some(Box::new(dispatch.clone())), None)
                }
            }
        };
        let mut names = Vec::new();
        let mut spreads = Vec::new();
        for (argument, parameter) in parameters.iter().copied().enumerate() {
            let follows_omission = (0..parameter).any(|index| {
                Some(index) != self.contract.extension_receiver() && omitted.contains(&index)
            });
            if !follows_omission {
                if self.contract.parameter_is_vararg(parameter) {
                    spreads.push(argument);
                }
                continue;
            }
            let Some(name) = self.contract.parameter_name(parameter).cloned() else {
                return Ok(None);
            };
            names.push((argument, name));
        }
        let Some(arguments) = KotlinCallArguments::from_parts(arguments, names, spreads) else {
            return Ok(None);
        };
        Ok(Some(KotlinExpr::Call {
            receiver,
            owner,
            type_arguments: Vec::new(),
            method: dialect.member_names.method(target),
            args: arguments,
        }))
    }

    fn retained_index(parameter: usize, omitted: &BTreeSet<usize>) -> Option<usize> {
        (!omitted.contains(&parameter)).then(|| parameter - omitted.range(..parameter).count())
    }
}

#[derive(Clone, Copy)]
struct ComparisonTest {
    operator: IfOp,
    negated: bool,
}

struct ComparisonSemantics;

impl ComparisonSemantics {
    const OPERATORS: [IfOp; 6] = [IfOp::Eq, IfOp::Ne, IfOp::Lt, IfOp::Le, IfOp::Gt, IfOp::Ge];

    fn recover(bias: Option<CmpBias>, ty: &ArgType, test: IfOp) -> Option<ComparisonTest> {
        if ty == &ArgType::LONG {
            return matches!(bias, None | Some(CmpBias::None)).then_some(ComparisonTest {
                operator: test,
                negated: false,
            });
        }
        if !matches!(
            ty,
            ArgType::Primitive(PrimitiveType::Float | PrimitiveType::Double)
        ) {
            return None;
        }
        let unordered = match bias {
            Some(CmpBias::Lt) => -1,
            Some(CmpBias::Gt) => 1,
            Some(CmpBias::None) | None => return None,
        };
        let expected = [-1, 0, 1, unordered].map(|value| Self::integer_test(value, test));
        let mut operators = vec![test];
        operators.extend(
            Self::OPERATORS
                .into_iter()
                .filter(|operator| *operator != test),
        );
        for negated in [false, true] {
            for operator in &operators {
                let mut actual = [
                    Self::integer_test(-1, *operator),
                    Self::integer_test(0, *operator),
                    Self::integer_test(1, *operator),
                    *operator == IfOp::Ne,
                ];
                if negated {
                    actual.iter_mut().for_each(|value| *value = !*value);
                }
                if actual == expected {
                    return Some(ComparisonTest {
                        operator: *operator,
                        negated,
                    });
                }
            }
        }
        None
    }

    fn integer_test(value: i32, operator: IfOp) -> bool {
        match operator {
            IfOp::Eq => value == 0,
            IfOp::Ne => value != 0,
            IfOp::Lt => value < 0,
            IfOp::Ge => value >= 0,
            IfOp::Gt => value > 0,
            IfOp::Le => value <= 0,
        }
    }
}

struct GenericCast<'a> {
    target: &'a KotlinType,
    erased: &'a KotlinType,
    erased_bridge: bool,
}

impl<'a> GenericCast<'a> {
    fn new(target: &'a KotlinType, erased: &'a KotlinType) -> Self {
        Self {
            target,
            erased,
            erased_bridge: false,
        }
    }

    fn with_erased_bridge(mut self, required: bool) -> Self {
        self.erased_bridge = required;
        self
    }

    fn is_parameterized(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Class(class) => class
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_empty()),
            KotlinType::Array(element) => Self::is_parameterized(element),
            KotlinType::Primitive(_) | KotlinType::Variable(_) => false,
        }
    }

    fn has_generic_evidence(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Variable(_) => true,
            KotlinType::Array(element) => Self::has_generic_evidence(element),
            KotlinType::Class(class) => class
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_empty()),
            KotlinType::Primitive(_) => false,
        }
    }

    fn has_wildcard(ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Array(element) => Self::has_wildcard(element),
            KotlinType::Class(class) => class.segments.iter().any(|segment| {
                segment.arguments.iter().any(|argument| match argument {
                    KotlinTypeArgument::Any
                    | KotlinTypeArgument::Extends(_)
                    | KotlinTypeArgument::Super(_) => true,
                    KotlinTypeArgument::Exact(ty) => Self::has_wildcard(ty),
                })
            }),
            KotlinType::Primitive(_) | KotlinType::Variable(_) => false,
        }
    }

    fn lower(self, expression: KotlinExpr) -> KotlinExpr {
        let value = if self.erased_bridge
            && !matches!(&expression, KotlinExpr::Cast { ty, .. } if ty == self.erased)
        {
            KotlinExpr::Cast {
                ty: self.erased.clone(),
                value: Box::new(expression),
            }
        } else {
            expression
        };
        if matches!(&value, KotlinExpr::Cast { ty, .. } if ty == self.target) {
            value
        } else {
            KotlinExpr::Cast {
                ty: self.target.clone(),
                value: Box::new(value),
            }
        }
    }
}

#[derive(Clone)]
pub struct DexKotlinDialect {
    names: BTreeMap<SourceVariable, KotlinIdentifier>,
    source_names: BTreeMap<u32, KotlinIdentifier>,
    binding_types: KotlinBindingTypes,
    source_variable_definition_types: BTreeMap<u32, KotlinType>,
    source_value_definition_types: BTreeMap<crate::ir::analysis::SsaVar, KotlinType>,
    source_variable_types: BTreeMap<u32, KotlinType>,
    source_value_types: BTreeMap<crate::ir::analysis::SsaVar, KotlinType>,
    source_variable_requirements: BTreeMap<u32, KotlinType>,
    source_value_requirements: BTreeMap<crate::ir::analysis::SsaVar, KotlinType>,
    primitive_expression_types: RefCell<BTreeMap<InstructionId, Option<PrimitiveType>>>,
    source_field_types: Arc<BTreeMap<FieldReference, KotlinType>>,
    generic_fields: Arc<BTreeMap<FieldReference, GenericFieldContract>>,
    source_object_types: Arc<BTreeMap<ArgType, KotlinType>>,
    generic_methods: Arc<BTreeMap<MethodReference, GenericMethodContract>>,
    method_nullability: Arc<BTreeMap<MethodReference, KotlinMethodNullability>>,
    extension_receivers: Arc<BTreeMap<MethodReference, usize>>,
    default_calls: Arc<BTreeMap<MethodReference, KotlinDefaultCallContract>>,
    vararg_parameters: Arc<BTreeMap<MethodReference, BTreeSet<usize>>>,
    platform_symbols: Option<Arc<crate::platform_symbols::PlatformSymbolSet>>,
    non_null_fields: Arc<std::collections::BTreeSet<FieldReference>>,
    singleton_types: Arc<std::collections::BTreeSet<ArgType>>,
    singleton_instances: Arc<std::collections::BTreeSet<FieldReference>>,
    generic_type_projection: Option<Arc<dyn GenericTypeProjection>>,
    declared: BTreeSet<KotlinIdentifier>,
    locals: BTreeMap<KotlinIdentifier, KotlinType>,
    current_type: Option<ArgType>,
    source_current_type: Option<KotlinType>,
    source_super_type: Option<KotlinType>,
    return_type: Option<ArgType>,
    source_return_type: Option<KotlinType>,
    source_type_erasures: BTreeMap<KotlinIdentifier, ArgType>,
    source_type_bounds: BTreeMap<KotlinIdentifier, KotlinType>,
    generic_throw_types: Vec<KotlinSourceErasure>,
    this_code_var: Option<u32>,
    types: SourceTypeEnvironment,
    source_types: BTreeMap<ArgType, KotlinType>,
    inline_declarations: BTreeSet<SourceVariable>,
    catch_storage: BTreeSet<SourceVariable>,
    name_scope: KotlinNameScope,
    member_names: Arc<KotlinMemberNames>,
    outer_instance: Option<OuterInstanceBinding>,
    outer_instance_fields: BTreeMap<FieldReference, KotlinType>,
    observer: Arc<dyn crate::ir::AnalysisObserver>,
}

#[derive(Debug, Clone, Default)]
struct KotlinBindingTypes {
    variables: BTreeMap<u32, KotlinType>,
    names: BTreeMap<KotlinIdentifier, KotlinType>,
}

impl KotlinBindingTypes {
    fn bind_variable(&mut self, variable: u32, name: Option<&KotlinIdentifier>, ty: KotlinType) {
        self.variables.insert(variable, ty.clone());
        if let Some(name) = name {
            self.names.insert(name.clone(), ty);
        }
    }

    fn bind_name(&mut self, name: KotlinIdentifier, ty: KotlinType) {
        self.names.insert(name, ty);
    }

    fn name_type(&self, name: &KotlinIdentifier) -> Option<&KotlinType> {
        self.names.get(name)
    }

    fn variable_type(&self, variable: u32) -> Option<&KotlinType> {
        self.variables.get(&variable)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KotlinSourceErasure {
    source: KotlinType,
    erased: ArgType,
}

impl KotlinSourceErasure {
    pub fn new(source: KotlinType, erased: ArgType) -> Self {
        Self { source, erased }
    }
}

#[derive(Debug, Clone)]
pub struct OuterInstanceBinding {
    outer_type: ArgType,
    field: Option<FieldReference>,
    constructor_parameter: Option<u32>,
}

impl OuterInstanceBinding {
    pub fn new(
        outer_type: ArgType,
        field: Option<FieldReference>,
        constructor_parameter: Option<u32>,
    ) -> Self {
        Self {
            outer_type,
            field,
            constructor_parameter,
        }
    }

    pub(crate) fn outer_type(&self) -> &ArgType {
        &self.outer_type
    }

    pub(crate) fn field(&self) -> Option<&FieldReference> {
        self.field.as_ref()
    }
}

impl DexKotlinDialect {
    pub fn new(
        is_static: bool,
        this_code_var: Option<u32>,
        parameter_code_vars: &[Option<u32>],
        parameter_names: &[KotlinIdentifier],
        types: &SourceTypeEnvironment,
        source_types: BTreeMap<ArgType, KotlinType>,
        member_names: Arc<KotlinMemberNames>,
    ) -> Result<Self, KotlinLoweringError> {
        if parameter_code_vars.len() != parameter_names.len() {
            return Err(KotlinLoweringError::ParameterBindingArity {
                variables: parameter_code_vars.len(),
                names: parameter_names.len(),
            });
        }
        let mut values = Self {
            names: BTreeMap::new(),
            source_names: BTreeMap::new(),
            binding_types: KotlinBindingTypes::default(),
            source_variable_definition_types: BTreeMap::new(),
            source_value_definition_types: BTreeMap::new(),
            source_variable_types: BTreeMap::new(),
            source_value_types: BTreeMap::new(),
            source_variable_requirements: BTreeMap::new(),
            source_value_requirements: BTreeMap::new(),
            primitive_expression_types: RefCell::new(BTreeMap::new()),
            source_field_types: Arc::new(BTreeMap::new()),
            generic_fields: Arc::new(BTreeMap::new()),
            source_object_types: Arc::new(BTreeMap::new()),
            generic_methods: Arc::new(BTreeMap::new()),
            method_nullability: Arc::new(BTreeMap::new()),
            extension_receivers: Arc::new(BTreeMap::new()),
            default_calls: Arc::new(BTreeMap::new()),
            vararg_parameters: Arc::new(BTreeMap::new()),
            platform_symbols: None,
            non_null_fields: Default::default(),
            singleton_types: Default::default(),
            singleton_instances: Default::default(),
            generic_type_projection: None,
            declared: BTreeSet::new(),
            locals: BTreeMap::new(),
            current_type: None,
            source_current_type: None,
            source_super_type: None,
            return_type: None,
            source_return_type: None,
            source_type_erasures: BTreeMap::new(),
            source_type_bounds: BTreeMap::new(),
            generic_throw_types: Vec::new(),
            this_code_var,
            types: types.clone(),
            source_types,
            inline_declarations: BTreeSet::new(),
            catch_storage: BTreeSet::new(),
            name_scope: KotlinNameScope::default(),
            member_names,
            outer_instance: None,
            outer_instance_fields: BTreeMap::new(),
            observer: Arc::new(crate::ir::NullAnalysisObserver),
        };
        if !is_static && this_code_var.is_none() {
            return Err(KotlinLoweringError::MissingThisSourceVariable);
        }
        for (index, (code_var, name)) in parameter_code_vars.iter().zip(parameter_names).enumerate()
        {
            let code_var =
                (*code_var).ok_or(KotlinLoweringError::MissingParameterSourceVariable(index))?;
            values
                .names
                .insert(SourceVariable::new(code_var), name.clone());
            values.source_names.insert(code_var, name.clone());
            values.declared.insert(name.clone());
            values.name_scope.reserve(name.clone());
        }
        Ok(values)
    }

    pub fn with_current_type(mut self, current_type: Option<ArgType>) -> Self {
        self.current_type = current_type;
        self
    }

    pub fn with_source_current_type(mut self, current_type: Option<KotlinType>) -> Self {
        self.source_current_type = current_type;
        self
    }

    pub fn with_source_super_type(mut self, super_type: Option<KotlinType>) -> Self {
        self.source_super_type = super_type;
        self
    }

    pub fn with_source_field_types(
        mut self,
        types: Arc<BTreeMap<FieldReference, KotlinType>>,
    ) -> Self {
        self.source_field_types = types;
        self
    }

    pub fn with_generic_fields(
        mut self,
        fields: Arc<BTreeMap<FieldReference, GenericFieldContract>>,
    ) -> Self {
        self.generic_fields = fields;
        self
    }

    pub fn with_generic_methods(
        mut self,
        methods: Arc<BTreeMap<MethodReference, GenericMethodContract>>,
    ) -> Self {
        self.generic_methods = methods;
        self
    }

    /// Declares the Kotlin classes that have exactly one instance.
    pub fn with_singleton_types(mut self, types: Arc<std::collections::BTreeSet<ArgType>>) -> Self {
        self.singleton_types = types;
        self
    }

    pub fn with_non_null_fields(
        mut self,
        fields: Arc<std::collections::BTreeSet<FieldReference>>,
    ) -> Self {
        self.non_null_fields = fields;
        self
    }

    pub fn with_singleton_instances(
        mut self,
        instances: Arc<std::collections::BTreeSet<FieldReference>>,
    ) -> Self {
        self.singleton_instances = instances;
        self
    }

    pub fn with_method_nullability(
        mut self,
        nullability: Arc<BTreeMap<MethodReference, KotlinMethodNullability>>,
    ) -> Self {
        self.method_nullability = nullability;
        self
    }

    pub fn with_extension_receivers(
        mut self,
        receivers: Arc<BTreeMap<MethodReference, usize>>,
    ) -> Self {
        self.extension_receivers = receivers;
        self
    }

    pub fn with_default_calls(
        mut self,
        calls: Arc<BTreeMap<MethodReference, KotlinDefaultCallContract>>,
    ) -> Self {
        self.default_calls = calls;
        self
    }

    pub fn with_vararg_parameters(
        mut self,
        parameters: Arc<BTreeMap<MethodReference, BTreeSet<usize>>>,
    ) -> Self {
        self.vararg_parameters = parameters;
        self
    }

    pub fn with_platform_symbols(
        mut self,
        symbols: Option<Arc<crate::platform_symbols::PlatformSymbolSet>>,
    ) -> Self {
        self.platform_symbols = symbols;
        self
    }

    pub fn with_source_object_types(mut self, types: Arc<BTreeMap<ArgType, KotlinType>>) -> Self {
        self.source_object_types = types;
        self
    }

    pub(crate) fn with_generic_type_projection(
        mut self,
        projection: Arc<dyn GenericTypeProjection>,
    ) -> Self {
        self.generic_type_projection = Some(projection);
        self
    }

    pub fn with_source_parameter_types(
        mut self,
        code_vars: &[Option<u32>],
        types: &[Option<KotlinType>],
    ) -> Self {
        for (code_var, ty) in code_vars
            .iter()
            .zip(types)
            .filter_map(|(code_var, ty)| (*code_var).zip(ty.clone()))
        {
            self.binding_types.bind_variable(
                code_var,
                self.source_names.get(&code_var),
                ty.clone(),
            );
            self.source_variable_types.insert(code_var, ty);
        }
        self
    }

    pub fn with_return_type(mut self, return_type: Option<ArgType>) -> Self {
        self.return_type = return_type;
        self
    }

    pub fn with_source_return_type(mut self, return_type: Option<KotlinType>) -> Self {
        self.source_return_type = return_type;
        self
    }

    pub fn with_source_type_erasures(
        mut self,
        erasures: BTreeMap<KotlinIdentifier, ArgType>,
    ) -> Self {
        self.source_type_erasures = erasures;
        self
    }

    pub fn with_source_type_bounds(
        mut self,
        bounds: BTreeMap<KotlinIdentifier, KotlinType>,
    ) -> Self {
        self.source_type_bounds = bounds;
        self
    }

    pub fn with_generic_throw_types(mut self, types: Vec<KotlinSourceErasure>) -> Self {
        self.generic_throw_types = types;
        self
    }

    pub fn with_outer_instance(mut self, outer_instance: Option<OuterInstanceBinding>) -> Self {
        self.outer_instance = outer_instance;
        self
    }

    pub fn with_outer_instance_fields(
        mut self,
        fields: BTreeMap<FieldReference, KotlinType>,
    ) -> Self {
        self.outer_instance_fields = fields;
        self
    }

    pub fn with_reserved_local_names(
        mut self,
        names: impl IntoIterator<Item = KotlinIdentifier>,
    ) -> Self {
        for name in names {
            self.name_scope.reserve(name);
        }
        self
    }

    pub fn with_analysis_observer(
        mut self,
        observer: Arc<dyn crate::ir::AnalysisObserver>,
    ) -> Self {
        self.observer = observer;
        self
    }

    pub fn with_semantic_names(mut self, names: BTreeMap<u32, KotlinIdentifier>) -> Self {
        for (variable, name) in names {
            if variable == self.this_code_var.unwrap_or(u32::MAX)
                || self.source_names.contains_key(&variable)
            {
                continue;
            }
            let name = self.name_scope.claim(name);
            self.source_names.insert(variable, name);
        }
        self
    }

    fn is_this(&self, argument: &SemanticExpression) -> bool {
        argument
            .as_register()
            .and_then(|register| register.code_var)
            == self.this_code_var
            && self.this_code_var.is_some()
    }

    fn outer_instance(
        &self,
        field: &FieldReference,
        owner: &SemanticExpression,
    ) -> Option<&OuterInstanceBinding> {
        self.is_this(owner)
            .then(|| self.outer_instance.as_ref())
            .flatten()
            .filter(|binding| binding.field.as_ref() == Some(field))
    }

    fn is_enclosing_instance_receiver(
        &self,
        receiver: &SemanticExpression,
        expected_owner: &ArgType,
    ) -> bool {
        let Some(operation) = receiver
            .as_operation()
            .filter(|operation| operation.insn_type == InsnType::Iget)
        else {
            return false;
        };
        let Some(MemberReference::Field(field)) = operation.payload.reference.as_ref() else {
            return false;
        };
        let Some(binding) = self.outer_instance.as_ref() else {
            return false;
        };
        binding.outer_type == *expected_owner
            && binding.field.as_ref() == Some(field)
            && operation
                .operands()
                .first()
                .is_some_and(|owner| self.is_this(owner))
    }

    fn register_name(
        &mut self,
        register: &RegisterArg,
    ) -> Result<KotlinIdentifier, KotlinLoweringError> {
        if register.code_var == self.this_code_var && self.this_code_var.is_some() {
            return Err(KotlinLoweringError::InvalidThisLvalue);
        }
        if let Some(name) = register
            .code_var
            .and_then(|code_var| self.source_names.get(&code_var))
        {
            return Ok(name.clone());
        }
        let key = SourceVariable::of(register)?;
        if let Some(name) = self.names.get(&key) {
            return Ok(name.clone());
        }
        let name = self
            .name_scope
            .claim(KotlinIdentifier::from_dex(&format!("v{}", key.raw())));
        self.names.insert(key, name.clone());
        Ok(name)
    }

    fn arg(&mut self, arg: &SemanticExpression) -> Result<KotlinExpr, KotlinLoweringError> {
        if matches!(arg, SemanticExpression::Select { .. })
            && self.expression_type(arg)? == &ArgType::BOOLEAN
        {
            return self.boolean_value(arg);
        }
        match arg {
            SemanticExpression::Register(register)
                if register.code_var == self.this_code_var && self.this_code_var.is_some() =>
            {
                Ok(KotlinExpr::This)
            }
            SemanticExpression::Register(register)
                if self.outer_instance.as_ref().is_some_and(|binding| {
                    binding.constructor_parameter == register.code_var
                        && binding.constructor_parameter.is_some()
                }) =>
            {
                let outer = self
                    .outer_instance
                    .as_ref()
                    .map(|binding| binding.outer_type.clone())
                    .ok_or_else(|| Self::missing_reference())?;
                Ok(KotlinExpr::QualifiedThis(self.source_type(&outer)?))
            }
            SemanticExpression::Register(register) => {
                Ok(KotlinExpr::Name(self.register_name(register)?))
            }
            SemanticExpression::Literal(literal) => {
                Ok(KotlinExpr::Literal(Self::literal(literal)?))
            }
            SemanticExpression::Operation(operation) => self.insn_expr(operation, None, None),
            SemanticExpression::Select {
                condition,
                when_true,
                when_false,
            } => self.select_value(condition, when_true, when_false, None),
        }
    }

    fn arg_as(
        &mut self,
        arg: &SemanticExpression,
        expected: &ArgType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let actual = self.source_primitive_type(arg);
        if expected == &ArgType::BOOLEAN && matches!(arg, SemanticExpression::Select { .. }) {
            return self.boolean_value(arg);
        }
        if let SemanticExpression::Select {
            condition,
            when_true,
            when_false,
        } = arg
        {
            return self.select_value(condition, when_true, when_false, Some(expected));
        }
        if expected.is_reference() {
            let invocation_requires_conversion = arg.as_operation().is_some_and(|operation| {
                if operation.insn_type != InsnType::Invoke {
                    return false;
                }
                let Some(actual) = Self::method(operation.payload.reference.as_ref())
                    .ok()
                    .map(|method| &method.descriptor.return_type)
                    .filter(|actual| actual.is_reference())
                else {
                    return false;
                };
                let object = ArgType::object("java/lang/Object");
                actual != expected
                    && (actual == &object
                        || !self
                            .generic_type_projection
                            .as_deref()
                            .is_some_and(|projection| projection.is_subtype(actual, expected)))
            });
            if invocation_requires_conversion {
                let source = self.source_type(expected)?.into_star_projection();
                return self.arg_as_source_target(arg, expected, &source);
            }
        }
        let expression = self.arg(arg)?;
        Ok(self.coerce_typed(expression, actual, expected))
    }

    fn arg_as_field(
        &mut self,
        arg: &SemanticExpression,
        field: &FieldReference,
        receiver: Option<&SemanticExpression>,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let source_type = self
            .source_field_type(field, receiver)
            .or_else(|| self.source_type(&field.field_type).ok());
        match source_type.as_ref() {
            Some(source_type) => self.arg_as_source_target(arg, &field.field_type, source_type),
            None => self.arg_as(arg, &field.field_type),
        }
    }

    fn arg_as_source_target(
        &mut self,
        value: &SemanticExpression,
        erased: &ArgType,
        source: &KotlinType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let actual = self.cast_source_type(value);
        let expression = self.arg_as_with_source_type(value, erased, source)?;
        if matches!(source, KotlinType::Primitive(_)) {
            return Ok(expression);
        }
        let erased_type = self.source_type(erased)?.into_star_projection();
        let emitted_type = match &expression {
            KotlinExpr::Name(name) => self.binding_types.name_type(name).cloned(),
            KotlinExpr::Cast { ty, .. } => Some(ty.clone()),
            KotlinExpr::New {
                ty, target_type, ..
            } => target_type
                .clone()
                .filter(|target| Self::same_erasure(target, ty))
                .or_else(|| Some(ty.clone())),
            KotlinExpr::NewArray { element_type, .. } => {
                Some(KotlinType::array(element_type.clone()))
            }
            _ => None,
        };
        let emitted_requires_parameterized_binding = GenericCast::is_parameterized(source)
            && emitted_type.as_ref().is_some_and(|emitted| {
                Self::same_erasure(emitted, source) && self.is_raw_generic_type(emitted)
            });
        if self.select_requires_target_binding(value, source) {
            return Ok(GenericCast::new(source, &erased_type)
                .with_erased_bridge(true)
                .lower(expression));
        }
        // The rendered expression's static Kotlin type is the conversion source.
        // It may carry generic evidence recovered after DEX type erasure (for
        // example, `new ArrayList<T>()`) that is intentionally absent from the
        // underlying register type.
        let conversion_type = emitted_type.as_ref().or(actual.as_ref());
        let accepts_target = !emitted_requires_parameterized_binding
            && (conversion_type.is_some_and(|actual| self.source_assignable_to(actual, source))
                || (emitted_type.is_none() && self.accepts_target_type(value, source)));
        let actual_is_incompatible = emitted_requires_parameterized_binding
            || conversion_type.is_some_and(|actual| !self.source_assignable_to(actual, source));
        if (!Self::source_return_requires_cast(source, &erased_type) && !actual_is_incompatible)
            || matches!(expression, KotlinExpr::Literal(KotlinLiteral::Null))
            || matches!(&expression, KotlinExpr::Cast { ty, .. } if ty == source)
            || accepts_target
        {
            return Ok(expression);
        }
        Ok(self.source_cast(expression, value, actual.as_ref(), source, &erased_type))
    }

    fn select_requires_target_binding(
        &self,
        value: &SemanticExpression,
        target: &KotlinType,
    ) -> bool {
        let SemanticExpression::Select {
            when_true,
            when_false,
            ..
        } = value
        else {
            return false;
        };
        if !GenericCast::has_generic_evidence(target) {
            return false;
        }
        let left = self.source_expression_type(when_true);
        let right = self.source_expression_type(when_false);
        left.zip(right).is_some_and(|(left, right)| left != right)
    }

    fn definition_value(
        &mut self,
        result: &RegisterArg,
        value: &SemanticExpression,
        erased: &ArgType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let name = self.register_name(result)?;
        let source = self
            .binding_types
            .name_type(&name)
            .cloned()
            .or_else(|| self.source_definition_type(result));
        match source {
            Some(source) => self.arg_as_source_target(value, erased, &source),
            None => self.semantic_value(value, erased),
        }
    }

    fn select_value(
        &mut self,
        condition: &SemanticPredicate,
        when_true: &SemanticExpression,
        when_false: &SemanticExpression,
        expected: Option<&ArgType>,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let when_true = match expected {
            Some(expected) => self.arg_as(when_true, expected)?,
            None => self.arg(when_true)?,
        };
        let when_false = match expected {
            Some(expected) => self.arg_as(when_false, expected)?,
            None => self.arg(when_false)?,
        };
        self.select_expression(condition, when_true, when_false)
    }

    fn select_value_with_source_type(
        &mut self,
        condition: &SemanticPredicate,
        when_true: &SemanticExpression,
        when_false: &SemanticExpression,
        expected: &KotlinType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let erased = self
            .source_erasure(expected)
            .ok_or_else(|| Self::missing_reference())?;
        self.select_value_with_source_target(condition, when_true, when_false, &erased, expected)
    }

    fn select_value_with_source_target(
        &mut self,
        condition: &SemanticPredicate,
        when_true: &SemanticExpression,
        when_false: &SemanticExpression,
        erased: &ArgType,
        expected: &KotlinType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let when_true = self.select_branch_with_source_type(when_true, &erased, expected)?;
        let when_false = self.select_branch_with_source_type(when_false, &erased, expected)?;
        self.select_expression(condition, when_true, when_false)
    }

    fn select_branch_with_source_type(
        &mut self,
        branch: &SemanticExpression,
        erased: &ArgType,
        expected: &KotlinType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let actual = self.intrinsic_source_type(branch);
        let expression = self.arg_as_source_target(branch, erased, expected)?;
        let needs_target_binding = actual.as_ref().is_some_and(|actual| {
            actual != expected
                && GenericCast::has_generic_evidence(expected)
                && self.source_assignable_to(actual, expected)
        }) || (GenericCast::has_wildcard(expected)
            && matches!(
                branch,
                SemanticExpression::Operation(_) | SemanticExpression::Select { .. }
            ));
        if needs_target_binding
            && !matches!(&expression, KotlinExpr::Cast { ty, .. } if ty == expected)
        {
            Ok(KotlinExpr::Cast {
                ty: expected.clone(),
                value: Box::new(expression),
            })
        } else {
            Ok(expression)
        }
    }

    fn select_expression(
        &mut self,
        condition: &SemanticPredicate,
        mut when_true: KotlinExpr,
        mut when_false: KotlinExpr,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let condition_is_pure = condition.effects().is_pure();
        let mut positive = self.predicate(condition)?;
        let negative = self.predicate(&condition.clone().negate())?;
        if condition_is_pure && when_true == when_false {
            return Ok(when_true);
        }
        if negative.cost() < positive.cost() {
            positive = negative;
            std::mem::swap(&mut when_true, &mut when_false);
        }
        Ok(KotlinExpr::Conditional {
            condition: Box::new(positive),
            when_true: Box::new(when_true),
            when_false: Box::new(when_false),
        })
    }

    fn coerce(&self, expression: KotlinExpr, expected: &ArgType) -> KotlinExpr {
        match (expected, expression) {
            (
                ArgType::Primitive(PrimitiveType::Boolean),
                KotlinExpr::Literal(KotlinLiteral::Integer(value)),
            ) => KotlinExpr::Literal(KotlinLiteral::Boolean(value != 0)),
            (
                ArgType::Primitive(PrimitiveType::Long),
                KotlinExpr::Literal(KotlinLiteral::Integer(value)),
            ) => KotlinExpr::Literal(KotlinLiteral::Long(i64::from(value))),
            (
                ArgType::Primitive(PrimitiveType::Char),
                KotlinExpr::Literal(KotlinLiteral::Integer(value)),
            ) => KotlinExpr::Literal(KotlinLiteral::Character(value as u16)),
            (
                ArgType::Primitive(primitive @ (PrimitiveType::Byte | PrimitiveType::Short)),
                expression @ KotlinExpr::Literal(KotlinLiteral::Integer(_)),
            ) => KotlinExpr::Cast {
                ty: KotlinType::Primitive(match primitive {
                    PrimitiveType::Byte => KotlinPrimitiveType::Byte,
                    PrimitiveType::Short => KotlinPrimitiveType::Short,
                    _ => unreachable!(),
                }),
                value: Box::new(expression),
            },
            (
                ArgType::Primitive(PrimitiveType::Float),
                KotlinExpr::Literal(KotlinLiteral::Integer(value)),
            ) => KotlinExpr::Literal(KotlinLiteral::Float(f32::from_bits(value as u32))),
            (
                ArgType::Primitive(PrimitiveType::Double),
                KotlinExpr::Literal(KotlinLiteral::Long(value)),
            ) => KotlinExpr::Literal(KotlinLiteral::Double(f64::from_bits(value as u64))),
            (
                ArgType::Object(_) | ArgType::Array(_),
                KotlinExpr::Literal(KotlinLiteral::Integer(0)),
            ) => KotlinExpr::Literal(KotlinLiteral::Null),
            (
                expected,
                KotlinExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                },
            ) => KotlinExpr::Conditional {
                condition,
                when_true: Box::new(self.coerce(*when_true, expected)),
                when_false: Box::new(self.coerce(*when_false, expected)),
            },
            (_, expression) => expression,
        }
    }

    fn coerce_typed(
        &self,
        expression: KotlinExpr,
        actual: Option<PrimitiveType>,
        expected: &ArgType,
    ) -> KotlinExpr {
        match (actual, expected) {
            (
                Some(PrimitiveType::Boolean),
                ArgType::Primitive(
                    primitive @ (PrimitiveType::Byte
                    | PrimitiveType::Short
                    | PrimitiveType::Char
                    | PrimitiveType::Int
                    | PrimitiveType::Long),
                ),
            ) => {
                let materialized = KotlinExpr::Conditional {
                    condition: Box::new(self.coerce(expression, &ArgType::BOOLEAN)),
                    when_true: Box::new(Self::integral_literal(*primitive, 1)),
                    when_false: Box::new(Self::integral_literal(*primitive, 0)),
                };
                if matches!(
                    primitive,
                    PrimitiveType::Byte | PrimitiveType::Short | PrimitiveType::Char
                ) {
                    KotlinExpr::Cast {
                        ty: KotlinType::Primitive(Self::narrowing_primitive(*primitive)),
                        value: Box::new(materialized),
                    }
                } else {
                    materialized
                }
            }
            (
                Some(
                    actual @ (PrimitiveType::Byte
                    | PrimitiveType::Short
                    | PrimitiveType::Char
                    | PrimitiveType::Int
                    | PrimitiveType::Long),
                ),
                ArgType::Primitive(PrimitiveType::Boolean),
            ) => match expression {
                KotlinExpr::Literal(KotlinLiteral::Integer(value)) => {
                    KotlinExpr::Literal(KotlinLiteral::Boolean(value != 0))
                }
                KotlinExpr::Literal(KotlinLiteral::Long(value)) => {
                    KotlinExpr::Literal(KotlinLiteral::Boolean(value != 0))
                }
                expression => KotlinExpr::Binary {
                    left: Box::new(expression),
                    op: KotlinBinaryOp::NotEqual,
                    right: Box::new(Self::integral_literal(actual, 0)),
                },
            },
            (Some(actual), ArgType::Primitive(expected))
                if Self::requires_narrowing_conversion(actual, *expected)
                    && !matches!(&expression, KotlinExpr::Literal(_)) =>
            {
                KotlinExpr::Cast {
                    ty: KotlinType::Primitive(Self::narrowing_primitive(*expected)),
                    value: Box::new(expression),
                }
            }
            (Some(actual), ArgType::Primitive(expected))
                if actual != *expected
                    && Self::is_numeric_primitive(actual)
                    && Self::is_numeric_primitive(*expected) =>
            {
                KotlinExpr::Cast {
                    ty: KotlinType::Primitive(Self::source_primitive(*expected)),
                    value: Box::new(expression),
                }
            }
            _ => self.coerce(expression, expected),
        }
    }

    fn is_numeric_primitive(primitive: PrimitiveType) -> bool {
        matches!(
            primitive,
            PrimitiveType::Byte
                | PrimitiveType::Short
                | PrimitiveType::Char
                | PrimitiveType::Int
                | PrimitiveType::Long
                | PrimitiveType::Float
                | PrimitiveType::Double
        )
    }

    fn source_primitive(primitive: PrimitiveType) -> KotlinPrimitiveType {
        match primitive {
            PrimitiveType::Byte => KotlinPrimitiveType::Byte,
            PrimitiveType::Short => KotlinPrimitiveType::Short,
            PrimitiveType::Char => KotlinPrimitiveType::Char,
            PrimitiveType::Int => KotlinPrimitiveType::Int,
            PrimitiveType::Long => KotlinPrimitiveType::Long,
            PrimitiveType::Float => KotlinPrimitiveType::Float,
            PrimitiveType::Double => KotlinPrimitiveType::Double,
            PrimitiveType::Boolean => KotlinPrimitiveType::Boolean,
            PrimitiveType::Void => KotlinPrimitiveType::Void,
            PrimitiveType::Object | PrimitiveType::Array => {
                unreachable!("reference pseudo-primitives are not Kotlin primitives")
            }
        }
    }

    fn requires_narrowing_conversion(actual: PrimitiveType, expected: PrimitiveType) -> bool {
        match expected {
            PrimitiveType::Byte => actual != PrimitiveType::Byte,
            PrimitiveType::Short => !matches!(actual, PrimitiveType::Byte | PrimitiveType::Short),
            PrimitiveType::Char => actual != PrimitiveType::Char,
            _ => false,
        }
    }

    fn narrowing_primitive(primitive: PrimitiveType) -> KotlinPrimitiveType {
        match primitive {
            PrimitiveType::Byte => KotlinPrimitiveType::Byte,
            PrimitiveType::Short => KotlinPrimitiveType::Short,
            PrimitiveType::Char => KotlinPrimitiveType::Char,
            _ => unreachable!("narrowing conversion only targets byte, short, or char"),
        }
    }

    fn integral_literal(primitive: PrimitiveType, value: i64) -> KotlinExpr {
        match primitive {
            PrimitiveType::Long => KotlinExpr::Literal(KotlinLiteral::Long(value)),
            PrimitiveType::Byte
            | PrimitiveType::Short
            | PrimitiveType::Char
            | PrimitiveType::Int => KotlinExpr::Literal(KotlinLiteral::Integer(value as i32)),
            _ => unreachable!("integral coercion only accepts integral primitive types"),
        }
    }

    fn source_primitive_type(&self, expression: &SemanticExpression) -> Option<PrimitiveType> {
        let identity = expression
            .as_operation()
            .map(|operation| operation.id)
            .filter(|identity| identity.is_valid());
        if let Some(cached) = identity.and_then(|identity| {
            self.primitive_expression_types
                .borrow()
                .get(&identity)
                .copied()
        }) {
            return cached;
        }
        let primitive = self.infer_source_primitive_type(expression);
        if let Some(identity) = identity {
            self.primitive_expression_types
                .borrow_mut()
                .insert(identity, primitive);
        }
        primitive
    }

    fn infer_source_primitive_type(
        &self,
        expression: &SemanticExpression,
    ) -> Option<PrimitiveType> {
        let mut expression = expression;
        loop {
            if Self::is_boolean_materialization(expression) {
                return Some(PrimitiveType::Boolean);
            }
            let Some(operation) = expression.as_operation() else {
                break;
            };
            if operation.insn_type == InsnType::Move && operation.operands().len() == 1 {
                expression = &operation.operands()[0];
                continue;
            }
            if let Some(MemberReference::Method(method)) = operation.payload.reference.as_ref() {
                if let ArgType::Primitive(primitive) = &method.descriptor.return_type {
                    return Some(*primitive);
                }
            }
            if self.arithmetic_is_boolean(operation) {
                return Some(PrimitiveType::Boolean);
            }
            if operation.insn_type == InsnType::Arith {
                let [left, right] = operation.operands() else {
                    return None;
                };
                if let Some(primitive) = PrimitiveOperationDomain::arithmetic_result(
                    operation.payload.arith_op?,
                    self.source_primitive_type(left)?,
                    self.source_primitive_type(right)?,
                ) {
                    return Some(primitive);
                }
            }
            if let Some(primitive) = Self::intrinsic_primitive_type(expression) {
                return Some(primitive);
            }
            if let Some(KotlinType::Primitive(primitive)) = operation
                .result
                .as_ref()
                .and_then(|result| self.source_register_type(result))
            {
                return Some(Self::erased_primitive(*primitive));
            }
            if operation.insn_type == InsnType::Arith {
                if let Some(ArgType::Primitive(primitive)) = operation
                    .result
                    .as_ref()
                    .and_then(|result| self.types.register_type(result).ok())
                {
                    return Some(*primitive);
                }
            }
            if let Some(ArgType::Primitive(primitive)) =
                operation.result.as_ref().map(|result| &result.ty)
            {
                return Some(*primitive);
            }
            break;
        }
        if let Some(ty) = expression
            .as_register()
            .and_then(|register| register.code_var)
            .and_then(|code_var| self.source_variable_types.get(&code_var))
        {
            return match ty {
                KotlinType::Primitive(primitive) => Some(Self::erased_primitive(*primitive)),
                KotlinType::Class(_) | KotlinType::Variable(_) | KotlinType::Array(_) => None,
            };
        }
        match self.expression_type(expression).ok()? {
            ArgType::Primitive(primitive) => Some(*primitive),
            ArgType::Object(_) | ArgType::Array(_) | ArgType::Unknown(_) => None,
        }
    }

    /// Returns the primitive domain carried by the value-producing operation
    /// itself. Unlike source-variable typing, this cannot be influenced by a
    /// different SSA definition that happened to reuse the same DEX register.
    fn intrinsic_primitive_type(expression: &SemanticExpression) -> Option<PrimitiveType> {
        match expression {
            SemanticExpression::Literal(literal) => literal.ty.as_primitive(),
            SemanticExpression::Operation(operation) => {
                if operation.insn_type == InsnType::Move && operation.operands().len() == 1 {
                    return Self::intrinsic_primitive_type(&operation.operands()[0]);
                }
                if operation.insn_type == InsnType::Const {
                    return operation
                        .operands()
                        .first()
                        .and_then(Self::intrinsic_primitive_type);
                }
                match operation.payload.reference.as_ref() {
                    Some(MemberReference::Method(method)) => {
                        return method.descriptor.return_type.as_primitive();
                    }
                    Some(MemberReference::Field(field))
                        if matches!(operation.insn_type, InsnType::Iget | InsnType::Sget) =>
                    {
                        return field.field_type.as_primitive();
                    }
                    _ => {}
                }
                operation
                    .payload
                    .cast_type
                    .as_ref()
                    .and_then(ArgType::as_primitive)
                    .or_else(|| {
                        operation
                            .result
                            .as_ref()
                            .and_then(|result| result.ty.as_primitive())
                    })
            }
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let when_true = Self::intrinsic_primitive_type(when_true)?;
                (Self::intrinsic_primitive_type(when_false) == Some(when_true)).then_some(when_true)
            }
            SemanticExpression::Register(_) => None,
        }
    }

    fn has_intrinsic_numeric_comparison_domain(
        &self,
        left: &SemanticExpression,
        right: &SemanticExpression,
    ) -> Result<bool, KotlinLoweringError> {
        if self.expression_type(left)?.is_reference() || self.expression_type(right)?.is_reference()
        {
            return Ok(false);
        }
        Ok([left, right].into_iter().any(|value| {
            Self::intrinsic_primitive_type(value)
                .is_some_and(|primitive| primitive != PrimitiveType::Boolean)
        }))
    }

    fn numeric_comparison_type(
        &self,
        left: &SemanticExpression,
        right: &SemanticExpression,
    ) -> Result<Option<ArgType>, KotlinLoweringError> {
        let primitive =
            |value: &SemanticExpression| -> Result<Option<PrimitiveType>, KotlinLoweringError> {
                Ok(self.source_primitive_type(value).or_else(|| {
                    self.expression_type(value)
                        .ok()
                        .and_then(ArgType::as_primitive)
                }))
            };
        let (Some(left), Some(right)) = (primitive(left)?, primitive(right)?) else {
            return Ok(None);
        };
        Ok(PrimitiveOperationDomain::binary_numeric_promotion(left, right).map(ArgType::Primitive))
    }

    fn arithmetic_is_boolean(&self, operation: &SemanticOperation) -> bool {
        operation.insn_type == InsnType::Arith
            && matches!(
                operation.payload.arith_op,
                Some(ArithOp::And | ArithOp::Or | ArithOp::Xor)
            )
            && operation.operands().len() == 2
            && operation.operands().iter().all(|operand| {
                matches!(Self::constant(operand), Some(0) | Some(1))
                    || self.source_primitive_type(operand) == Some(PrimitiveType::Boolean)
            })
    }

    fn erased_primitive(primitive: KotlinPrimitiveType) -> PrimitiveType {
        match primitive {
            KotlinPrimitiveType::Void => PrimitiveType::Void,
            KotlinPrimitiveType::Boolean => PrimitiveType::Boolean,
            KotlinPrimitiveType::Byte => PrimitiveType::Byte,
            KotlinPrimitiveType::Short => PrimitiveType::Short,
            KotlinPrimitiveType::Char => PrimitiveType::Char,
            KotlinPrimitiveType::Int => PrimitiveType::Int,
            KotlinPrimitiveType::Long => PrimitiveType::Long,
            KotlinPrimitiveType::Float => PrimitiveType::Float,
            KotlinPrimitiveType::Double => PrimitiveType::Double,
        }
    }

    fn source_return_requires_cast(source: &KotlinType, erased: &KotlinType) -> bool {
        source != erased && !matches!(source, KotlinType::Primitive(_))
    }

    fn source_cast(
        &self,
        expression: KotlinExpr,
        value: &SemanticExpression,
        actual: Option<&KotlinType>,
        target: &KotlinType,
        erased: &KotlinType,
    ) -> KotlinExpr {
        let existing_erased_bridge = matches!(&expression, KotlinExpr::Cast { ty, .. }
            if !GenericCast::is_parameterized(ty) && Self::same_erasure(ty, target));
        let target = if self.has_only_default_type_arguments(target) && !existing_erased_bridge {
            erased
        } else {
            target
        };
        let wildcard_erasure_bridge = GenericCast::has_wildcard(target)
            && actual.is_some_and(|actual| {
                let actual_erasure = self.source_erasure(actual);
                let target_erasure = self.source_erasure(target);
                !self.source_assignable_to(actual, target)
                    && (self.is_raw_generic_type(actual)
                        || actual_erasure
                            .as_ref()
                            .zip(target_erasure.as_ref())
                            .is_some_and(|(actual, target)| {
                                actual == target
                                    || self.generic_type_projection.as_deref().is_some_and(
                                        |projection| projection.is_subtype(actual, target),
                                    )
                            }))
            });
        if wildcard_erasure_bridge {
            return KotlinExpr::Cast {
                ty: erased.clone(),
                value: Box::new(expression),
            };
        }
        let erased_bridge = GenericCast::is_parameterized(target)
            && match actual {
                Some(actual) => !self.source_assignable_to(actual, target),
                None => self.expression_declares_parameterized_type(value),
            };
        GenericCast::new(target, erased)
            .with_erased_bridge(erased_bridge)
            .lower(expression)
    }

    fn comparison_arg(
        &mut self,
        arg: &SemanticExpression,
        opposite: &SemanticExpression,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        if Self::constant(opposite) == Some(0) {
            if let Ok(expected) = self.expression_type(arg).cloned() {
                if expected.is_reference() {
                    return self.arg_as(arg, &expected);
                }
            }
        }
        if let Some(expected) = self.source_primitive_type(opposite) {
            return self.arg_as(arg, &ArgType::Primitive(expected));
        }
        if let Some(expected) = self.source_expression_type(opposite) {
            if let Some(erased) = self.source_erasure(&expected) {
                if erased.is_reference() && self.expression_type(arg)? == &erased {
                    return self.arg_as_source_target(arg, &erased, &expected);
                }
            }
        }
        match self.expression_type(opposite).cloned() {
            Ok(expected) => self.arg_as(arg, &expected),
            Err(_) if Self::constant(arg) != Some(0) => self.arg(arg),
            Err(error) => Err(error.into()),
        }
    }

    fn is_boolean_arg(&self, arg: &SemanticExpression) -> Result<bool, KotlinLoweringError> {
        Ok(self.source_primitive_type(arg) == Some(PrimitiveType::Boolean))
    }

    fn is_reference_arg(&self, arg: &SemanticExpression) -> Result<bool, KotlinLoweringError> {
        Ok(matches!(
            self.expression_type(arg)?,
            ArgType::Object(_) | ArgType::Array(_)
        ))
    }

    fn expression_type<'a>(
        &'a self,
        expression: &'a SemanticExpression,
    ) -> Result<&'a ArgType, KotlinLoweringError> {
        match expression {
            SemanticExpression::Register(register) => Ok(self.types.register_type(register)?),
            SemanticExpression::Literal(literal) => Ok(&literal.ty),
            SemanticExpression::Operation(operation) => operation
                .result
                .as_ref()
                .map(|result| self.types.register_type(result))
                .transpose()?
                .or_else(|| Self::declared_expression_erasure(expression))
                .ok_or(KotlinLoweringError::UnresolvedOperationType {
                    instruction: operation.insn_type,
                    offset: operation.offset,
                    domain: "inferred",
                }),
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let true_type = self.expression_type(when_true);
                let false_type = self.expression_type(when_false);
                match (true_type, false_type) {
                    (Ok(_), Ok(false_type))
                        if Self::constant(when_true) == Some(0) && false_type.is_reference() =>
                    {
                        Ok(false_type)
                    }
                    (Ok(true_type), Ok(_))
                        if Self::constant(when_false) == Some(0) && true_type.is_reference() =>
                    {
                        Ok(true_type)
                    }
                    (Ok(true_type), _) => Ok(true_type),
                    (Err(_), Ok(false_type)) => Ok(false_type),
                    (Err(error), Err(_)) => Err(error),
                }
            }
        }
    }

    fn ssa_expression_type<'a>(
        &'a self,
        expression: &'a SemanticExpression,
    ) -> Result<&'a ArgType, KotlinLoweringError> {
        match expression {
            SemanticExpression::Register(register) => Ok(self.types.ssa_type(register)?),
            SemanticExpression::Literal(literal) => Ok(&literal.ty),
            SemanticExpression::Operation(operation) => operation
                .result
                .as_ref()
                .map(|result| self.types.ssa_type(result))
                .transpose()?
                .or_else(|| Self::declared_expression_erasure(expression))
                .ok_or(KotlinLoweringError::UnresolvedOperationType {
                    instruction: operation.insn_type,
                    offset: operation.offset,
                    domain: "SSA",
                }),
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let true_type = self.ssa_expression_type(when_true);
                let false_type = self.ssa_expression_type(when_false);
                match (true_type, false_type) {
                    (Ok(_), Ok(false_type))
                        if Self::constant(when_true) == Some(0) && false_type.is_reference() =>
                    {
                        Ok(false_type)
                    }
                    (Ok(true_type), Ok(_))
                        if Self::constant(when_false) == Some(0) && true_type.is_reference() =>
                    {
                        Ok(true_type)
                    }
                    (Ok(true_type), _) => Ok(true_type),
                    (Err(_), Ok(false_type)) => Ok(false_type),
                    (Err(error), Err(_)) => Err(error),
                }
            }
        }
    }

    fn insn_expr(
        &mut self,
        insn: &SemanticOperation,
        predicate: Option<&SemanticPredicate>,
        expected_source_type: Option<&KotlinType>,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        match insn.insn_type {
            InsnType::Const => {
                let argument = insn
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                self.arg(argument)
            }
            InsnType::ConstStr => Ok(KotlinExpr::Literal(KotlinLiteral::String(
                insn.payload
                    .string_value
                    .as_ref()
                    .ok_or(KotlinLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "string_value",
                    })?
                    .clone(),
            ))),
            InsnType::ConstClass => Ok(KotlinExpr::ClassLiteral(
                self.source_type(insn.payload.class_type.as_ref().ok_or(
                    KotlinLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "class_type",
                    },
                )?)?,
            )),
            InsnType::Move => self.arg(
                insn.operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
            ),
            InsnType::Phi => Err(KotlinLoweringError::UnrecoveredPhi(insn.offset)),
            InsnType::MoveResult => Err(KotlinLoweringError::UnrecoveredMoveResult(insn.offset)),
            InsnType::MoveException => {
                Err(KotlinLoweringError::UnrecoveredExceptionValue(insn.offset))
            }
            InsnType::MonitorEnter | InsnType::MonitorExit => {
                Err(KotlinLoweringError::UnrecoveredMonitor(insn.offset))
            }
            InsnType::Arith => {
                let operator =
                    insn.payload
                        .arith_op
                        .ok_or(KotlinLoweringError::MissingPayload {
                            instruction: insn.insn_type,
                            field: "arith_op",
                        })?;
                let result_type = if self.arithmetic_is_boolean(insn) {
                    ArgType::BOOLEAN
                } else if let [left, right] = insn.operands() {
                    self.source_primitive_type(left)
                        .zip(self.source_primitive_type(right))
                        .and_then(|(left, right)| {
                            PrimitiveOperationDomain::arithmetic_result(operator, left, right)
                        })
                        .map(ArgType::Primitive)
                        .unwrap_or_else(|| {
                            insn.result
                                .as_ref()
                                .map(|result| result.ty.clone())
                                .filter(ArgType::is_known)
                                .unwrap_or(ArgType::INT)
                        })
                } else {
                    insn.result
                        .as_ref()
                        .map(|result| result.ty.clone())
                        .filter(ArgType::is_known)
                        .or_else(|| {
                            insn.result
                                .as_ref()
                                .and_then(|result| self.types.register_type(result).ok())
                                .cloned()
                        })
                        .or_else(|| {
                            insn.operands()
                                .first()
                                .and_then(|argument| self.expression_type(argument).ok())
                                .cloned()
                        })
                        .ok_or(KotlinLoweringError::UnresolvedOperationType {
                            instruction: insn.insn_type,
                            offset: insn.offset,
                            domain: "arithmetic",
                        })?
                };
                let mut left = self.arg_as(
                    insn.operands()
                        .first()
                        .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                    &result_type,
                )?;
                let right_type = if matches!(operator, ArithOp::Shl | ArithOp::Shr | ArithOp::Ushr)
                {
                    ArgType::INT
                } else {
                    result_type
                };
                let mut right = self.arg_as(
                    insn.operands()
                        .get(1)
                        .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                    &right_type,
                )?;
                let (operator, reverse) = Self::binary_operator(operator);
                if reverse {
                    std::mem::swap(&mut left, &mut right);
                }
                Ok(KotlinArithmetic::binary(left, operator, right))
            }
            InsnType::StringConcat => {
                let mut args = insn.operands().iter();
                let first = args
                    .next()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                let mut expression = self.arg(first)?;
                for arg in args {
                    expression = KotlinExpr::Binary {
                        left: Box::new(expression),
                        op: KotlinBinaryOp::Add,
                        right: Box::new(self.arg(arg)?),
                    };
                }
                Ok(expression)
            }
            InsnType::Neg | InsnType::Not => {
                let boolean = match insn.operands().first() {
                    Some(argument) => self.is_boolean_arg(argument)?,
                    None => false,
                };
                Ok(KotlinExpr::Unary {
                    op: if insn.insn_type == InsnType::Neg {
                        KotlinUnaryOp::Negate
                    } else if boolean {
                        KotlinUnaryOp::LogicalNot
                    } else {
                        KotlinUnaryOp::BitwiseNot
                    },
                    operand: Box::new(
                        self.arg(
                            insn.operands()
                                .first()
                                .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                        )?,
                    ),
                })
            }
            InsnType::Cast | InsnType::CheckCast => {
                let target = insn
                    .conversion_type()
                    .ok_or(KotlinLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "conversion_type",
                    })?;
                let operand = insn
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                if insn.insn_type == InsnType::CheckCast
                    && target.is_reference()
                    && Self::constant(operand) == Some(0)
                {
                    Ok(KotlinExpr::Literal(KotlinLiteral::Null))
                } else {
                    let source_target = insn
                        .result
                        .as_ref()
                        .and_then(|result| self.source_register_type(result))
                        .cloned()
                        .filter(|_| target.is_reference())
                        .or_else(|| self.reference_cast_source_type(insn));
                    let source_actual = self.intrinsic_source_type(operand);
                    let value = match source_target.as_ref() {
                        Some(source_target) => self.arg_with_source_type(operand, source_target)?,
                        None => self.arg(operand)?,
                    };
                    if target.is_reference()
                        && source_target.as_ref().is_some_and(|target| {
                            source_actual
                                .as_ref()
                                .is_some_and(|actual| self.source_assignable_to(actual, target))
                        })
                    {
                        return Ok(value);
                    }
                    Ok(KotlinExpr::Cast {
                        ty: source_target.unwrap_or(self.source_type(target)?),
                        value: Box::new(value),
                    })
                }
            }
            InsnType::InstanceOf => Ok(KotlinExpr::InstanceOf {
                value: Box::new(
                    self.arg(
                        insn.operands()
                            .first()
                            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
                ty: self.source_type(insn.payload.class_type.as_ref().ok_or(
                    KotlinLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "class_type",
                    },
                )?)?,
            }),
            InsnType::ArrayLength => Ok(KotlinExpr::Field {
                owner: Box::new(
                    self.arg(
                        insn.operands()
                            .first()
                            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
                name: KotlinIdentifier::from_dex("size"),
            }),
            InsnType::Aget => Ok(KotlinExpr::ArrayAccess {
                array: Box::new(
                    self.arg(
                        insn.operands()
                            .first()
                            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
                index: Box::new(
                    self.arg(
                        insn.operands()
                            .get(1)
                            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
            }),
            InsnType::Iget => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                let owner = insn
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                let owner_expression = self.arg(owner)?;
                if self.outer_instance(field, owner).is_some()
                    || self.outer_instance_fields.contains_key(field)
                {
                    if self.is_implicit_enclosing_instance(&owner_expression, Some(&field.owner)) {
                        return Ok(KotlinExpr::QualifiedThis(
                            self.source_type(&field.field_type)?,
                        ));
                    }
                }
                Ok(KotlinExpr::Field {
                    owner: Box::new(owner_expression),
                    name: self.member_names.field(field),
                })
            }
            InsnType::Sget => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                if self.singleton_instances.contains(field) {
                    return Ok(KotlinExpr::ObjectReference(
                        self.source_type(&field.field_type)?,
                    ));
                }
                let expression = KotlinExpr::StaticField {
                    owner: self.static_owner_type(&field.owner)?,
                    name: self.member_names.field(field),
                };
                Ok(self.apply_platform_field_contract(field, expression))
            }
            InsnType::Invoke => self.invoke(insn, None),
            InsnType::Constructor => {
                let method = Self::method(insn.payload.reference.as_ref())?;
                let allocation_owner = insn.allocation_type().unwrap_or(&method.owner);
                let contract = self.generic_methods.get(method).cloned();
                let mut constraints = contract
                    .as_ref()
                    .map(|contract| {
                        self.solver(&contract.owner, &contract.signature.type_parameters)
                    })
                    .unwrap_or_else(|| {
                        GenericTypeSolver::new(&self.source_types)
                            .with_projection(self.generic_type_projection.as_deref())
                    });
                let contextual_allocation_type = expected_source_type.and_then(|expected| {
                    if self.source_erasure(expected).as_ref() == Some(allocation_owner) {
                        return Some(expected.clone());
                    }
                    self.generic_type_projection
                        .as_deref()
                        .and_then(|projection| projection.infer_subtype(allocation_owner, expected))
                });
                if let Some(contract) = &contract {
                    if allocation_owner == &method.owner {
                        if let Some(allocation_type) = contextual_allocation_type.as_ref() {
                            constraints.constrain_owner(&contract.owner, allocation_type);
                        }
                    }
                    for ((formal, erased), actual) in contract
                        .signature
                        .parameter_types
                        .iter()
                        .zip(&method.descriptor.parameters)
                        .zip(insn.operands().iter().skip(1))
                    {
                        if let Some(actual) =
                            self.generic_inference_argument_source_type(actual, erased)
                        {
                            constraints.constrain(formal, &actual);
                        }
                    }
                }
                let argument_source_types = method
                    .descriptor
                    .parameters
                    .iter()
                    .enumerate()
                    .map(|(index, _)| {
                        contract
                            .as_ref()
                            .and_then(|contract| contract.signature.parameter_types.get(index))
                            .and_then(|formal| constraints.invocation_input_type(formal))
                    })
                    .collect::<Vec<_>>();
                let needs_inferred_allocation = contextual_allocation_type.is_some()
                    || insn
                        .operands()
                        .iter()
                        .skip(1)
                        .any(|argument| self.is_function_object_expression(argument));
                let inferred_allocation_type = needs_inferred_allocation
                    .then(|| match contract.as_ref() {
                        Some(contract)
                            if constraints
                                .satisfies_declared_bounds(&contract.owner_parameters) =>
                        {
                            constraints.owner_type(&contract.owner)
                        }
                        Some(_) => None,
                        None => contextual_allocation_type
                            .filter(|ty| constraints.valid_source_type(ty)),
                    })
                    .flatten()
                    .filter(|ty| self.source_erasure(ty).as_ref() == Some(allocation_owner));
                let explicit_function_targets = inferred_allocation_type.is_none();
                drop(constraints);
                let lowered = insn
                    .operands()
                    .iter()
                    .skip(1)
                    .enumerate()
                    .map(
                        |(index, arg)| match method.descriptor.parameters.get(index) {
                            Some(expected) => {
                                match argument_source_types.get(index).cloned().flatten() {
                                    Some(source) => self
                                        .arg_as_source_target(arg, expected, &source)
                                        .map(|expression| {
                                            if explicit_function_targets
                                                && self.is_function_object_expression(arg)
                                            {
                                                KotlinExpr::Cast {
                                                    ty: source,
                                                    value: Box::new(expression),
                                                }
                                            } else {
                                                expression
                                            }
                                        }),
                                    None => self.arg_as(arg, expected),
                                }
                                .and_then(|expression| {
                                    self.disambiguate_null_argument(
                                        method, index, expected, expression,
                                    )
                                })
                            }
                            None => self.arg(arg),
                        },
                    )
                    .collect::<Result<Vec<_>, _>>()?;
                let default = self
                    .default_calls
                    .get(method)
                    .filter(|contract| contract.is_constructor())
                    .and_then(|contract| {
                        DefaultArguments::new(contract, &lowered, 0)
                            .recover()
                            .filter(|recovered| {
                                recovered.is_positional(
                                    contract.target().descriptor.parameters.len(),
                                    None,
                                )
                            })
                            .map(|recovered| (contract.target(), recovered.values))
                    });
                let (source_constructor, lowered) = default.unwrap_or((method, lowered));
                let hidden = self
                    .member_names
                    .hidden_constructor_parameters(source_constructor)
                    .cloned()
                    .unwrap_or_default();
                let enclosing_parameter = self
                    .member_names
                    .enclosing_constructor_parameter(source_constructor);
                let enclosing = enclosing_parameter
                    .and_then(|parameter| lowered.get(parameter).cloned())
                    .filter(|expression| {
                        !self.is_implicit_enclosing_instance(
                            expression,
                            enclosing_parameter.and_then(|parameter| {
                                source_constructor.descriptor.parameters.get(parameter)
                            }),
                        )
                    });
                let args = lowered
                    .into_iter()
                    .enumerate()
                    .filter_map(|(index, argument)| {
                        if hidden.contains(&index) {
                            None
                        } else {
                            Some(argument)
                        }
                    })
                    .collect();
                let concrete_type = self.source_type(allocation_owner)?;
                let allocation_type =
                    Self::instantiation_type(inferred_allocation_type.unwrap_or(concrete_type));
                Ok(KotlinExpr::New {
                    enclosing: enclosing.map(Box::new),
                    ty: allocation_type,
                    target_type: None,
                    args,
                    anonymous_body: None,
                })
            }
            InsnType::NewInstance => Err(KotlinLoweringError::UnrecoveredObjectInitialization(
                insn.offset,
            )),
            InsnType::NewArray => Ok(KotlinExpr::NewArray {
                element_type: self.source_type(self.array_element_type(insn)?)?,
                dimensions: vec![self.arg(
                    insn.operands()
                        .first()
                        .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                )?],
                initializer: Vec::new(),
            }),
            InsnType::FilledNewArray => Ok(KotlinExpr::NewArray {
                element_type: self.source_type(self.array_element_type(insn)?)?,
                dimensions: Vec::new(),
                initializer: {
                    let element = self.array_element_type(insn)?.clone();
                    insn.operands()
                        .iter()
                        .map(|arg| self.arg_as(arg, &element))
                        .collect::<Result<Vec<_>, _>>()?
                },
            }),
            InsnType::Ternary => {
                let condition = predicate.ok_or(KotlinLoweringError::MissingCondition)?;
                let condition = self.predicate(condition)?;
                let result_is_boolean = insn
                    .result
                    .as_ref()
                    .map(|result| self.types.register_type(result))
                    .transpose()?
                    == Some(&ArgType::BOOLEAN);
                if result_is_boolean {
                    match (
                        insn.operands().first().and_then(Self::constant),
                        insn.operands().get(1).and_then(Self::constant),
                    ) {
                        (Some(1), Some(0)) => return Ok(condition),
                        (Some(0), Some(1)) => {
                            return Ok(Self::negate_boolean(condition));
                        }
                        _ => {}
                    }
                }
                Ok(KotlinExpr::Conditional {
                    condition: Box::new(condition),
                    when_true: Box::new(
                        self.arg(
                            insn.operands()
                                .first()
                                .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                        )?,
                    ),
                    when_false: Box::new(
                        self.arg(
                            insn.operands()
                                .get(1)
                                .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                        )?,
                    ),
                })
            }
            InsnType::Cmp => self.comparison(insn),
            _ => Err(KotlinLoweringError::UnsupportedExpression(insn.insn_type)),
        }
    }

    fn invocation_solver<'operation>(
        &self,
        operation: &'operation SemanticOperation,
    ) -> Option<(
        GenericTypeSolver<'_>,
        Vec<&'operation SemanticExpression>,
        GenericMethodContract,
    )> {
        let method = Self::method(operation.payload.reference.as_ref()).ok()?;
        let contract = self.generic_methods.get(method)?.clone();
        let invoke_type = operation.payload.invoke_type?;
        let is_static = invoke_type == InvokeType::Static;
        let mut solver = self.solver(&contract.owner, &contract.signature.type_parameters);
        if !is_static {
            if let Some(receiver) = operation.operands().first() {
                self.constrain_invocation_owner(
                    &mut solver,
                    &method.owner,
                    &contract.owner,
                    receiver,
                );
            }
        }
        let arguments = operation
            .operands()
            .iter()
            .skip(usize::from(!is_static))
            .collect::<Vec<_>>();
        for ((formal, erased), actual) in contract
            .signature
            .parameter_types
            .iter()
            .zip(&method.descriptor.parameters)
            .zip(arguments.iter().copied())
        {
            if let Some(actual) = self.generic_inference_argument_source_type(actual, erased) {
                solver.constrain(formal, &actual);
            }
        }
        Some((solver, arguments, contract))
    }

    fn owner_inferred_from_arguments(
        &self,
        operation: &SemanticOperation,
        method: &MethodReference,
        contract: &GenericMethodContract,
        expected: Option<&KotlinType>,
    ) -> Option<KotlinType> {
        if operation.payload.invoke_type == Some(InvokeType::Static) {
            return None;
        }
        let mut solver = self.solver(&contract.owner, &contract.signature.type_parameters);
        for ((formal, erased), actual) in contract
            .signature
            .parameter_types
            .iter()
            .zip(&method.descriptor.parameters)
            .zip(operation.operands().iter().skip(1))
        {
            if let Some(actual_type) = self
                .generic_inference_argument_source_type(actual, erased)
                .filter(|actual| self.has_generic_argument_evidence(actual))
            {
                solver.constrain(formal, &actual_type);
            }
            let SemanticExpression::Operation(nested_operation) = actual else {
                continue;
            };
            let Some((mut nested, _, nested_contract)) = self.invocation_solver(nested_operation)
            else {
                continue;
            };
            let result = invocation_expression_signature(nested_operation, &nested_contract);
            GenericTypeRelation::converge(&mut solver, formal, &mut nested, result.as_ref());
        }
        let receiver_has_evidence = operation
            .operands()
            .first()
            .and_then(|receiver| self.source_receiver_type(receiver))
            .is_some_and(|receiver| self.has_generic_argument_evidence(&receiver))
            || operation
                .operands()
                .first()
                .is_some_and(|receiver| self.expression_declares_concrete_generic_type(receiver));
        if let Some(expected) = expected.filter(|_| !receiver_has_evidence) {
            let result = invocation_expression_signature(operation, contract);
            solver.constrain_context(result.as_ref(), expected);
        }
        solver.complete_with_bounds(&contract.signature.type_parameters);
        solver.evidenced_owner_type(&contract.owner)
    }

    fn constrain_invocation_owner(
        &self,
        solver: &mut GenericTypeSolver<'_>,
        owner: &ArgType,
        owner_signature: &ClassTypeSignature,
        receiver: &SemanticExpression,
    ) {
        if self.is_enclosing_instance_receiver(receiver, owner) {
            solver.constrain_current_owner(owner_signature);
            solver.assume_raw_owner_if_unbound(owner_signature);
            return;
        }
        if self.this_code_var.is_some_and(|this_variable| {
            receiver
                .as_register()
                .and_then(|receiver| receiver.code_var)
                == Some(this_variable)
        }) {
            if self.current_type.as_ref() == Some(owner) {
                let declared_owner = JvmTypeSignature::ClassType(owner_signature.clone()).erased();
                if &declared_owner == owner {
                    solver.constrain_current_owner(owner_signature);
                } else if let Some(projected) =
                    self.source_current_type.as_ref().and_then(|current| {
                        self.generic_type_projection
                            .as_deref()
                            .and_then(|projection| {
                                projection.project_supertype(current, &declared_owner)
                            })
                    })
                {
                    solver.constrain_owner(owner_signature, &projected);
                }
            } else if let Some(projected) = self.source_current_type.as_ref().and_then(|current| {
                self.generic_type_projection
                    .as_deref()
                    .and_then(|projection| projection.project_supertype(current, owner))
            }) {
                solver.constrain_owner(owner_signature, &projected);
            }
            solver.assume_raw_owner_if_unbound(owner_signature);
            return;
        }
        if let Some(actual) = self.source_receiver_type(receiver) {
            solver.constrain_owner(owner_signature, &actual);
        }
        solver.assume_raw_owner_if_unbound(owner_signature);
    }

    fn singleton_instance_owner(&self, expression: &SemanticExpression) -> Option<ArgType> {
        let SemanticExpression::Operation(operation) = expression else {
            return None;
        };
        if operation.insn_type == InsnType::CheckCast {
            return operation
                .operands()
                .first()
                .and_then(|value| self.singleton_instance_owner(value));
        }
        if operation.insn_type != InsnType::Sget {
            return None;
        }
        let Some(MemberReference::Field(field)) = operation.payload.reference.as_ref() else {
            return None;
        };
        self.singleton_instances
            .contains(field)
            .then(|| field.owner.clone())
    }

    fn invoke(
        &mut self,
        insn: &SemanticOperation,
        expected_source_type: Option<&KotlinType>,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let method = Self::method(insn.payload.reference.as_ref())?;
        let invoke_type = insn
            .payload
            .invoke_type
            .ok_or(KotlinLoweringError::MissingPayload {
                instruction: insn.insn_type,
                field: "invoke_type",
            })?;
        let is_static = invoke_type == InvokeType::Static;
        let singleton_owner = matches!(invoke_type, InvokeType::Virtual | InvokeType::Interface)
            .then(|| insn.operands().first())
            .flatten()
            .and_then(|receiver| self.singleton_instance_owner(receiver))
            .filter(|_| !self.extension_receivers.contains_key(method));
        let default_dispatch_owner = self
            .default_calls
            .get(method)
            .filter(|contract| {
                contract.target_is_static() == Some(false)
                    && contract.extension_receiver().is_none()
            })
            .and_then(|_| insn.operands().first())
            .and_then(|receiver| self.singleton_instance_owner(receiver));
        let platform_owner = method.owner.to_descriptor();
        let platform_descriptor = method.descriptor.to_string();
        let platform_parameter_nullability = self
            .platform_symbols
            .as_deref()
            .and_then(|symbols| {
                symbols.resolve_method(&platform_owner, &method.name, &platform_descriptor)
            })
            .map(|(class, platform_method)| {
                (0..method.descriptor.parameters.len())
                    .map(|parameter| class.method_parameter_nullability(platform_method, parameter))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let contract = self.generic_methods.get(method).cloned();
        let mut constraints = contract
            .as_ref()
            .map(|contract| self.solver(&contract.owner, &contract.signature.type_parameters))
            .unwrap_or_else(|| {
                GenericTypeSolver::new(&self.source_types)
                    .with_projection(self.generic_type_projection.as_deref())
            });
        if let Some(contract) = &contract {
            if !is_static {
                if let Some(receiver) = insn.operands().first() {
                    self.constrain_invocation_owner(
                        &mut constraints,
                        &method.owner,
                        &contract.owner,
                        receiver,
                    );
                }
            }
            for ((formal, erased), actual) in contract
                .signature
                .parameter_types
                .iter()
                .zip(&method.descriptor.parameters)
                .zip(
                    insn.operands()
                        .iter()
                        .skip(usize::from(invoke_type != InvokeType::Static)),
                )
            {
                if let Some(actual) = self.generic_inference_argument_source_type(actual, erased) {
                    constraints.constrain(formal, &actual);
                }
            }
            if let Some(expected) = expected_source_type {
                constraints.constrain_context(&contract.signature.return_type, expected);
            }
            for (formal, actual) in contract.signature.parameter_types.iter().zip(
                insn.operands()
                    .iter()
                    .skip(usize::from(invoke_type != InvokeType::Static)),
            ) {
                let SemanticExpression::Operation(operation) = actual else {
                    continue;
                };
                let Some((mut nested, _, nested_contract)) = self.invocation_solver(operation)
                else {
                    continue;
                };
                let result = invocation_expression_signature(operation, &nested_contract);
                GenericTypeRelation::converge(
                    &mut constraints,
                    formal,
                    &mut nested,
                    result.as_ref(),
                );
            }
            constraints.complete_with_bounds(&contract.signature.type_parameters);
        }
        let receiver_is_poly_invocation = insn
            .operands()
            .first()
            .and_then(SemanticExpression::as_operation)
            .is_some_and(|receiver| receiver.insn_type == InsnType::Invoke);
        let receiver_has_evidence =
            insn.operands()
                .first()
                .and_then(|receiver| self.source_receiver_type(receiver))
                .is_some_and(|receiver| self.has_generic_argument_evidence(&receiver))
                || insn.operands().first().is_some_and(|receiver| {
                    self.expression_declares_concrete_generic_type(receiver)
                });
        let inferred_receiver_source_type = contract.as_ref().and_then(|contract| {
            (receiver_is_poly_invocation && !receiver_has_evidence)
                .then(|| {
                    self.owner_inferred_from_arguments(insn, method, contract, expected_source_type)
                })
                .flatten()
                .or_else(|| constraints.owner_type(&contract.owner))
        });
        if receiver_is_poly_invocation && !receiver_has_evidence {
            if let (Some(contract), Some(inferred)) =
                (contract.as_ref(), inferred_receiver_source_type.as_ref())
            {
                constraints.constrain_owner(&contract.owner, inferred);
                constraints.complete_with_bounds(&contract.signature.type_parameters);
            }
        }
        let receiver_requires_capture_conversion = contract.as_ref().is_some_and(|contract| {
            constraints.owner_requires_capture_conversion(
                &contract.owner,
                &contract.signature.parameter_types,
            )
        });
        let receiver_actual_type = (!is_static)
            .then(|| insn.operands().first())
            .flatten()
            .and_then(|receiver| self.source_receiver_type(receiver));
        let raw_receiver_type = (!is_static)
            .then(|| self.source_type(&method.owner).ok())
            .flatten()
            .map(KotlinType::into_raw);
        let receiver_is_source_compatible = receiver_actual_type.as_ref().is_some_and(|actual| {
            inferred_receiver_source_type
                .as_ref()
                .map(|expected| self.source_assignable_to(actual, expected))
                .unwrap_or_else(|| {
                    self.source_erasure(actual).as_ref() == Some(&method.owner)
                        || raw_receiver_type
                            .as_ref()
                            .is_some_and(|owner| self.source_assignable_to(actual, owner))
                })
        });
        let receiver_source_type = if receiver_requires_capture_conversion {
            raw_receiver_type.clone()
        } else if receiver_is_source_compatible {
            receiver_actual_type.clone()
        } else {
            inferred_receiver_source_type.or_else(|| raw_receiver_type.clone())
        };
        let receiver_requires_source_conversion = receiver_actual_type
            .as_ref()
            .zip(receiver_source_type.as_ref())
            .is_some_and(|(actual, expected)| !self.source_assignable_to(actual, expected));
        let mut argument_source_types = method
            .descriptor
            .parameters
            .iter()
            .zip(
                insn.operands()
                    .iter()
                    .skip(usize::from(invoke_type != InvokeType::Static)),
            )
            .enumerate()
            .map(|(index, (erased, actual))| {
                contract
                    .as_ref()
                    .and_then(|contract| contract.signature.parameter_types.get(index))
                    .and_then(|formal| {
                        constraints.invocation_input_type(formal).or_else(|| {
                            Self::signature_is_parameterized(formal)
                                .then(|| self.argument_requirement(actual, erased))
                                .flatten()
                        })
                    })
            })
            .collect::<Vec<_>>();
        let invocation_arguments = insn
            .operands()
            .iter()
            .skip(usize::from(invoke_type != InvokeType::Static))
            .collect::<Vec<_>>();
        let unchecked_arguments = contract
            .as_ref()
            .map(|contract| {
                contract
                    .signature
                    .parameter_types
                    .iter()
                    .zip(&method.descriptor.parameters)
                    .zip(&invocation_arguments)
                    .enumerate()
                    .filter_map(|(index, ((formal, erased), actual))| {
                        let actual = self
                            .intrinsic_source_type(actual)
                            .or_else(|| self.generic_argument_source_type(actual, erased))?;
                        GenericInvocationCompatibility::requires_unchecked_conversion(
                            formal,
                            &actual,
                            contract,
                            &self.source_types,
                        )
                        .then_some(index)
                    })
                    .collect::<BTreeSet<_>>()
            })
            .unwrap_or_default();
        let inferred_inputs_are_sound =
            self.invocation_inputs_are_sound(&argument_source_types, &invocation_arguments);
        // Conflicting inference evidence prevents publishing explicit method
        // type arguments, but it does not erase the source conversion required
        // by each instantiated formal. Keeping those targets lets lowering
        // materialize the same erased bridge casts that javac inserted before
        // DEX discarded the generic types.
        let explicit_invocation = inferred_inputs_are_sound
            .then(|| {
                contract
                    .as_ref()
                    .filter(|contract| {
                        contract
                            .signature
                            .type_parameters
                            .iter()
                            .any(|parameter| constraints.type_argument_is_captured(parameter))
                    })
                    .and_then(|contract| {
                        let (specialized, arguments) = constraints
                            .specialize_explicit_arguments(&contract.signature.type_parameters)?;
                        let targets = contract
                            .signature
                            .parameter_types
                            .iter()
                            .zip(&method.descriptor.parameters)
                            .zip(&invocation_arguments)
                            .map(|((formal, erased), actual)| {
                                specialized.invocation_input_type(formal).or_else(|| {
                                    Self::signature_is_parameterized(formal)
                                        .then(|| self.argument_requirement(actual, erased))
                                        .flatten()
                                })
                            })
                            .collect::<Vec<_>>();
                        self.invocation_inputs_are_sound(&targets, &invocation_arguments)
                            .then_some((arguments, targets))
                    })
            })
            .flatten();
        let invocation_type_arguments = match explicit_invocation {
            Some((arguments, targets)) => {
                argument_source_types = targets;
                arguments
            }
            None => Vec::new(),
        };
        drop(constraints);
        let receiver = match invoke_type {
            InvokeType::Static => None,
            InvokeType::Super => Some(Box::new(KotlinExpr::Super)),
            _ if singleton_owner.is_some() => None,
            _ => {
                let receiver = insn
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                let mut expression = match receiver_source_type.as_ref() {
                    Some(expected) => {
                        self.arg_as_source_target(receiver, &method.owner, expected)?
                    }
                    None => self.arg_as(receiver, &method.owner)?,
                };
                if let Some(expected) = receiver_source_type.as_ref() {
                    self.specialize_standalone_invocation(receiver, expected, &mut expression);
                }
                let expression = self.preserve_standalone_check_cast(receiver, expression);
                Some(Box::new(
                    if receiver_requires_capture_conversion
                        || (!receiver_is_source_compatible && receiver_requires_source_conversion)
                    {
                        let expected = receiver_source_type
                            .as_ref()
                            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                        let erased = self.source_type(&method.owner)?.into_star_projection();
                        self.source_cast(
                            expression,
                            receiver,
                            receiver_actual_type.as_ref(),
                            expected,
                            &erased,
                        )
                    } else {
                        expression
                    },
                ))
            }
        };
        let source_singleton_owner = singleton_owner
            .as_ref()
            .map(|owner| self.static_owner_type(owner))
            .transpose()?;
        let call_arguments = insn
            .operands()
            .iter()
            .skip(usize::from(!is_static))
            .cloned()
            .collect::<Vec<_>>();
        let overload_casts = self.overload_argument_casts(method, &call_arguments);
        let mut args = insn
            .operands()
            .iter()
            .skip(usize::from(!is_static))
            .enumerate()
            .map(|(index, arg)| {
                let Some(expected) = method.descriptor.parameters.get(index) else {
                    return self.arg(arg);
                };
                let inferred_target = argument_source_types.get(index).cloned().flatten();
                let proven_erasure_conversion = inferred_target.as_ref().is_some_and(|target| {
                    let actual = self.source_expression_type(arg);
                    actual.as_ref().is_some_and(|actual| {
                        self.source_erasure(actual)
                            .as_ref()
                            .zip(self.source_erasure(target).as_ref())
                            .is_some_and(|(actual, target)| {
                                actual == target
                                    || self
                                        .generic_type_projection
                                        .as_deref()
                                        .is_some_and(|projection| {
                                            projection.is_subtype(actual, target)
                                        })
                            })
                    })
                });
                let mut target_type = (!unchecked_arguments.contains(&index)
                    || proven_erasure_conversion)
                    .then_some(inferred_target)
                    .flatten();
                if let Some(requirement) = self
                    .source_requirement_type(arg)
                    .filter(|requirement| self.has_generic_argument_evidence(requirement))
                    .filter(|requirement| {
                        target_type.as_ref().is_none_or(|target| {
                            Self::same_erasure(target, requirement)
                                && !self.has_generic_argument_evidence(target)
                        })
                    })
                {
                    target_type = Some(requirement.clone());
                }
                if target_type.is_none()
                    && matches!(arg, SemanticExpression::Select { .. })
                    && contract
                        .as_ref()
                        .and_then(|contract| contract.signature.parameter_types.get(index))
                        .is_some_and(Self::signature_is_parameterized)
                {
                    target_type = self
                        .source_expression_type(arg)
                        .filter(|target| self.has_generic_argument_evidence(target));
                }
                let unresolved_poly_select = target_type.is_none()
                    && matches!(arg, SemanticExpression::Select { .. })
                    && contract
                        .as_ref()
                        .and_then(|contract| contract.signature.parameter_types.get(index))
                        .is_some_and(Self::signature_is_parameterized);
                let expression = match target_type.as_ref() {
                    Some(target_type) => self.arg_as_source_target(arg, expected, target_type)?,
                    None
                        if !inferred_inputs_are_sound
                            && self.is_function_object_expression(arg) =>
                    {
                        KotlinExpr::Cast {
                            ty: self.source_type(expected)?.into_star_projection(),
                            value: Box::new(self.arg(arg)?),
                        }
                    }
                    None => self.arg_as(arg, expected)?,
                };
                let expression = self.recover_symbolic_argument(method, index, expression);
                let expression = match (&target_type, &expression) {
                    (Some(target), KotlinExpr::Cast { ty, .. })
                        if GenericCast::is_parameterized(target)
                            && !GenericCast::has_wildcard(target)
                            && !GenericCast::is_parameterized(ty)
                            && Self::same_erasure(ty, target) =>
                    {
                        KotlinExpr::Cast {
                            ty: target.clone(),
                            value: Box::new(expression),
                        }
                    }
                    (Some(target), KotlinExpr::Name(name)) => {
                        let actual = self.binding_types.name_type(name).cloned();
                        if actual
                            .as_ref()
                            .is_some_and(|actual| !self.source_assignable_to(actual, target))
                        {
                            let erased = self.source_type(expected)?.into_star_projection();
                            self.source_cast(expression, arg, actual.as_ref(), target, &erased)
                        } else {
                            expression
                        }
                    }
                    _ => expression,
                };
                let expression = if unresolved_poly_select
                    && !matches!(&expression, KotlinExpr::Cast { ty, .. } if self.source_erasure(ty).as_ref() == Some(expected))
                {
                    KotlinExpr::Cast {
                        ty: self.source_type(expected)?.into_star_projection(),
                        value: Box::new(expression),
                    }
                } else {
                    expression
                };
                let expression = if overload_casts.contains(&index)
                    && !matches!(&expression, KotlinExpr::Cast { ty, .. } if self.source_erasure(ty).as_ref() == Some(expected))
                {
                    KotlinExpr::Cast {
                        ty: self.overload_cast_type(expected, target_type.as_ref())?,
                        value: Box::new(expression),
                    }
                } else {
                    expression
                };
                self.disambiguate_null_argument(method, index, expected, expression)
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (index, expression) in args.iter_mut().enumerate() {
            let source_contract = self
                .method_nullability
                .get(method)
                .is_some_and(|nullability| nullability.parameter_is_non_null(index));
            let platform_contract = platform_parameter_nullability.get(index)
                == Some(&Some(crate::platform_symbols::PlatformNullability::NonNull));
            if (source_contract || platform_contract)
                && !super::KotlinNullabilityFacts::expression_definitely_non_null(expression)
            {
                *expression = KotlinExpr::NonNullAssertion(Box::new(expression.clone()));
            }
        }
        if let Some(contract) = self.default_calls.get(method) {
            if let Some(expression) =
                DefaultCall::new(contract, &args, default_dispatch_owner).lower(self)?
            {
                return Ok(self.apply_platform_return_contract(contract.target(), expression));
            }
        }
        if let Some(expression) = self.lower_declared_extension(
            method,
            is_static,
            receiver.as_deref(),
            &mut args,
            invocation_type_arguments.clone(),
        ) {
            return Ok(self.apply_platform_return_contract(method, expression));
        }
        if args.is_empty() {
            if let Some(property) = self.member_names.property_getter(method) {
                let expression = match (is_static, receiver, source_singleton_owner.clone()) {
                    (true, _, _) => KotlinExpr::StaticField {
                        owner: self.static_owner_type(&method.owner)?,
                        name: property,
                    },
                    (false, Some(owner), _) => KotlinExpr::Field {
                        owner,
                        name: property,
                    },
                    (false, None, Some(owner)) => KotlinExpr::StaticField {
                        owner,
                        name: property,
                    },
                    (false, None, None) => KotlinExpr::Name(property),
                };
                return Ok(self.apply_platform_return_contract(method, expression));
            }
        }
        if args.len() == 1 {
            if let Some(property) = self.member_names.property_setter(method) {
                let target = match (is_static, receiver, source_singleton_owner.clone()) {
                    (true, _, _) => KotlinExpr::StaticField {
                        owner: self.static_owner_type(&method.owner)?,
                        name: property,
                    },
                    (false, Some(owner), _) => KotlinExpr::Field {
                        owner,
                        name: property,
                    },
                    (false, None, Some(owner)) => KotlinExpr::StaticField {
                        owner,
                        name: property,
                    },
                    (false, None, None) => KotlinExpr::Name(property),
                };
                return Ok(KotlinExpr::Assignment {
                    target: Box::new(target),
                    op: super::KotlinAssignOp::Assign,
                    value: Box::new(args.remove(0)),
                });
            }
        }
        if let Some(expression) = KotlinJvmCallSyntax::lower(
            method,
            receiver.as_deref(),
            &args,
            |subtype, supertype| {
                self.generic_type_projection
                    .as_deref()
                    .is_some_and(|projection| projection.is_subtype(subtype, supertype))
            },
            |owner| {
                self.generic_type_projection
                    .as_deref()
                    .is_some_and(|projection| projection.uses_mapped_collection_size(owner))
            },
        ) {
            return Ok(self.apply_platform_return_contract(method, expression));
        }
        let expression = KotlinExpr::Call {
            receiver,
            owner: if is_static {
                Some(self.static_owner_type(&method.owner)?)
            } else {
                source_singleton_owner
            },
            type_arguments: invocation_type_arguments,
            method: self.member_names.method(method),
            args: self.call_arguments(method, args, None),
        };
        let expression = if let Some(kind) = Self::jvm_intrinsic(method) {
            KotlinExpr::JvmIntrinsic {
                kind,
                expression: Box::new(expression),
            }
        } else {
            expression
        };
        Ok(self.apply_platform_return_contract(method, expression))
    }

    fn lower_declared_extension(
        &self,
        method: &MethodReference,
        is_static: bool,
        dispatch_receiver: Option<&KotlinExpr>,
        args: &mut Vec<KotlinExpr>,
        type_arguments: Vec<KotlinType>,
    ) -> Option<KotlinExpr> {
        if !is_static && !matches!(dispatch_receiver, None | Some(KotlinExpr::This)) {
            return None;
        }
        let receiver_index = self.extension_receivers.get(method).copied()?;
        if receiver_index >= args.len() {
            return None;
        }
        let receiver = Box::new(args.remove(receiver_index));
        if args.is_empty() {
            if let Some(property) = self.member_names.property_getter(method) {
                return Some(KotlinExpr::Field {
                    owner: receiver,
                    name: property,
                });
            }
        }
        if args.len() == 1 {
            if let Some(property) = self.member_names.property_setter(method) {
                return Some(KotlinExpr::Assignment {
                    target: Box::new(KotlinExpr::Field {
                        owner: receiver,
                        name: property,
                    }),
                    op: super::KotlinAssignOp::Assign,
                    value: Box::new(args.remove(0)),
                });
            }
        }
        Some(KotlinExpr::Call {
            receiver: Some(receiver),
            owner: None,
            type_arguments,
            method: self.member_names.method(method),
            args: self.call_arguments(method, std::mem::take(args), Some(receiver_index)),
        })
    }

    fn call_arguments(
        &self,
        method: &MethodReference,
        arguments: Vec<KotlinExpr>,
        omitted_parameter: Option<usize>,
    ) -> KotlinCallArguments {
        let spreads = self
            .vararg_parameters
            .get(method)
            .into_iter()
            .flatten()
            .filter_map(|parameter| match omitted_parameter {
                Some(omitted) if *parameter == omitted => None,
                Some(omitted) if *parameter > omitted => Some(*parameter - 1),
                _ => Some(*parameter),
            })
            .filter(|parameter| *parameter < arguments.len())
            .collect::<Vec<_>>();
        KotlinCallArguments::from_parts(arguments, std::iter::empty(), spreads)
            .expect("filtered vararg positions must address an argument")
    }

    fn jvm_intrinsic(method: &MethodReference) -> Option<super::KotlinJvmIntrinsic> {
        if method.owner.as_object() == Some("java/lang/Object")
            && method.name == "getClass"
            && method.descriptor.parameters.is_empty()
            && method.descriptor.return_type == ArgType::object("java/lang/Class")
        {
            return Some(super::KotlinJvmIntrinsic::ReceiverNullCheck);
        }
        if method.owner.as_object() != Some("kotlin/jvm/internal/Intrinsics")
            || method.descriptor.parameters
                != [
                    ArgType::object("java/lang/Object"),
                    ArgType::object("java/lang/String"),
                ]
            || method.descriptor.return_type != ArgType::VOID
        {
            return None;
        }
        match method.name.as_str() {
            "checkNotNullExpressionValue" => Some(super::KotlinJvmIntrinsic::ExpressionValueCheck),
            "checkNotNullParameter" => Some(super::KotlinJvmIntrinsic::ParameterCheck),
            _ => None,
        }
    }

    fn apply_platform_return_contract(
        &self,
        method: &MethodReference,
        expression: KotlinExpr,
    ) -> KotlinExpr {
        let platform_contract = self.platform_symbols.as_deref().is_some_and(|symbols| {
            symbols.method_return_nullability(
                &method.owner.to_descriptor(),
                &method.name,
                &method.descriptor.to_string(),
            ) == Some(crate::platform_symbols::PlatformNullability::NonNull)
        });
        let source_contract = self
            .method_nullability
            .get(method)
            .is_some_and(KotlinMethodNullability::return_is_non_null);
        if method.descriptor.return_type.is_reference() && (platform_contract || source_contract) {
            KotlinExpr::SmartCast(Box::new(expression))
        } else {
            expression
        }
    }

    fn recover_symbolic_argument(
        &self,
        method: &MethodReference,
        parameter: usize,
        expression: KotlinExpr,
    ) -> KotlinExpr {
        let Some(symbols) = self.platform_symbols.as_deref() else {
            return expression;
        };
        let Some(domain) = symbols.parameter_domain(
            &method.owner.to_descriptor(),
            &method.name,
            &method.descriptor.to_string(),
            parameter,
        ) else {
            return expression;
        };
        let Some(value) = Self::platform_constant(&expression) else {
            return expression;
        };
        let Some(members) = domain.resolve(&value) else {
            return expression;
        };
        let Some(fields) = members
            .into_iter()
            .map(|member| self.platform_field_expression(&member.field))
            .collect::<Option<Vec<_>>>()
        else {
            return expression;
        };
        let mut fields = fields.into_iter();
        let Some(first) = fields.next() else {
            return expression;
        };
        fields.fold(first, |left, right| KotlinExpr::Binary {
            left: Box::new(left),
            op: KotlinBinaryOp::BitOr,
            right: Box::new(right),
        })
    }

    fn platform_constant(
        expression: &KotlinExpr,
    ) -> Option<crate::platform_symbols::PlatformConstant> {
        match expression {
            KotlinExpr::Literal(KotlinLiteral::Integer(value)) => Some(
                crate::platform_symbols::PlatformConstant::Integer(i64::from(*value)),
            ),
            KotlinExpr::Literal(KotlinLiteral::Long(value)) => {
                Some(crate::platform_symbols::PlatformConstant::Integer(*value))
            }
            KotlinExpr::Literal(KotlinLiteral::Character(value)) => Some(
                crate::platform_symbols::PlatformConstant::Integer(i64::from(*value)),
            ),
            KotlinExpr::Literal(KotlinLiteral::String(value)) => {
                String::from_utf16(value.as_utf16())
                    .ok()
                    .map(crate::platform_symbols::PlatformConstant::String)
            }
            _ => None,
        }
    }

    fn platform_field_expression(
        &self,
        field: &crate::platform_symbols::PlatformFieldReference,
    ) -> Option<KotlinExpr> {
        let owner = field.owner.parse::<ArgType>().ok()?;
        let field_type = field.descriptor.parse::<ArgType>().ok()?;
        let name = self.member_names.field(&FieldReference {
            owner: owner.clone(),
            name: field.name.clone(),
            field_type: field_type.clone(),
        });
        let expression = KotlinExpr::StaticField {
            owner: self.source_type(&owner).ok()?,
            name,
        };
        let reference = FieldReference {
            owner,
            name: field.name.clone(),
            field_type,
        };
        Some(self.apply_platform_field_contract(&reference, expression))
    }

    fn apply_platform_field_contract(
        &self,
        field: &FieldReference,
        expression: KotlinExpr,
    ) -> KotlinExpr {
        // A Kotlin object and a companion each have one instance, held in a
        // static field the compiler assigns before anything can observe it.
        let singleton = self.singleton_types.contains(&field.field_type);
        let non_null = field.field_type.is_reference()
            && (singleton
                || self.non_null_fields.contains(field)
                || self.platform_symbols.as_deref().is_some_and(|symbols| {
                    symbols.field_nullability(
                        &field.owner.to_descriptor(),
                        &field.name,
                        &field.field_type.to_descriptor(),
                    ) == Some(crate::platform_symbols::PlatformNullability::NonNull)
                }));
        if non_null {
            KotlinExpr::SmartCast(Box::new(expression))
        } else {
            expression
        }
    }

    fn overload_cast_type(
        &self,
        erased: &ArgType,
        inferred: Option<&KotlinType>,
    ) -> Result<KotlinType, KotlinLoweringError> {
        if let Some(inferred) = inferred {
            if self.source_erasure(inferred).as_ref() == Some(erased) {
                return Ok(inferred.clone());
            }
        }
        Ok(self.source_type(erased)?.into_star_projection())
    }

    fn overload_argument_casts(
        &self,
        method: &MethodReference,
        arguments: &[SemanticExpression],
    ) -> BTreeSet<usize> {
        let Some(overloads) = self.member_names.overloads(method) else {
            return BTreeSet::new();
        };
        let target_types = method
            .descriptor
            .parameters
            .iter()
            .map(|ty| self.source_type(ty).ok())
            .collect::<Vec<_>>();
        let mut casts = BTreeSet::new();
        for candidate in overloads {
            if candidate == &method.descriptor || candidate.parameters.len() != arguments.len() {
                continue;
            }
            let candidate_types = candidate
                .parameters
                .iter()
                .map(|ty| self.source_type(ty).ok())
                .collect::<Vec<_>>();
            let applicable = arguments
                .iter()
                .zip(&candidate_types)
                .all(|(argument, target)| {
                    let Some(target) = target else {
                        return false;
                    };
                    if Self::constant(argument) == Some(0)
                        && !matches!(target, KotlinType::Primitive(_))
                    {
                        return true;
                    }
                    self.source_expression_type(argument)
                        .is_some_and(|actual| self.source_assignable_to(&actual, target))
                });
            if !applicable {
                continue;
            }
            let mut strict = None;
            let more_specific = candidate_types.iter().zip(&target_types).enumerate().all(
                |(index, (candidate, target))| {
                    let (Some(candidate), Some(target)) = (candidate, target) else {
                        return false;
                    };
                    if candidate == target {
                        return true;
                    }
                    if self.source_assignable_to(candidate, target) {
                        strict.get_or_insert(index);
                        true
                    } else {
                        false
                    }
                },
            );
            if more_specific {
                if let Some(index) = strict {
                    casts.insert(index);
                }
                continue;
            }
            if let Some(index) = candidate_types
                .iter()
                .zip(&target_types)
                .zip(arguments)
                .enumerate()
                .find_map(|(index, ((candidate, target), argument))| {
                    let (Some(candidate), Some(target)) = (candidate, target) else {
                        return None;
                    };
                    if candidate == target
                        || self.source_assignable_to(candidate, target)
                        || self.source_assignable_to(target, candidate)
                    {
                        return None;
                    }
                    self.source_expression_type(argument)
                        .is_some_and(|actual| {
                            self.source_assignable_to(&actual, candidate)
                                && self.source_assignable_to(&actual, target)
                        })
                        .then_some(index)
                })
            {
                casts.insert(index);
            }
        }
        casts
    }

    fn invocation_inputs_are_sound(
        &self,
        targets: &[Option<KotlinType>],
        arguments: &[&SemanticExpression],
    ) -> bool {
        targets.iter().zip(arguments).all(|(target, actual)| {
            let Some(target) = target else {
                return true;
            };
            self.source_expression_type(actual).is_none_or(|actual| {
                !self.has_generic_argument_evidence(&actual)
                    || self.source_assignable_to(&actual, target)
            })
        })
    }

    fn disambiguate_null_argument(
        &self,
        method: &MethodReference,
        index: usize,
        expected: &ArgType,
        expression: KotlinExpr,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        if !matches!(expression, KotlinExpr::Literal(KotlinLiteral::Null))
            || !self.member_names.null_argument_requires_cast(method, index)
        {
            return Ok(expression);
        }
        Ok(KotlinExpr::Cast {
            ty: self.source_type(expected)?,
            value: Box::new(expression),
        })
    }

    /// Method-select receivers are standalone expressions in Kotlin. A generic
    /// invocation used as a receiver cannot consume the selected method's owner
    /// type as target-typing evidence, so an explicit DEX check-cast remains
    /// necessary unless the operand is independently assignable.
    fn preserve_standalone_check_cast(
        &self,
        value: &SemanticExpression,
        expression: KotlinExpr,
    ) -> KotlinExpr {
        let Some(operation) = value
            .as_operation()
            .filter(|operation| operation.insn_type == InsnType::CheckCast)
        else {
            return expression;
        };
        if operation.operands().is_empty() {
            return expression;
        }
        let Some(target) = operation
            .result
            .as_ref()
            .and_then(|result| self.source_register_type(result).cloned())
            .or_else(|| {
                operation
                    .conversion_type()
                    .and_then(|target| self.source_type(target).ok())
            })
        else {
            return expression;
        };
        if matches!(&expression, KotlinExpr::Cast { ty, .. }
                if ty == &target
                    || (!GenericCast::has_generic_evidence(&target)
                        && GenericCast::has_generic_evidence(ty)
                        && Self::same_erasure(ty, &target)))
            || self.source_check_cast_is_redundant(operation, &target)
        {
            return expression;
        }
        KotlinExpr::Cast {
            ty: target,
            value: Box::new(expression),
        }
    }

    fn specialize_standalone_invocation(
        &self,
        value: &SemanticExpression,
        expected: &KotlinType,
        expression: &mut KotlinExpr,
    ) {
        let Some(operation) = value
            .as_operation()
            .filter(|operation| operation.insn_type == InsnType::Invoke)
        else {
            return;
        };
        if operation
            .payload
            .invoke_type
            .is_some_and(|invoke| invoke == InvokeType::Super)
        {
            return;
        }
        if self
            .declared_operation_source_type(operation)
            .is_some_and(|actual| self.source_assignable_to(&actual, expected))
        {
            return;
        }
        let Some((mut solver, arguments, contract)) = self.invocation_solver(operation) else {
            return;
        };
        if contract.signature.type_parameters.is_empty() {
            return;
        }
        solver.constrain_context(&contract.signature.return_type, expected);
        solver.complete_with_bounds(&contract.signature.type_parameters);
        let Some((specialized, type_arguments)) =
            solver.specialize_explicit_arguments(&contract.signature.type_parameters)
        else {
            return;
        };
        let targets = contract
            .signature
            .parameter_types
            .iter()
            .map(|formal| specialized.invocation_input_type(formal))
            .collect::<Vec<_>>();
        if !self.invocation_inputs_are_sound(&targets, &arguments) {
            return;
        }
        if let KotlinExpr::Call {
            type_arguments: emitted,
            ..
        } = expression
        {
            *emitted = type_arguments;
        }
    }

    fn arg_with_source_type(
        &mut self,
        value: &SemanticExpression,
        expected: &KotlinType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        if expected == &KotlinType::boolean() {
            return self.boolean_value(value);
        }
        let mut expression = match value {
            SemanticExpression::Select {
                condition,
                when_true,
                when_false,
            } => self.select_value_with_source_type(condition, when_true, when_false, expected),
            SemanticExpression::Operation(operation) if operation.insn_type == InsnType::Invoke => {
                self.invoke(operation, Some(expected))
            }
            SemanticExpression::Operation(operation)
                if operation.insn_type == InsnType::Constructor =>
            {
                self.insn_expr(operation, None, Some(expected))
            }
            SemanticExpression::Operation(operation)
                if operation.insn_type == InsnType::Move && operation.operands().len() == 1 =>
            {
                self.arg_with_source_type(&operation.operands()[0], expected)
            }
            SemanticExpression::Operation(operation)
                if operation.insn_type == InsnType::CheckCast =>
            {
                let target =
                    operation
                        .conversion_type()
                        .ok_or(KotlinLoweringError::MissingPayload {
                            instruction: operation.insn_type,
                            field: "conversion_type",
                        })?;
                let operand = operation
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(operation.insn_type))?;
                let source_target = target
                    .is_reference()
                    .then(|| self.reference_cast_source_type(operation))
                    .flatten();
                if target.is_reference() && Self::constant(operand) == Some(0) {
                    Ok(KotlinExpr::Literal(KotlinLiteral::Null))
                } else if target.is_reference()
                    && source_target
                        .as_ref()
                        .is_some_and(|source| self.source_assignable_to(&source, expected))
                    && source_target.as_ref().is_some_and(|target| {
                        self.source_check_cast_is_redundant(operation, target)
                    })
                {
                    self.arg_with_source_type(operand, expected)
                } else if let Some(source_target) =
                    source_target.filter(|source| self.source_assignable_to(source, expected))
                {
                    let actual = self.cast_source_type(operand);
                    let expression = self.arg_with_source_type(operand, &source_target)?;
                    let erased = self.source_type(target)?.into_star_projection();
                    Ok(self.source_cast(
                        expression,
                        operand,
                        actual.as_ref(),
                        &source_target,
                        &erased,
                    ))
                } else if target.is_reference() && self.target_has_source_erasure(expected, target)
                {
                    let actual = self.cast_source_type(operand);
                    let expression = self.arg_with_source_type(operand, expected)?;
                    let erased = self.source_type(target)?.into_star_projection();
                    Ok(self.source_cast(expression, operand, actual.as_ref(), expected, &erased))
                } else {
                    Ok(KotlinExpr::Cast {
                        ty: self.source_type(target)?,
                        value: Box::new(self.arg_with_source_type(operand, expected)?),
                    })
                }
            }
            _ => self.arg(value),
        }?;
        if let KotlinExpr::New { target_type, .. } = &mut expression {
            // Constructor lowering has already solved and validated the
            // allocation's class arguments. The assignment target describes
            // conversion context; it cannot legally re-parameterize `new`
            // after owner bounds have been checked.
            *target_type = Some(Self::instantiation_type(expected.clone()));
        }
        Ok(expression)
    }

    fn arg_as_with_source_type(
        &mut self,
        value: &SemanticExpression,
        erased: &ArgType,
        expected: &KotlinType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let source_erasure = matches!(expected, KotlinType::Primitive(_))
            .then(|| self.source_erasure(expected))
            .flatten();
        let erased = source_erasure.as_ref().unwrap_or(erased);
        if erased == &ArgType::BOOLEAN {
            return self.boolean_value(value);
        }
        let actual = self.source_primitive_type(value);
        let expression = match value {
            SemanticExpression::Select {
                condition,
                when_true,
                when_false,
            } => self.select_value_with_source_target(
                condition, when_true, when_false, erased, expected,
            )?,
            _ => self.arg_with_source_type(value, expected)?,
        };
        let mut expression = self.coerce_typed(expression, actual, erased);
        if let KotlinExpr::New { target_type, .. } = &mut expression {
            *target_type = Some(Self::instantiation_type(expected.clone()));
        }
        Ok(expression)
    }

    fn instantiation_type(mut ty: KotlinType) -> KotlinType {
        if let KotlinType::Class(class) = &mut ty {
            for segment in &mut class.segments {
                if segment
                    .arguments
                    .iter()
                    .any(|argument| matches!(argument, KotlinTypeArgument::Any))
                {
                    segment.arguments.clear();
                    continue;
                }
                segment.arguments = std::mem::take(&mut segment.arguments)
                    .into_iter()
                    .map(|argument| {
                        let value = match argument {
                            KotlinTypeArgument::Any => unreachable!(),
                            KotlinTypeArgument::Exact(value)
                            | KotlinTypeArgument::Extends(value)
                            | KotlinTypeArgument::Super(value) => value,
                        };
                        KotlinTypeArgument::Exact(value)
                    })
                    .collect();
            }
        }
        ty
    }

    fn source_expression_type(&self, value: &SemanticExpression) -> Option<KotlinType> {
        if self.is_this(value) {
            return self.source_current_type.clone();
        }
        if let SemanticExpression::Select {
            when_true,
            when_false,
            ..
        } = value
        {
            let is_null = |branch: &SemanticExpression| {
                branch.literal_value() == Some(0)
                    && branch.declared_type().is_some_and(ArgType::is_reference)
            };
            let joined = match (is_null(when_true), is_null(when_false)) {
                (true, false) => self.source_expression_type(when_false),
                (false, true) => self.source_expression_type(when_true),
                _ => self
                    .source_expression_type(when_true)
                    .zip(self.source_expression_type(when_false))
                    .and_then(|(left, right)| {
                        self.type_relations().least_upper_bound(&left, &right)
                    }),
            };
            if joined.is_some() {
                return joined;
            }
        }
        let declared = value
            .as_operation()
            .and_then(|operation| self.declared_operation_source_type(operation));
        let analyzed = Self::expression_value(value)
            .and_then(|value| self.source_value_types.get(&value))
            .cloned();
        match (declared, analyzed) {
            (Some(declared), Some(analyzed)) if Self::same_erasure(&declared, &analyzed) => {
                return GenericTypeEvidence::reconcile_type(
                    &declared,
                    &analyzed,
                    self.source_types.get(&ArgType::object("java/lang/Object")),
                )
                .or(Some(declared));
            }
            (Some(declared), _) => return Some(declared),
            (None, Some(analyzed)) => return Some(analyzed),
            (None, None) => {}
        }
        if let Some(source_type) = value
            .as_register()
            .and_then(|register| self.source_register_type(register))
        {
            return Some(source_type.clone());
        }
        if let Some(source_type) = value
            .as_operation()
            .and_then(|operation| operation.result.as_ref())
            .and_then(|register| self.source_register_type(register))
        {
            return Some(source_type.clone());
        }
        value
            .declared_type()
            .and_then(|ty| self.source_type(ty).ok())
    }

    fn source_requirement_type(&self, value: &SemanticExpression) -> Option<&KotlinType> {
        let register = value.as_register().or_else(|| {
            value
                .as_operation()
                .and_then(|operation| operation.result.as_ref())
        })?;
        crate::ir::analysis::SsaVar::from_reg(register)
            .and_then(|value| self.source_value_requirements.get(&value))
            .or_else(|| {
                register
                    .code_var
                    .and_then(|variable| self.source_variable_requirements.get(&variable))
            })
    }

    fn declared_operation_source_type(&self, operation: &SemanticOperation) -> Option<KotlinType> {
        match operation.insn_type {
            InsnType::Invoke => self.intrinsic_invocation_source_type(operation),
            InsnType::Iget | InsnType::Sget => {
                operation
                    .payload
                    .reference
                    .as_ref()
                    .and_then(|reference| match reference {
                        MemberReference::Field(field) => {
                            self.outer_instance_fields.get(field).cloned().or_else(|| {
                                self.source_field_type(field, operation.operands().first())
                            })
                        }
                        MemberReference::Method(_) => None,
                    })
            }
            InsnType::ConstClass => operation
                .payload
                .class_type
                .as_ref()
                .and_then(|represented| self.class_literal_source_type(represented)),
            InsnType::Constructor => operation
                .allocation_type()
                .and_then(|owner| self.source_object_types.get(owner).cloned()),
            InsnType::CheckCast => self.reference_cast_source_type(operation),
            InsnType::Move => operation
                .operands()
                .first()
                .and_then(|operand| self.source_expression_type(operand)),
            _ => None,
        }
    }

    fn source_field_type(
        &self,
        field: &FieldReference,
        receiver: Option<&SemanticExpression>,
    ) -> Option<KotlinType> {
        if let Some(contract) = self.generic_fields.get(field) {
            let mut solver = self.solver(&contract.owner, &[]);
            if let Some(receiver) = receiver {
                let declared_owner = JvmTypeSignature::ClassType(contract.owner.clone()).erased();
                self.constrain_invocation_owner(
                    &mut solver,
                    &declared_owner,
                    &contract.owner,
                    receiver,
                );
            }
            if solver.owner_is_raw(&contract.owner) {
                return self.source_type(&field.field_type).ok();
            }
            if let Some(ty) = solver.instantiate(&contract.signature) {
                return Some(ty);
            }
        }
        self.source_field_types.get(field).cloned()
    }

    fn intrinsic_invocation_source_type(
        &self,
        operation: &SemanticOperation,
    ) -> Option<KotlinType> {
        let method = Self::method(operation.payload.reference.as_ref()).ok()?;
        let (mut solver, arguments, contract) = self.invocation_solver(operation)?;
        if solver.owner_is_raw(&contract.owner)
            || contract
                .signature
                .parameter_types
                .iter()
                .zip(arguments)
                .any(|(formal, actual)| {
                    self.source_expression_type(actual).is_some_and(|actual| {
                        GenericInvocationCompatibility::requires_unchecked_conversion(
                            formal,
                            &actual,
                            &contract,
                            &self.source_types,
                        )
                    })
                })
        {
            return self.source_type(&method.descriptor.return_type).ok();
        }
        if !solver.satisfies_declared_bounds(&contract.signature.type_parameters) {
            return self.source_type(&method.descriptor.return_type).ok();
        }
        solver.complete_with_bounds(&contract.signature.type_parameters);
        solver.instantiate(&contract.signature.return_type)
    }

    fn generic_argument_source_type(
        &self,
        value: &SemanticExpression,
        erased_formal: &ArgType,
    ) -> Option<KotlinType> {
        if erased_formal.is_reference() && Self::constant(value) == Some(0) {
            return None;
        }
        let inferred = self.source_expression_type(value).or_else(|| {
            Self::expression_value(value)
                .and_then(|value| self.source_value_types.get(&value))
                .cloned()
        });
        let declared = value
            .as_operation()
            .filter(|operation| operation.insn_type == InsnType::Constructor)
            .and_then(|operation| Self::method(operation.payload.reference.as_ref()).ok())
            .and_then(|method| {
                self.source_object_types
                    .get(&method.owner)
                    .cloned()
                    .or_else(|| self.source_type(&method.owner).ok())
            });
        match (declared, inferred) {
            (Some(declared), Some(inferred)) => GenericTypeEvidence::reconcile_type(
                &declared,
                &inferred,
                self.source_types.get(&ArgType::object("java/lang/Object")),
            )
            .or(Some(declared)),
            (Some(declared), None) => Some(declared),
            (None, inferred) => inferred,
        }
    }

    fn generic_inference_argument_source_type(
        &self,
        value: &SemanticExpression,
        erased_formal: &ArgType,
    ) -> Option<KotlinType> {
        self.generic_argument_source_type(value, erased_formal)
            .filter(|ty| !self.is_raw_generic_type(ty))
    }

    fn is_raw_generic_type(&self, ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Array(element) => self.is_raw_generic_type(element),
            KotlinType::Class(class) => {
                let Some(erased) = self.source_erasure(ty) else {
                    return false;
                };
                self.generic_type_projection
                    .as_deref()
                    .and_then(|projection| projection.declared_type_parameters(&erased))
                    .is_some_and(|parameters| {
                        !parameters.is_empty()
                            && class.segments.last().is_some_and(|segment| {
                                segment.arguments.is_empty()
                                    || segment
                                        .arguments
                                        .iter()
                                        .all(|argument| matches!(argument, KotlinTypeArgument::Any))
                            })
                    })
            }
            KotlinType::Variable(_) | KotlinType::Primitive(_) => false,
        }
    }

    fn expression_value(value: &SemanticExpression) -> Option<crate::ir::analysis::SsaVar> {
        value
            .as_register()
            .or_else(|| {
                value
                    .as_operation()
                    .and_then(|operation| operation.result.as_ref())
            })
            .and_then(crate::ir::analysis::SsaVar::from_reg)
    }

    fn argument_requirement(
        &self,
        value: &SemanticExpression,
        erased: &ArgType,
    ) -> Option<KotlinType> {
        let requirement = self.generic_argument_source_type(value, erased)?;
        if !self.has_generic_argument_evidence(&requirement) {
            return None;
        }
        let erased = self.source_type(erased).ok()?.into_star_projection();
        Self::source_return_requires_cast(&requirement, &erased).then_some(requirement)
    }

    fn intrinsic_source_type(&self, value: &SemanticExpression) -> Option<KotlinType> {
        match value {
            SemanticExpression::Register(register)
                if register.code_var == self.this_code_var && self.this_code_var.is_some() =>
            {
                self.source_current_type
                    .clone()
                    .or_else(|| self.source_type(&register.ty).ok())
            }
            SemanticExpression::Register(register) => self
                .source_register_type(register)
                .cloned()
                .or_else(|| self.source_type(&register.ty).ok()),
            SemanticExpression::Literal(_) => None,
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let left = self.intrinsic_source_type(when_true)?;
                let right = self.intrinsic_source_type(when_false)?;
                (left == right).then_some(left)
            }
            SemanticExpression::Operation(operation) => match operation.insn_type {
                InsnType::Iget | InsnType::Sget => {
                    operation
                        .payload
                        .reference
                        .as_ref()
                        .and_then(|reference| match reference {
                            MemberReference::Field(field) => self
                                .source_field_type(field, operation.operands().first())
                                .or_else(|| self.source_type(&field.field_type).ok()),
                            MemberReference::Method(_) => None,
                        })
                }
                InsnType::Constructor => {
                    let owner = operation.allocation_type()?;
                    self.source_object_types
                        .get(owner)
                        .cloned()
                        .or_else(|| self.source_type(owner).ok())
                }
                InsnType::ConstClass => operation
                    .payload
                    .class_type
                    .as_ref()
                    .and_then(|represented| self.class_literal_source_type(represented)),
                InsnType::CheckCast => self.reference_cast_source_type(operation),
                InsnType::Move => operation
                    .operands()
                    .first()
                    .and_then(|operand| self.intrinsic_source_type(operand)),
                InsnType::Aget => operation
                    .operands()
                    .first()
                    .and_then(|array| self.intrinsic_source_type(array))
                    .and_then(|array| match array {
                        KotlinType::Array(element) => Some(element.into_type()),
                        KotlinType::Class(_)
                        | KotlinType::Variable(_)
                        | KotlinType::Primitive(_) => None,
                    }),
                InsnType::Invoke => {
                    self.intrinsic_invocation_source_type(operation)
                        .or_else(|| {
                            let method = Self::method(operation.payload.reference.as_ref()).ok()?;
                            self.source_type(&method.descriptor.return_type).ok()
                        })
                }
                _ => operation
                    .result
                    .as_ref()
                    .and_then(|result| self.source_type(&result.ty).ok()),
            },
        }
    }

    fn cast_source_type(&self, value: &SemanticExpression) -> Option<KotlinType> {
        self.definition_source_type(value)
            .or_else(|| self.intrinsic_source_type(value))
            .or_else(|| self.source_expression_type(value))
    }

    fn definition_source_type(&self, value: &SemanticExpression) -> Option<KotlinType> {
        match value {
            SemanticExpression::Register(register) => {
                crate::ir::analysis::SsaVar::from_reg(register)
                    .and_then(|value| self.source_value_definition_types.get(&value))
                    .or_else(|| {
                        register.code_var.and_then(|variable| {
                            self.source_variable_definition_types.get(&variable)
                        })
                    })
                    .cloned()
            }
            SemanticExpression::Operation(operation) => {
                self.intrinsic_source_type(value).or_else(|| {
                    operation
                        .result
                        .as_ref()
                        .and_then(crate::ir::analysis::SsaVar::from_reg)
                        .and_then(|value| self.source_value_definition_types.get(&value))
                        .cloned()
                })
            }
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                let left = self.definition_source_type(when_true)?;
                let right = self.definition_source_type(when_false)?;
                (left == right).then_some(left)
            }
            SemanticExpression::Literal(_) => None,
        }
    }

    fn reference_cast_source_type(&self, operation: &SemanticOperation) -> Option<KotlinType> {
        let target = operation.conversion_type()?;
        target.is_reference().then_some(())?;
        if let Some(result) = operation
            .result
            .as_ref()
            .and_then(|result| self.source_register_type(result))
            .filter(|result| self.source_erasure(result).as_ref() == Some(target))
        {
            return Some(result.clone());
        }
        let operand = operation.operands().first()?;
        let actual = self.source_expression_type(operand);
        if let Some(actual) = actual.as_ref() {
            if self.source_erasure(actual).as_ref() == Some(target) {
                return Some(actual.clone());
            }
            if GenericCast::has_generic_evidence(actual) {
                if let Some(specialized) = self
                    .generic_type_projection
                    .as_deref()
                    .and_then(|projection| projection.infer_subtype(target, actual))
                {
                    return Some(specialized);
                }
            }
        }
        self.source_type(target).ok()
    }

    fn source_check_cast_is_redundant(
        &self,
        operation: &SemanticOperation,
        target: &KotlinType,
    ) -> bool {
        operation
            .operands()
            .first()
            .and_then(|operand| self.intrinsic_source_type(operand))
            .is_some_and(|source| self.source_assignable_to(&source, target))
    }

    fn declared_expression_erasure(value: &SemanticExpression) -> Option<&ArgType> {
        match value {
            SemanticExpression::Operation(operation) => match operation.insn_type {
                InsnType::Invoke => Self::method(operation.payload.reference.as_ref())
                    .ok()
                    .map(|method| &method.descriptor.return_type),
                InsnType::Move => operation
                    .operands()
                    .first()
                    .and_then(Self::declared_expression_erasure),
                InsnType::CheckCast => operation.conversion_type(),
                InsnType::Constructor => Self::method(operation.payload.reference.as_ref())
                    .ok()
                    .map(|method| &method.owner),
                _ => value.declared_type(),
            },
            _ => value.declared_type(),
        }
    }

    fn expression_declares_parameterized_type(&self, value: &SemanticExpression) -> bool {
        match value {
            SemanticExpression::Register(register) => self
                .source_register_type(register)
                .is_some_and(GenericCast::is_parameterized),
            SemanticExpression::Literal(_) => false,
            SemanticExpression::Select {
                when_true,
                when_false,
                ..
            } => {
                self.expression_declares_parameterized_type(when_true)
                    || self.expression_declares_parameterized_type(when_false)
            }
            SemanticExpression::Operation(operation) => match operation.insn_type {
                InsnType::Invoke | InsnType::Constructor => operation
                    .payload
                    .reference
                    .as_ref()
                    .and_then(|reference| match reference {
                        MemberReference::Method(method) => self.generic_methods.get(method),
                        MemberReference::Field(_) => None,
                    })
                    .is_some_and(|contract| {
                        let signature = invocation_expression_signature(operation, contract);
                        Self::signature_is_parameterized(signature.as_ref())
                    }),
                InsnType::Iget | InsnType::Sget => operation
                    .payload
                    .reference
                    .as_ref()
                    .and_then(|reference| match reference {
                        MemberReference::Field(field) => self.generic_fields.get(field),
                        MemberReference::Method(_) => None,
                    })
                    .is_some_and(|contract| Self::signature_is_parameterized(&contract.signature)),
                InsnType::ConstClass => true,
                InsnType::Move | InsnType::CheckCast => operation
                    .operands()
                    .first()
                    .is_some_and(|operand| self.expression_declares_parameterized_type(operand)),
                _ => false,
            },
        }
    }

    fn expression_declares_concrete_generic_type(&self, value: &SemanticExpression) -> bool {
        let Some(operation) = value.as_operation() else {
            return false;
        };
        if matches!(operation.insn_type, InsnType::Move | InsnType::CheckCast) {
            return operation
                .operands()
                .first()
                .is_some_and(|operand| self.expression_declares_concrete_generic_type(operand));
        }
        let Some(reference) = operation.payload.reference.as_ref() else {
            return false;
        };
        match reference {
            MemberReference::Method(method)
                if matches!(
                    operation.insn_type,
                    InsnType::Invoke | InsnType::Constructor
                ) =>
            {
                self.generic_methods.get(method).is_some_and(|contract| {
                    let signature = invocation_expression_signature(operation, contract);
                    GenericInvocationCompatibility::has_concrete_type_argument(signature.as_ref())
                })
            }
            MemberReference::Field(field)
                if matches!(operation.insn_type, InsnType::Iget | InsnType::Sget) =>
            {
                self.generic_fields.get(field).is_some_and(|contract| {
                    GenericInvocationCompatibility::has_concrete_type_argument(&contract.signature)
                })
            }
            MemberReference::Method(_) | MemberReference::Field(_) => false,
        }
    }

    fn signature_is_parameterized(signature: &JvmTypeSignature) -> bool {
        match signature {
            JvmTypeSignature::TypeVariable(_) => true,
            JvmTypeSignature::Array(element) => Self::signature_is_parameterized(element),
            JvmTypeSignature::ClassType(class) => {
                !class.type_arguments.is_empty()
                    || class
                        .inner_segments
                        .iter()
                        .any(|segment| !segment.type_arguments.is_empty())
            }
            JvmTypeSignature::BaseType(_) => false,
        }
    }

    fn class_literal_source_type(&self, represented: &ArgType) -> Option<KotlinType> {
        let represented = self.source_type(represented).ok()?.into_star_projection();
        let KotlinType::Class(mut class) = self
            .source_type(&ArgType::object("java/lang/Class"))
            .ok()?
            .into_star_projection()
        else {
            return None;
        };
        class.segments.last_mut()?.arguments = vec![KotlinTypeArgument::Exact(represented)];
        Some(KotlinType::Class(class))
    }

    fn is_function_object_expression(&self, value: &SemanticExpression) -> bool {
        let constructed_type = value
            .as_operation()
            .filter(|operation| operation.insn_type == InsnType::Constructor)
            .and_then(|operation| operation.payload.reference.as_ref())
            .and_then(|reference| match reference {
                MemberReference::Method(method) => Some(&method.owner),
                MemberReference::Field(_) => None,
            });
        if constructed_type.is_some_and(|owner| self.source_object_types.contains_key(owner)) {
            return true;
        }
        value
            .declared_type()
            .filter(|ty| self.source_object_types.contains_key(*ty))
            .is_some()
            || self
                .source_expression_type(value)
                .and_then(|ty| self.source_erasure(&ty))
                .is_some_and(|owner| self.source_object_types.contains_key(&owner))
    }

    fn source_erasure(&self, source: &KotlinType) -> Option<ArgType> {
        self.type_relations().erasure_of(source)
    }

    fn source_assignable_to(&self, source: &KotlinType, target: &KotlinType) -> bool {
        self.type_relations().is_assignable(source, target)
    }

    fn type_relations(&self) -> KotlinTypeRelations<'_> {
        KotlinTypeRelations::new(
            &self.source_types,
            &self.source_type_erasures,
            self.generic_type_projection.as_deref(),
        )
        .with_variable_bounds(Some(&self.source_type_bounds))
    }

    fn solver<'a>(
        &'a self,
        owner: &ClassTypeSignature,
        parameters: &[TypeParameter],
    ) -> GenericTypeSolver<'a> {
        let solver = GenericTypeSolver::new(&self.source_types)
            .with_local_owner_variables(owner)
            .with_inference_variables(parameters)
            .with_lexical_scope(
                self.current_type.as_ref(),
                owner,
                &self.source_type_erasures,
                &self.source_type_bounds,
            )
            .with_projection(self.generic_type_projection.as_deref());
        solver
    }

    fn accepts_target_type(&self, value: &SemanticExpression, target: &KotlinType) -> bool {
        if self
            .intrinsic_source_type(value)
            .is_some_and(|source| self.source_assignable_to(&source, target))
        {
            return true;
        }
        if self.is_function_object_expression(value) {
            return true;
        }
        let Some(operation) = value.as_operation() else {
            return false;
        };
        if matches!(operation.insn_type, InsnType::Move | InsnType::CheckCast) {
            return operation
                .operands()
                .first()
                .is_some_and(|operand| self.accepts_target_type(operand, target));
        }
        if operation.insn_type != InsnType::Invoke {
            return false;
        }
        let Some(MemberReference::Method(method)) = operation.payload.reference.as_ref() else {
            return false;
        };
        let Some(contract) = self.generic_methods.get(method) else {
            return false;
        };
        let Some(invoke_type) = operation.payload.invoke_type else {
            return false;
        };
        let is_static = invoke_type == InvokeType::Static;
        let mut constraints = self.solver(&contract.owner, &contract.signature.type_parameters);
        if !is_static {
            if let Some(receiver) = operation.operands().first() {
                self.constrain_invocation_owner(
                    &mut constraints,
                    &method.owner,
                    &contract.owner,
                    receiver,
                );
            }
        }
        if constraints.owner_is_raw(&contract.owner) {
            return false;
        }
        for ((formal, erased), actual) in contract
            .signature
            .parameter_types
            .iter()
            .zip(&method.descriptor.parameters)
            .zip(operation.operands().iter().skip(usize::from(!is_static)))
        {
            if let Some(actual) = self.generic_argument_source_type(actual, erased) {
                if self.source_erasure(&actual).as_ref() == Some(erased)
                    && GenericInvocationCompatibility::requires_unchecked_conversion(
                        formal,
                        &actual,
                        contract,
                        &self.source_types,
                    )
                {
                    return false;
                }
                constraints.constrain(formal, &actual);
            }
        }
        if constraints
            .instantiate(&contract.signature.return_type)
            .is_some_and(|actual| {
                self.has_generic_argument_evidence(&actual)
                    && !self.source_assignable_to(&actual, target)
            })
        {
            return false;
        }
        constraints.constrain_context(&contract.signature.return_type, target);
        constraints.complete_with_bounds(&contract.signature.type_parameters);
        if !constraints.satisfies_declared_bounds(&contract.signature.type_parameters) {
            return false;
        }
        if !is_static {
            if let Some(receiver) = operation.operands().first() {
                if receiver
                    .as_operation()
                    .is_some_and(|receiver| receiver.insn_type == InsnType::Invoke)
                {
                    if let Some(owner) = self
                        .owner_inferred_from_arguments(operation, method, contract, Some(target))
                        .or_else(|| constraints.owner_type(&contract.owner))
                    {
                        if !self.accepts_target_type(receiver, &owner) {
                            return false;
                        }
                    }
                }
            }
        }
        constraints
            .instantiate(&contract.signature.return_type)
            .as_ref()
            == Some(target)
    }

    fn source_receiver_type(&self, value: &SemanticExpression) -> Option<KotlinType> {
        self.source_expression_type(value)
    }

    fn same_erasure(left: &KotlinType, right: &KotlinType) -> bool {
        match (left, right) {
            (KotlinType::Class(left), KotlinType::Class(right)) => left.name() == right.name(),
            (KotlinType::Array(left), KotlinType::Array(right)) => Self::same_erasure(left, right),
            (KotlinType::Primitive(left), KotlinType::Primitive(right)) => left == right,
            _ => left == right,
        }
    }

    fn has_generic_argument_evidence(&self, ty: &KotlinType) -> bool {
        let KotlinType::Class(class) = ty else {
            return matches!(ty, KotlinType::Variable(_) | KotlinType::Array(_));
        };
        class.segments.iter().any(|segment| {
            segment.arguments.iter().any(|argument| match argument {
                KotlinTypeArgument::Any => false,
                KotlinTypeArgument::Exact(value)
                | KotlinTypeArgument::Extends(value)
                | KotlinTypeArgument::Super(value) => self.type_argument_has_evidence(value),
            })
        })
    }

    fn type_argument_has_evidence(&self, ty: &KotlinType) -> bool {
        match ty {
            KotlinType::Variable(_) | KotlinType::Primitive(_) => true,
            KotlinType::Array(element) => self.type_argument_has_evidence(element),
            KotlinType::Class(class) => {
                if self.is_raw_generic_type(ty) {
                    return false;
                }
                let parameterized = class
                    .segments
                    .iter()
                    .any(|segment| !segment.arguments.is_empty());
                if parameterized {
                    self.has_generic_argument_evidence(ty)
                } else {
                    self.source_erasure(ty) != Some(ArgType::object("java/lang/Object"))
                }
            }
        }
    }

    fn has_only_default_type_arguments(&self, ty: &KotlinType) -> bool {
        let KotlinType::Class(class) = ty else {
            return false;
        };
        let arguments = class
            .segments
            .iter()
            .flat_map(|segment| &segment.arguments)
            .collect::<Vec<_>>();
        !arguments.is_empty()
            && arguments.into_iter().all(|argument| {
                let KotlinTypeArgument::Exact(KotlinType::Class(value)) = argument else {
                    return false;
                };
                let value = KotlinType::Class(value.clone());
                !GenericCast::is_parameterized(&value)
                    && self.source_erasure(&value) == Some(ArgType::object("java/lang/Object"))
            })
    }

    fn target_has_source_erasure(&self, source: &KotlinType, erased: &ArgType) -> bool {
        match (source, erased) {
            (KotlinType::Variable(variable), erased)
                if self.source_type_erasures.get(variable) == Some(erased) =>
            {
                return true;
            }
            (KotlinType::Array(source), ArgType::Array(erased))
                if self.target_has_source_erasure(source, erased) =>
            {
                return true;
            }
            _ => {}
        }
        self.source_type(erased)
            .ok()
            .is_some_and(|erased| Self::same_erasure(source, &erased))
            || (self.source_return_type.as_ref() == Some(source)
                && self.return_type.as_ref() == Some(erased))
    }

    fn source_register_type(&self, register: &RegisterArg) -> Option<&KotlinType> {
        register
            .code_var
            .and_then(|variable| self.binding_types.variable_type(variable))
            .or_else(|| {
                register
                    .code_var
                    .and_then(|variable| self.source_names.get(&variable))
                    .and_then(|name| self.binding_types.name_type(name))
            })
            .or_else(|| {
                SourceVariable::of(register)
                    .ok()
                    .and_then(|variable| self.names.get(&variable))
                    .and_then(|name| self.binding_types.name_type(name))
            })
            .or_else(|| {
                register
                    .code_var
                    .and_then(|variable| self.source_variable_types.get(&variable))
            })
            .or_else(|| {
                crate::ir::analysis::SsaVar::from_reg(register)
                    .and_then(|value| self.source_value_types.get(&value))
            })
    }

    fn source_definition_type(&self, register: &RegisterArg) -> Option<KotlinType> {
        let variable_type = self.source_register_type(register);
        let value_type = crate::ir::analysis::SsaVar::from_reg(register)
            .and_then(|value| self.source_value_types.get(&value));
        let source = match (variable_type, value_type) {
            (Some(variable), Some(value))
                if Self::same_erasure(variable, value)
                    && !self.source_assignable_to(value, variable)
                    && !self.source_assignable_to(variable, value) =>
            {
                Some(variable.clone().into_star_projection())
            }
            (Some(variable), _) => Some(variable.clone()),
            (None, Some(value)) => Some(value.clone()),
            (None, None) => None,
        }?;
        let erased = self
            .types
            .register_type(register)
            .ok()
            .unwrap_or(&register.ty);
        Some(self.kotlin_source_type(erased, source))
    }

    fn constructor_invocation(
        &mut self,
        insn: &SemanticOperation,
    ) -> Result<KotlinStmt, KotlinLoweringError> {
        let method = Self::method(insn.payload.reference.as_ref())?;
        let receiver = insn
            .operands()
            .first()
            .and_then(SemanticExpression::as_register)
            .ok_or(KotlinLoweringError::InvalidConstructorReceiver)?;
        if receiver.code_var != self.this_code_var {
            return Err(KotlinLoweringError::UnrecoveredObjectInitialization(
                insn.offset,
            ));
        }
        let target = if self.current_type.as_ref() == Some(&method.owner) {
            KotlinConstructorTarget::This
        } else {
            KotlinConstructorTarget::Super
        };
        let source_argument_types = self
            .invocation_solver(insn)
            .map(|(mut solver, _, contract)| {
                if matches!(target, KotlinConstructorTarget::Super) {
                    if let Some(super_type) = self.source_super_type.as_ref().filter(|super_type| {
                        self.source_erasure(super_type).as_ref() == Some(&method.owner)
                    }) {
                        solver.constrain_owner(&contract.owner, super_type);
                    }
                }
                contract
                    .signature
                    .parameter_types
                    .iter()
                    .map(|formal| solver.invocation_input_type(formal))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let call_arguments = insn.operands().iter().skip(1).cloned().collect::<Vec<_>>();
        let overload_casts = self.overload_argument_casts(method, &call_arguments);
        let lowered = insn
            .operands()
            .iter()
            .skip(1)
            .enumerate()
            .map(|(index, arg)| match method.descriptor.parameters.get(index) {
                Some(expected) => {
                    let target_type = source_argument_types
                        .get(index)
                        .and_then(Option::as_ref)
                        .cloned();
                    let expression = match target_type.as_ref() {
                        Some(source) => self.arg_as_source_target(arg, expected, source),
                        None => self.arg_as(arg, expected),
                    };
                    expression.and_then(|expression| {
                        let needs_overload_cast = overload_casts.contains(&index)
                            && !matches!(&expression, KotlinExpr::Cast { ty, .. } if self.source_erasure(ty).as_ref() == Some(expected));
                        let needs_null_cast = expected.is_reference()
                            && matches!(&expression, KotlinExpr::Literal(KotlinLiteral::Null));
                        let expression = if needs_overload_cast || needs_null_cast {
                            KotlinExpr::Cast {
                                ty: if needs_overload_cast {
                                    self.overload_cast_type(expected, target_type.as_ref())?
                                } else {
                                    target_type.clone().unwrap_or(self.source_type(expected)?)
                                },
                                value: Box::new(expression),
                            }
                        } else {
                            expression
                        };
                        self.disambiguate_null_argument(method, index, expected, expression)
                    })
                }
                None => self.arg(arg),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let default = self
            .default_calls
            .get(method)
            .filter(|contract| contract.is_constructor())
            .and_then(|contract| {
                DefaultArguments::new(contract, &lowered, 0)
                    .recover()
                    .filter(|recovered| {
                        recovered.is_positional(contract.target().descriptor.parameters.len(), None)
                    })
                    .map(|recovered| (contract.target(), recovered.values))
            });
        let (source_constructor, lowered) = default.unwrap_or((method, lowered));
        let hidden = self
            .member_names
            .hidden_constructor_parameters(source_constructor)
            .cloned()
            .unwrap_or_default();
        Ok(KotlinStmt::ConstructorInvocation {
            target,
            args: lowered
                .into_iter()
                .enumerate()
                .filter_map(|(index, argument)| {
                    if hidden.contains(&index) {
                        None
                    } else {
                        Some(argument)
                    }
                })
                .collect(),
        })
    }

    fn comparison(&mut self, insn: &SemanticOperation) -> Result<KotlinExpr, KotlinLoweringError> {
        let left_arg = insn
            .operands()
            .first()
            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
        let right_arg = insn
            .operands()
            .get(1)
            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
        let comparison_type = self.expression_type(left_arg)?.clone();
        let left = self.arg_as(left_arg, &comparison_type)?;
        let right = self.arg_as(right_arg, &comparison_type)?;
        let owner = match &comparison_type {
            ArgType::Primitive(PrimitiveType::Float) => "java/lang/Float",
            ArgType::Primitive(PrimitiveType::Double) => "java/lang/Double",
            ArgType::Primitive(PrimitiveType::Long) => "java/lang/Long",
            other => return Err(KotlinLoweringError::InvalidComparisonType(other.clone())),
        };
        let owner_type = self.source_type(&ArgType::object(owner))?;
        if owner == "java/lang/Long" {
            return Ok(KotlinExpr::Call {
                receiver: None,
                owner: Some(owner_type),
                type_arguments: Vec::new(),
                method: KotlinIdentifier::from_dex("compare"),
                args: vec![left, right].into(),
            });
        }
        let nan_value = match insn.payload.cmp_bias {
            Some(crate::ir::CmpBias::Lt) => -1,
            Some(crate::ir::CmpBias::Gt) => 1,
            Some(crate::ir::CmpBias::None) | None => {
                return Err(KotlinLoweringError::MissingPayload {
                    instruction: insn.insn_type,
                    field: "cmp_bias",
                });
            }
        };
        let is_nan = |value| KotlinExpr::Call {
            receiver: None,
            owner: Some(owner_type.clone()),
            type_arguments: Vec::new(),
            method: KotlinIdentifier::from_dex("isNaN"),
            args: vec![value].into(),
        };
        Ok(KotlinExpr::Conditional {
            condition: Box::new(KotlinExpr::Binary {
                left: Box::new(is_nan(left.clone())),
                op: KotlinBinaryOp::LogicalOr,
                right: Box::new(is_nan(right.clone())),
            }),
            when_true: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(nan_value))),
            when_false: Box::new(KotlinExpr::Conditional {
                condition: Box::new(KotlinExpr::Binary {
                    left: Box::new(left.clone()),
                    op: KotlinBinaryOp::Less,
                    right: Box::new(right.clone()),
                }),
                when_true: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(-1))),
                when_false: Box::new(KotlinExpr::Conditional {
                    condition: Box::new(KotlinExpr::Binary {
                        left: Box::new(left),
                        op: KotlinBinaryOp::Equal,
                        right: Box::new(right),
                    }),
                    when_true: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(0))),
                    when_false: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(1))),
                }),
            }),
        })
    }

    fn array_element_type<'a>(
        &'a self,
        insn: &'a SemanticOperation,
    ) -> Result<&'a ArgType, KotlinLoweringError> {
        let array_type = match &insn.result {
            Some(result) => self.types.ssa_type(result)?,
            None => {
                insn.payload
                    .class_type
                    .as_ref()
                    .ok_or(KotlinLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "result or class_type",
                    })?
            }
        };
        array_type
            .as_array_element()
            .ok_or_else(|| KotlinLoweringError::InvalidArrayType {
                instruction: insn.insn_type,
                offset: insn.offset,
                ty: array_type.clone(),
            })
    }

    fn fill_array(&mut self, insn: &SemanticOperation) -> Result<KotlinStmt, KotlinLoweringError> {
        let array_arg = insn
            .operands()
            .first()
            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
        let array = self.arg(array_arg)?;
        let array_type = self.ssa_expression_type(array_arg)?.clone();
        let element = array_type
            .as_array_element()
            .ok_or_else(|| KotlinLoweringError::InvalidArrayType {
                instruction: insn.insn_type,
                offset: insn.offset,
                ty: array_type.clone(),
            })?
            .clone();
        let data = insn
            .payload
            .fill_array_data
            .as_ref()
            .ok_or(KotlinLoweringError::MissingArrayData)?;
        let width = usize::from(data.element_width);
        if !matches!(width, 1 | 2 | 4 | 8) {
            return Err(KotlinLoweringError::InvalidArrayElementWidth(
                data.element_width,
            ));
        }
        let statements = data
            .data
            .chunks_exact(width)
            .take(data.size as usize)
            .enumerate()
            .map(|(index, bytes)| {
                let index = i32::try_from(index)
                    .map_err(|_| KotlinLoweringError::InvalidIntegerLiteral(index as i64))?;
                let bits = bytes.iter().enumerate().fold(0u64, |value, (shift, byte)| {
                    value | (u64::from(*byte) << (shift * 8))
                });
                let shift = 64 - width * 8;
                let signed = ((bits << shift) as i64) >> shift;
                let literal = if width == 8 {
                    KotlinLiteral::Long(signed)
                } else {
                    KotlinLiteral::Integer(
                        i32::try_from(signed)
                            .map_err(|_| KotlinLoweringError::InvalidIntegerLiteral(signed))?,
                    )
                };
                Ok(KotlinStmt::Assign {
                    target: KotlinExpr::ArrayAccess {
                        array: Box::new(array.clone()),
                        index: Box::new(KotlinExpr::Literal(KotlinLiteral::Integer(index))),
                    },
                    op: KotlinAssignOp::Assign,
                    value: self.coerce(KotlinExpr::Literal(literal), &element),
                })
            })
            .collect::<Result<Vec<_>, KotlinLoweringError>>()?;
        Ok(KotlinStmt::Block(statements))
    }

    fn predicate(
        &mut self,
        condition: &SemanticPredicate,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let mut pending = vec![KotlinPredicateTask::Visit(condition)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                KotlinPredicateTask::Visit(condition) => match condition {
                    SemanticPredicate::True => {
                        results.push(KotlinExpr::Literal(KotlinLiteral::Boolean(true)))
                    }
                    SemanticPredicate::False => {
                        results.push(KotlinExpr::Literal(KotlinLiteral::Boolean(false)))
                    }
                    SemanticPredicate::Test(test) => {
                        results.push(self.test_condition(test, false)?)
                    }
                    SemanticPredicate::Not(inner) => match inner.as_ref() {
                        SemanticPredicate::Test(test) => {
                            results.push(self.test_condition(test, true)?)
                        }
                        inner => {
                            pending.push(KotlinPredicateTask::Not);
                            pending.push(KotlinPredicateTask::Visit(inner));
                        }
                    },
                    SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                        let conjunction = matches!(condition, SemanticPredicate::And(_));
                        pending.push(KotlinPredicateTask::Junction {
                            count: terms.len(),
                            conjunction,
                        });
                        pending.extend(terms.iter().rev().map(KotlinPredicateTask::Visit));
                    }
                },
                KotlinPredicateTask::Not => {
                    let operand = results
                        .pop()
                        .ok_or(KotlinLoweringError::MalformedPredicate)?;
                    results.push(Self::negate_boolean(operand));
                }
                KotlinPredicateTask::Junction { count, conjunction } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(KotlinLoweringError::MalformedPredicate)?;
                    let mut terms = results.drain(start..).collect::<Vec<_>>();
                    if terms.is_empty() {
                        results.push(KotlinExpr::Literal(KotlinLiteral::Boolean(conjunction)));
                        continue;
                    }
                    let operator = if conjunction {
                        KotlinBinaryOp::LogicalAnd
                    } else {
                        KotlinBinaryOp::LogicalOr
                    };
                    while terms.len() > 1 {
                        let mut next = Vec::with_capacity(terms.len().div_ceil(2));
                        let mut current = std::mem::take(&mut terms).into_iter();
                        while let Some(left) = current.next() {
                            next.push(match current.next() {
                                Some(right) => KotlinExpr::Binary {
                                    left: Box::new(left),
                                    op: operator,
                                    right: Box::new(right),
                                },
                                None => left,
                            });
                        }
                        terms = next;
                    }
                    results.push(terms.pop().ok_or(KotlinLoweringError::MalformedPredicate)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(KotlinLoweringError::MalformedPredicate);
        }
        results.pop().ok_or(KotlinLoweringError::MalformedPredicate)
    }

    fn semantic_value(
        &mut self,
        value: &SemanticExpression,
        expected: &ArgType,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        if expected == &ArgType::BOOLEAN {
            return self.boolean_value(value);
        }
        if let SemanticExpression::Select {
            condition,
            when_true,
            when_false,
        } = value
        {
            let condition_is_pure = condition.effects().is_pure();
            let condition = self.predicate(condition)?;
            let when_true = self.semantic_value(when_true, expected)?;
            let when_false = self.semantic_value(when_false, expected)?;
            return Ok(if condition_is_pure && when_true == when_false {
                when_true
            } else {
                KotlinExpr::Conditional {
                    condition: Box::new(condition),
                    when_true: Box::new(when_true),
                    when_false: Box::new(when_false),
                }
            });
        }
        self.arg_as(value, expected)
    }

    fn boolean_value(
        &mut self,
        value: &SemanticExpression,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        if let Some(value) = Self::semantic_constant(value) {
            if matches!(value, 0 | 1) {
                return Ok(KotlinExpr::Literal(KotlinLiteral::Boolean(value != 0)));
            }
        }
        if let SemanticExpression::Operation(operation) = value {
            if operation.insn_type == InsnType::Move && operation.operands().len() == 1 {
                return self.boolean_value(&operation.operands()[0]);
            }
        }
        let SemanticExpression::Select {
            condition,
            when_true,
            when_false,
        } = value
        else {
            return self.arg_as(value, &ArgType::BOOLEAN);
        };
        let condition_is_pure = condition.effects().is_pure();
        let condition = self.predicate(condition)?;
        let when_true = self.boolean_value(when_true)?;
        let when_false = self.boolean_value(when_false)?;
        if condition_is_pure && when_true == when_false {
            return Ok(when_true);
        }
        Ok(match (&when_true, &when_false) {
            (
                KotlinExpr::Literal(KotlinLiteral::Boolean(true)),
                KotlinExpr::Literal(KotlinLiteral::Boolean(false)),
            ) => condition,
            (
                KotlinExpr::Literal(KotlinLiteral::Boolean(false)),
                KotlinExpr::Literal(KotlinLiteral::Boolean(true)),
            ) => Self::negate_boolean(condition),
            (KotlinExpr::Literal(KotlinLiteral::Boolean(true)), _) => KotlinExpr::Binary {
                left: Box::new(condition),
                op: KotlinBinaryOp::LogicalOr,
                right: Box::new(when_false),
            },
            (KotlinExpr::Literal(KotlinLiteral::Boolean(false)), _) => KotlinExpr::Binary {
                left: Box::new(Self::negate_boolean(condition)),
                op: KotlinBinaryOp::LogicalAnd,
                right: Box::new(when_false),
            },
            (_, KotlinExpr::Literal(KotlinLiteral::Boolean(true))) => KotlinExpr::Binary {
                left: Box::new(Self::negate_boolean(condition)),
                op: KotlinBinaryOp::LogicalOr,
                right: Box::new(when_true),
            },
            (_, KotlinExpr::Literal(KotlinLiteral::Boolean(false))) => KotlinExpr::Binary {
                left: Box::new(condition),
                op: KotlinBinaryOp::LogicalAnd,
                right: Box::new(when_true),
            },
            _ => KotlinExpr::Conditional {
                condition: Box::new(condition),
                when_true: Box::new(when_true),
                when_false: Box::new(when_false),
            },
        })
    }

    fn semantic_constant(value: &SemanticExpression) -> Option<i64> {
        Self::constant(value)
    }

    fn test_condition(
        &mut self,
        condition: &SemanticOperation,
        inverted: bool,
    ) -> Result<KotlinExpr, KotlinLoweringError> {
        let mut op = condition
            .payload
            .if_op
            .ok_or(KotlinLoweringError::MissingPayload {
                instruction: condition.insn_type,
                field: "if_op",
            })?;
        if inverted {
            op = op.invert();
        }
        let left_arg = condition
            .operands()
            .first()
            .ok_or(KotlinLoweringError::MissingArgument(InsnType::If))?;
        let right_arg = condition
            .operands()
            .get(1)
            .ok_or(KotlinLoweringError::MissingArgument(InsnType::If))?;
        if matches!(op, IfOp::Eq | IfOp::Ne) {
            if let Some(test) = self.boolean_test(left_arg, right_arg, op)? {
                return Ok(test);
            }
            if let Some(test) = self.boolean_test(right_arg, left_arg, op)? {
                return Ok(test);
            }
            if self.is_boolean_condition_value(left_arg)?
                && self.is_boolean_condition_value(right_arg)?
            {
                return Ok(KotlinExpr::Binary {
                    left: Box::new(self.boolean_value(left_arg)?),
                    op: if op == IfOp::Eq {
                        KotlinBinaryOp::Equal
                    } else {
                        KotlinBinaryOp::NotEqual
                    },
                    right: Box::new(self.boolean_value(right_arg)?),
                });
            }
        }
        if let Some(comparison) = self.direct_comparison(left_arg, right_arg, op)? {
            return Ok(comparison);
        }
        if self.has_intrinsic_numeric_comparison_domain(left_arg, right_arg)? {
            let comparison_type = self.numeric_comparison_type(left_arg, right_arg)?;
            let left = match comparison_type.as_ref() {
                Some(ty) => self.arg_as(left_arg, ty)?,
                None => self.arg(left_arg)?,
            };
            let right = match comparison_type.as_ref() {
                Some(ty) => self.arg_as(right_arg, ty)?,
                None => self.arg(right_arg)?,
            };
            return Ok(KotlinExpr::Binary {
                left: Box::new(left),
                op: Self::comparison_operator(op),
                right: Box::new(right),
            });
        }
        let mut left = self.comparison_arg(left_arg, right_arg)?;
        let right = self.comparison_arg(right_arg, left_arg)?;
        if matches!(op, IfOp::Eq | IfOp::Ne) {
            if let Some(bridge) = self.equality_bridge_type(left_arg, right_arg) {
                left = KotlinExpr::Cast {
                    ty: bridge,
                    value: Box::new(left),
                };
            }
        }
        let operator = if matches!(op, IfOp::Eq | IfOp::Ne)
            && (self.expression_type(left_arg)?.is_reference()
                || self.expression_type(right_arg)?.is_reference())
        {
            Self::referential_comparison_operator(op)
        } else {
            Self::comparison_operator(op)
        };
        Ok(KotlinExpr::Binary {
            left: Box::new(left),
            op: operator,
            right: Box::new(right),
        })
    }

    fn boolean_test(
        &mut self,
        value: &SemanticExpression,
        literal: &SemanticExpression,
        op: IfOp,
    ) -> Result<Option<KotlinExpr>, KotlinLoweringError> {
        let Some(expected) = Self::constant(literal)
            .filter(|value| matches!(value, 0 | 1))
            .map(|value| value == 1)
        else {
            return Ok(None);
        };
        if !self.is_boolean_condition_value(value)? {
            return Ok(None);
        }
        let value = self.boolean_value(value)?;
        let positive = (op == IfOp::Eq) == expected;
        Ok(Some(if positive {
            value
        } else {
            Self::negate_boolean(value)
        }))
    }

    fn equality_bridge_type(
        &self,
        left: &SemanticExpression,
        right: &SemanticExpression,
    ) -> Option<KotlinType> {
        let left = self.source_expression_type(left)?;
        let right = self.source_expression_type(right)?;
        if self.source_assignable_to(&left, &right) || self.source_assignable_to(&right, &left) {
            return None;
        }
        let left_erasure = self.source_erasure(&left)?;
        let right_erasure = self.source_erasure(&right)?;
        (left_erasure == right_erasure && left_erasure.is_reference())
            .then(|| {
                self.source_type(&left_erasure)
                    .ok()
                    .map(KotlinType::into_raw)
            })
            .flatten()
    }

    fn is_boolean_materialization(value: &SemanticExpression) -> bool {
        let SemanticExpression::Select {
            when_true,
            when_false,
            ..
        } = value
        else {
            return false;
        };
        Self::is_boolean_arm(when_true) && Self::is_boolean_arm(when_false)
    }

    fn is_boolean_condition_value(
        &self,
        value: &SemanticExpression,
    ) -> Result<bool, KotlinLoweringError> {
        if Self::is_boolean_materialization(value) {
            return Ok(true);
        }
        if value
            .as_operation()
            .is_some_and(|operation| self.arithmetic_is_boolean(operation))
        {
            return Ok(true);
        }
        if let Some(primitive) = Self::intrinsic_primitive_type(value) {
            return Ok(primitive == PrimitiveType::Boolean);
        }
        if self.is_boolean_arg(value)? {
            return Ok(true);
        }
        let SemanticExpression::Select {
            when_true,
            when_false,
            ..
        } = value
        else {
            return Ok(false);
        };
        Ok(self.is_boolean_condition_value(when_true)?
            && self.is_boolean_condition_value(when_false)?)
    }

    fn is_boolean_arm(value: &SemanticExpression) -> bool {
        matches!(Self::constant(value), Some(0) | Some(1))
            || Self::intrinsic_primitive_type(value) == Some(PrimitiveType::Boolean)
            || Self::is_boolean_materialization(value)
    }

    fn direct_comparison(
        &mut self,
        left: &SemanticExpression,
        right: &SemanticExpression,
        op: IfOp,
    ) -> Result<Option<KotlinExpr>, KotlinLoweringError> {
        let (comparison, op) = if Self::constant(right) == Some(0) {
            (Self::comparison_instruction(left), op)
        } else if Self::constant(left) == Some(0) {
            (
                Self::comparison_instruction(right),
                Self::swap_comparison(op),
            )
        } else {
            return Ok(None);
        };
        let Some(comparison) = comparison else {
            return Ok(None);
        };
        let left = comparison
            .operands()
            .first()
            .ok_or(KotlinLoweringError::MissingArgument(InsnType::Cmp))?;
        let right = comparison
            .operands()
            .get(1)
            .ok_or(KotlinLoweringError::MissingArgument(InsnType::Cmp))?;
        let comparison_type = self.expression_type(left)?.clone();
        let Some(test) =
            ComparisonSemantics::recover(comparison.payload.cmp_bias, &comparison_type, op)
        else {
            return Ok(None);
        };
        let expression = KotlinExpr::Binary {
            left: Box::new(self.arg_as(left, &comparison_type)?),
            op: Self::comparison_operator(test.operator),
            right: Box::new(self.arg_as(right, &comparison_type)?),
        };
        Ok(Some(if test.negated {
            KotlinExpr::Unary {
                op: KotlinUnaryOp::LogicalNot,
                operand: Box::new(expression),
            }
        } else {
            expression
        }))
    }

    fn comparison_instruction(mut argument: &SemanticExpression) -> Option<&SemanticOperation> {
        loop {
            let SemanticExpression::Operation(instruction) = argument else {
                return None;
            };
            if instruction.insn_type == InsnType::Cmp {
                return Some(instruction);
            }
            if instruction.insn_type != InsnType::Move || instruction.operands().len() != 1 {
                return None;
            }
            argument = &instruction.operands()[0];
        }
    }

    fn swap_comparison(op: IfOp) -> IfOp {
        match op {
            IfOp::Eq | IfOp::Ne => op,
            IfOp::Lt => IfOp::Gt,
            IfOp::Ge => IfOp::Le,
            IfOp::Gt => IfOp::Lt,
            IfOp::Le => IfOp::Ge,
        }
    }

    fn negate_boolean(expression: KotlinExpr) -> KotlinExpr {
        expression.negated()
    }

    fn assignment(
        &mut self,
        result: &RegisterArg,
        value: KotlinExpr,
    ) -> Result<KotlinStmt, KotlinLoweringError> {
        let inferred_type = self.types.register_type(result)?.clone();
        let value = self.coerce(value, &inferred_type);
        let name = self.register_name(result)?;
        let key = SourceVariable::of(result)?;
        if !self.declared.contains(&name) {
            let ty = self
                .source_definition_type(result)
                .map(Ok)
                .unwrap_or_else(|| self.source_type(&inferred_type))?;
            let ty = self.kotlin_source_type(&inferred_type, ty);
            if self.inline_declarations.contains(&key) {
                self.declared.insert(name.clone());
                self.binding_types.bind_name(name.clone(), ty.clone());
                return Ok(KotlinStmt::Variable {
                    binding: Default::default(),
                    ty,
                    name,
                    value: Some(value),
                });
            }
            self.binding_types.bind_name(name.clone(), ty.clone());
            self.locals.entry(name.clone()).or_insert(ty);
        }
        Ok(LocalAssignment::recover(&name, value).into_statement(name))
    }

    fn is_implicit_enclosing_instance(
        &self,
        expression: &KotlinExpr,
        expected: Option<&ArgType>,
    ) -> bool {
        let Some(expected) = expected else {
            return false;
        };
        match expression {
            KotlinExpr::QualifiedThis(outer) => self
                .source_type(expected)
                .is_ok_and(|expected| expected == *outer),
            KotlinExpr::This => self.current_type.as_ref().is_some_and(|current| {
                current == expected
                    || self
                        .generic_type_projection
                        .as_deref()
                        .is_some_and(|projection| projection.is_subtype(current, expected))
            }),
            _ => false,
        }
    }
}

enum KotlinPredicateTask<'a> {
    Visit(&'a SemanticPredicate),
    Not,
    Junction { count: usize, conjunction: bool },
}

impl KotlinDialect for DexKotlinDialect {
    type Error = KotlinLoweringError;

    fn condition(&mut self, condition: &SemanticPredicate) -> Result<KotlinExpr, Self::Error> {
        self.predicate(condition)
    }

    fn negated_condition(
        &mut self,
        condition: &SemanticPredicate,
    ) -> Result<KotlinExpr, Self::Error> {
        self.predicate(&condition.clone().negate())
    }

    fn expression(&mut self, value: &SemanticExpression) -> Result<KotlinExpr, Self::Error> {
        self.arg(value)
    }

    fn iterable_expression(
        &mut self,
        element_type: &KotlinType,
        value: &SemanticExpression,
    ) -> Result<KotlinExpr, Self::Error> {
        if matches!(value.declared_type(), Some(ArgType::Array(_))) {
            return self.arg(value);
        }
        let erased_type = ArgType::object("java/lang/Iterable");
        let erased_source = self.source_type(&erased_type)?;
        let KotlinType::Class(mut iterable) = erased_source.clone() else {
            unreachable!("a source class always lowers to a class type");
        };
        let Some(segment) = iterable.segments.last_mut() else {
            return self.arg(value);
        };
        segment.arguments = vec![KotlinTypeArgument::Exact(element_type.clone())];
        let expected = KotlinType::Class(iterable);
        let expression = self.arg_as_source_target(value, &erased_type, &expected)?;
        if self.accepts_target_type(value, &expected) {
            Ok(expression)
        } else {
            let actual = self.cast_source_type(value);
            Ok(self.source_cast(
                expression,
                value,
                actual.as_ref(),
                &expected,
                &erased_source,
            ))
        }
    }

    fn return_expression(
        &mut self,
        value: &SemanticExpression,
        condition: Option<&SemanticPredicate>,
    ) -> Result<KotlinExpr, Self::Error> {
        let _ = condition;
        if let (Some(expected), Some(source)) =
            (self.return_type.clone(), self.source_return_type.clone())
        {
            return self.arg_as_source_target(value, &expected, &source);
        } else if let Some(expected) = self.return_type.clone() {
            return self.arg_as(value, &expected);
        } else {
            self.arg(value)
        }
    }

    fn throw_expression(&mut self, value: &SemanticExpression) -> Result<KotlinExpr, Self::Error> {
        let expression = self.arg_as(value, &ArgType::object("java/lang/Throwable"))?;
        let Some(erased) = value.declared_type() else {
            return Ok(expression);
        };
        let source = self.source_expression_type(value);
        let source_erasure = source
            .as_ref()
            .and_then(|source| self.source_erasure(source));
        let unknown_reference = matches!(
            erased,
            ArgType::Unknown(types)
                if types
                    .iter()
                    .all(|ty| matches!(ty, PrimitiveType::Object | PrimitiveType::Array))
        );
        let mut candidates = self
            .generic_throw_types
            .iter()
            .filter(|candidate| {
                &candidate.erased == erased
                    || source_erasure.as_ref() == Some(&candidate.erased)
                    || unknown_reference
            })
            .filter(|candidate| source.as_ref() != Some(&candidate.source));
        let Some(candidate) = candidates.next() else {
            return Ok(expression);
        };
        if candidates.next().is_some()
            || matches!(&expression, KotlinExpr::Cast { ty, .. } if ty == &candidate.source)
        {
            return Ok(expression);
        }
        Ok(KotlinExpr::Cast {
            ty: candidate.source.clone(),
            value: Box::new(expression),
        })
    }

    fn loop_variable(
        &mut self,
        register: &RegisterArg,
    ) -> Result<(KotlinType, KotlinIdentifier), Self::Error> {
        let name = self.register_name(register)?;
        self.declared.insert(name.clone());
        self.locals.remove(&name);
        let binding_type = if register.ty.is_known() {
            &register.ty
        } else {
            self.types.register_type(register)?
        };
        let ty = self
            .source_register_type(register)
            .cloned()
            .map(Ok)
            .unwrap_or_else(|| self.source_type(binding_type))?;
        self.binding_types.bind_name(name.clone(), ty.clone());
        Ok((ty, name))
    }

    fn synthetic_variable(&mut self, hint: &str) -> KotlinIdentifier {
        self.name_scope.claim(KotlinIdentifier::from_dex(hint))
    }

    fn statement(&mut self, statement: &SemanticStatement) -> Result<KotlinStmt, Self::Error> {
        if let SemanticStatementKind::Definition { result, value, .. } = &statement.kind {
            let expected = self.types.register_type(result)?.clone();
            let value = self.definition_value(result, value, &expected)?;
            return self.assignment(result, value);
        }
        let SemanticStatementKind::Instruction(insn) = &statement.kind else {
            unreachable!("semantic definition was handled above")
        };
        let lowered = if let Some(result) = &insn.result {
            let expected = self.types.register_type(result)?.clone();
            let value = self.definition_value(
                result,
                &SemanticExpression::Operation(Box::new(insn.clone())),
                &expected,
            )?;
            self.assignment(result, value)?
        } else {
            match insn.insn_type {

            InsnType::Invoke | InsnType::Constructor => {
                if insn.insn_type == InsnType::Invoke
                    && insn
                        .payload
                        .reference
                        .as_ref()
                        .is_some_and(|reference| {
                            matches!(reference, MemberReference::Method(method) if method.is_constructor())
                        })
                {
                    self.constructor_invocation(insn)?
                } else {
                    KotlinStmt::Expression(
                        self.insn_expr(insn, None, None)?,
                    )
                }
            }
            InsnType::FilledNewArray => {
                KotlinStmt::Expression(self.insn_expr(insn, None, None)?)
            }
            InsnType::Iput => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                let value = insn
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                let owner = insn
                    .operands()
                    .get(1)
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                if self.outer_instance(field, owner).is_some_and(|binding| {
                    value
                        .as_register()
                        .and_then(|register| register.code_var)
                        == binding.constructor_parameter
                        && binding.constructor_parameter.is_some()
                }) {
                    return Ok(KotlinStmt::Empty);
                }
                KotlinStmt::Assign {
                    target: KotlinExpr::Field {
                        owner: Box::new(self.arg(owner)?),
                        name: self.member_names.field(field),
                    },
                    op: KotlinAssignOp::Assign,
                    value: self.arg_as_field(value, field, Some(owner))?,
                }
            }
            InsnType::Sput => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                KotlinStmt::Assign {
                    target: KotlinExpr::StaticField {
                        owner: self.static_owner_type(&field.owner)?,
                        name: self.member_names.field(field),
                    },
                    op: KotlinAssignOp::Assign,
                    value: self.arg_as_field(
                        insn.operands()
                            .first()
                            .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                        field,
                        None,
                    )?,
                }
            }
            InsnType::Aput => {
                let array_arg = insn
                    .operands()
                    .get(1)
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                let array_type = self.ssa_expression_type(array_arg)?.clone();
                let element = array_type
                    .as_array_element()
                    .ok_or_else(|| KotlinLoweringError::InvalidArrayType {
                        instruction: insn.insn_type,
                        offset: insn.offset,
                        ty: array_type.clone(),
                    })?
                    .clone();
                let source_element = self.source_expression_type(array_arg).and_then(|ty| match ty {
                    KotlinType::Array(element) => Some(element.into_type()),
                    KotlinType::Primitive(_) | KotlinType::Class(_) | KotlinType::Variable(_) => None,
                });
                let value = insn
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                KotlinStmt::Assign {
                    target: KotlinExpr::ArrayAccess {
                        array: Box::new(self.arg(array_arg)?),
                        index: Box::new(
                            self.arg(
                                insn.operands().get(2).ok_or(
                                    KotlinLoweringError::MissingArgument(insn.insn_type),
                                )?,
                            )?,
                        ),
                    },
                    op: KotlinAssignOp::Assign,
                    value: match source_element.as_ref() {
                        Some(source) => self.arg_as_source_target(value, &element, source)?,
                        None => self.arg_as(value, &element)?,
                    },
                }
            }
            InsnType::CompoundAssign => KotlinStmt::Assign {
                target: self.arg(
                    insn.compound_target()
                        .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                )?,
                op: Self::assignment_operator(
                    insn.payload
                        .arith_op
                        .ok_or(KotlinLoweringError::MissingPayload {
                            instruction: insn.insn_type,
                            field: "arith_op",
                        })?,
                )?,
                value: self.arg(
                    insn.operands()
                        .last()
                        .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?,
                )?,
            },
            InsnType::FillArray => self.fill_array(insn)?,
            InsnType::CheckCast => {
                let value = insn
                    .operands()
                    .first()
                    .ok_or(KotlinLoweringError::MissingArgument(insn.insn_type))?;
                let target = self.arg(value)?;
                KotlinStmt::Assign {
                    target: target.clone(),
                    op: KotlinAssignOp::Assign,
                    value: KotlinExpr::Cast {
                        ty: self.source_type(
                            insn.conversion_type()
                                .ok_or(KotlinLoweringError::MissingPayload {
                                    instruction: insn.insn_type,
                                    field: "conversion_type",
                                })?,
                        )?,
                        value: Box::new(target),
                    },
                }
            }
            InsnType::Nop => Err(KotlinLoweringError::UnsupportedStatement(InsnType::Nop))?,
            InsnType::Phi => Err(KotlinLoweringError::UnrecoveredPhi(insn.offset))?,
            InsnType::MoveResult => {
                Err(KotlinLoweringError::UnrecoveredMoveResult(insn.offset))?
            }
            InsnType::MoveException => {
                Err(KotlinLoweringError::UnrecoveredExceptionValue(insn.offset))?
            }
            InsnType::MonitorEnter | InsnType::MonitorExit => {
                Err(KotlinLoweringError::UnrecoveredMonitor(insn.offset))?
            }
            _ => Err(KotlinLoweringError::UnsupportedStatement(insn.insn_type))?,
            }
        };
        Ok(lowered)
    }

    fn catch_binding(
        &mut self,
        register: Option<&RegisterArg>,
    ) -> Result<KotlinCatchBinding, Self::Error> {
        let Some(register) = register else {
            return Ok(KotlinCatchBinding::local(
                self.name_scope.claim(KotlinIdentifier::from_dex("e")),
            ));
        };
        let variable = SourceVariable::of(register)?;
        let name = self.register_name(register)?;
        if self.catch_storage.contains(&variable) {
            let parameter = self.name_scope.claim(KotlinIdentifier::from_dex("e"));
            return Ok(KotlinCatchBinding::stored(parameter, name));
        }
        self.declared.insert(name.clone());
        self.locals.remove(&name);
        Ok(KotlinCatchBinding::local(name))
    }

    fn type_name(&mut self, ty: &ArgType) -> Result<KotlinType, Self::Error> {
        self.source_type(ty)
    }

    fn take_declarations(&mut self) -> Vec<KotlinStmt> {
        std::mem::take(&mut self.locals)
            .into_iter()
            .map(|(name, ty)| KotlinStmt::Variable {
                binding: Default::default(),
                ty,
                name,
                value: None,
            })
            .collect()
    }

    fn prepare(&mut self, root: &crate::ir::SemanticNode) -> Result<(), Self::Error> {
        crate::profile_scope!("kotlin_prepare.verify", KotlinInputVerifier::verify(root))?;
        let diagnostics_enabled = self
            .observer
            .is_enabled(crate::ir::AnalysisEventKind::SourceTypes);
        let source_types = crate::profile_scope!("kotlin_prepare.source_types", {
            SourceTypeFlow::solve(
                root,
                &self.source_field_types,
                &self.generic_fields,
                &self.source_object_types,
                &self.generic_methods,
                self.generic_type_projection.as_deref(),
                &self.source_types,
                &self.source_type_erasures,
                &self.source_type_bounds,
                self.source_return_type.as_ref(),
                self.current_type.as_ref(),
                self.source_current_type.as_ref(),
                self.this_code_var,
                &self.source_variable_types,
                diagnostics_enabled,
            )
        });
        if diagnostics_enabled {
            let diagnostics = source_types.diagnostics();
            self.observer
                .observe(crate::ir::AnalysisEvent::SourceTypes(&diagnostics));
        }
        (
            self.source_variable_definition_types,
            self.source_value_definition_types,
            self.source_variable_types,
            self.source_value_types,
            self.source_variable_requirements,
            self.source_value_requirements,
        ) = source_types.into_parts();
        let declarations = crate::profile_scope!("kotlin_prepare.declarations", {
            DeclarationAnalysis::default().analyze(root)
        })?;
        self.inline_declarations = declarations.inline_variables().clone();
        let mut bindings = SourceBindings::default();
        bindings.visit_node(root);
        for (kind, register) in bindings.registers {
            let name = self.register_name(&register)?;
            let variable = SourceVariable::of(&register)?;
            if kind == SemanticBindingKind::Catch && declarations.catch_requires_storage(variable) {
                let inferred_type = self.types.register_type(&register)?.clone();
                let ty = self
                    .source_definition_type(&register)
                    .map(Ok)
                    .unwrap_or_else(|| self.source_type(&inferred_type))?;
                let ty = self.kotlin_source_type(&inferred_type, ty);
                self.locals.entry(name).or_insert(ty);
                self.catch_storage.insert(variable);
            } else {
                self.declared.insert(name.clone());
                self.locals.remove(&name);
            }
        }
        Ok(())
    }
}

#[derive(Default)]
struct SourceBindings {
    registers: Vec<(SemanticBindingKind, RegisterArg)>,
}

impl SemanticVisitor for SourceBindings {
    fn visit_binding(&mut self, kind: SemanticBindingKind, register: &RegisterArg) {
        self.registers.push((kind, register.clone()));
    }
}

#[derive(Debug, Clone)]
pub enum KotlinLoweringError {
    Structure(KotlinStructuralError),
    MissingSourceVariable(u32),
    MissingThisSourceVariable,
    MissingParameterSourceVariable(usize),
    ParameterBindingArity {
        variables: usize,
        names: usize,
    },
    MissingArgument(InsnType),
    MissingPayload {
        instruction: InsnType,
        field: &'static str,
    },
    MissingReference {
        caller: &'static std::panic::Location<'static>,
    },
    InvalidReferenceKind,
    MissingCondition,
    UnexpectedCondition(InsnType),
    MalformedPredicate,
    MissingArrayData,
    InvalidArrayElementWidth(u16),
    InvalidArrayType {
        instruction: InsnType,
        offset: u32,
        ty: ArgType,
    },
    InvalidComparisonType(ArgType),
    InvalidAssignmentOperator(ArithOp),
    InvalidIntegerLiteral(i64),
    InvalidCharLiteral(i64),
    InvalidConstructorReceiver,
    InvalidThisLvalue,
    UnrecoveredObjectInitialization(u32),
    UnrecoveredPhi(u32),
    UnrecoveredMoveResult(u32),
    UnrecoveredExceptionValue(u32),
    UnsupportedExpression(InsnType),
    UnsupportedStatement(InsnType),
    UnrecoveredMonitor(u32),
    UnresolvedOperationType {
        instruction: InsnType,
        offset: u32,
        domain: &'static str,
    },
    UnresolvedSourceType {
        ty: ArgType,
        caller: &'static std::panic::Location<'static>,
    },
    MissingSourceType(ArgType),
    Type(TypeConstraintError),
}

impl From<KotlinStructuralError> for KotlinLoweringError {
    fn from(source: KotlinStructuralError) -> Self {
        Self::Structure(source)
    }
}

impl From<DeclarationError> for KotlinLoweringError {
    fn from(source: DeclarationError) -> Self {
        match source {
            DeclarationError::MissingSourceVariable(register) => {
                Self::MissingSourceVariable(register)
            }
            DeclarationError::MalformedConstructor(offset) => {
                Self::UnrecoveredObjectInitialization(offset)
            }
        }
    }
}

impl From<TypeConstraintError> for KotlinLoweringError {
    fn from(source: TypeConstraintError) -> Self {
        Self::Type(source)
    }
}

impl fmt::Display for KotlinLoweringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Structure(source) => write!(f, "Kotlin structure is invalid: {source}"),
            Self::MissingSourceVariable(register) => {
                write!(f, "register v{register} has no assigned source variable")
            }
            Self::MissingThisSourceVariable => {
                f.write_str("instance method has no assigned `this` variable")
            }
            Self::MissingParameterSourceVariable(parameter) => {
                write!(f, "parameter {parameter} has no assigned source variable")
            }
            Self::ParameterBindingArity { variables, names } => write!(
                f,
                "method has {variables} parameter variables but {names} source names"
            ),
            Self::MissingArgument(instruction) => {
                write!(f, "{instruction:?} is missing an operand")
            }
            Self::MissingPayload { instruction, field } => {
                write!(f, "{instruction:?} is missing {field}")
            }
            Self::MissingReference { caller } => {
                write!(f, "required Kotlin reference is missing at {caller}")
            }
            Self::InvalidReferenceKind => {
                f.write_str("instruction has the wrong member-reference kind")
            }
            Self::MissingCondition => f.write_str("conditional value has no predicate"),
            Self::UnexpectedCondition(instruction) => {
                write!(f, "{instruction:?} carries a conditional-value predicate")
            }
            Self::MalformedPredicate => f.write_str("Kotlin predicate tree is malformed"),
            Self::MissingArrayData => f.write_str("fill-array instruction has no array data"),
            Self::InvalidArrayElementWidth(width) => {
                write!(f, "fill-array uses unsupported element width {width}")
            }
            Self::InvalidArrayType {
                instruction,
                offset,
                ty,
            } => write!(
                f,
                "{instruction:?} at DEX offset {offset} requires an array, found {ty}"
            ),
            Self::InvalidComparisonType(ty) => {
                write!(f, "comparison result has unsupported type {ty}")
            }
            Self::InvalidAssignmentOperator(operator) => {
                write!(f, "{operator:?} has no Kotlin compound-assignment form")
            }
            Self::InvalidIntegerLiteral(value) => {
                write!(f, "{value} is outside the Kotlin int literal range")
            }
            Self::InvalidCharLiteral(value) => {
                write!(f, "{value} is not a valid Kotlin char literal")
            }
            Self::InvalidConstructorReceiver => {
                f.write_str("constructor invocation has no receiver")
            }
            Self::InvalidThisLvalue => f.write_str("`this` cannot be used as a Kotlin lvalue"),
            Self::UnrecoveredObjectInitialization(offset) => {
                write!(f, "object initialization at {offset:#x} was not recovered")
            }
            Self::UnrecoveredPhi(offset) => {
                write!(f, "SSA phi at {offset:#x} reached Kotlin lowering")
            }
            Self::UnrecoveredMoveResult(offset) => {
                write!(f, "move-result at {offset:#x} reached Kotlin lowering")
            }
            Self::UnrecoveredExceptionValue(offset) => {
                write!(f, "move-exception at {offset:#x} reached Kotlin lowering")
            }
            Self::UnsupportedExpression(instruction) => {
                write!(f, "{instruction:?} has no Kotlin expression form")
            }
            Self::UnsupportedStatement(instruction) => {
                write!(f, "{instruction:?} has no Kotlin statement form")
            }
            Self::UnrecoveredMonitor(offset) => {
                write!(f, "monitor operation at {offset:#x} was not regionized")
            }
            Self::UnresolvedOperationType {
                instruction,
                offset,
                domain,
            } => write!(
                f,
                "{instruction:?} at DEX offset {offset:#x} has no {domain} expression type"
            ),
            Self::UnresolvedSourceType { ty, caller } => write!(
                f,
                "Kotlin source type is unresolved: {ty} (requested at {}:{})",
                caller.file(),
                caller.line()
            ),
            Self::MissingSourceType(ty) => {
                write!(f, "Kotlin source naming cannot represent {ty}")
            }
            Self::Type(source) => write!(f, "type recovery failed: {source}"),
        }
    }
}

impl std::error::Error for KotlinLoweringError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Structure(source) => Some(source),
            Self::Type(source) => Some(source),
            _ => None,
        }
    }
}

enum LocalAssignment {
    Assignment {
        operator: KotlinAssignOp,
        value: KotlinExpr,
    },
    Update(super::KotlinUpdateOp),
}

impl LocalAssignment {
    fn recover(target: &KotlinIdentifier, value: KotlinExpr) -> Self {
        let KotlinExpr::Binary { left, op, right } = value else {
            return Self::plain(value);
        };
        if left.as_ref() != &KotlinExpr::Name(target.clone()) {
            return Self::plain(KotlinExpr::Binary { left, op, right });
        }
        let Some(operator) = Self::compound_operator(op) else {
            return Self::plain(KotlinExpr::Binary { left, op, right });
        };
        let value = *right;
        if Self::is_one(&value) {
            if operator == KotlinAssignOp::Add {
                return Self::Update(super::KotlinUpdateOp::Increment);
            }
            if operator == KotlinAssignOp::Subtract {
                return Self::Update(super::KotlinUpdateOp::Decrement);
            }
        }
        Self::Assignment { operator, value }
    }

    fn plain(value: KotlinExpr) -> Self {
        Self::Assignment {
            operator: KotlinAssignOp::Assign,
            value,
        }
    }

    fn into_statement(self, name: KotlinIdentifier) -> KotlinStmt {
        let target = KotlinExpr::Name(name);
        match self {
            Self::Assignment { operator, value } => KotlinStmt::Assign {
                target,
                op: operator,
                value,
            },
            Self::Update(op) => KotlinStmt::Expression(KotlinExpr::Update {
                op,
                target: Box::new(target),
                prefix: false,
            }),
        }
    }

    fn is_one(value: &KotlinExpr) -> bool {
        matches!(
            value,
            KotlinExpr::Literal(KotlinLiteral::Integer(1) | KotlinLiteral::Long(1))
        )
    }

    fn compound_operator(operator: KotlinBinaryOp) -> Option<KotlinAssignOp> {
        Some(match operator {
            KotlinBinaryOp::Add => KotlinAssignOp::Add,
            KotlinBinaryOp::Subtract => KotlinAssignOp::Subtract,
            KotlinBinaryOp::Multiply => KotlinAssignOp::Multiply,
            KotlinBinaryOp::Divide => KotlinAssignOp::Divide,
            KotlinBinaryOp::Remainder => KotlinAssignOp::Remainder,
            KotlinBinaryOp::BitAnd => KotlinAssignOp::BitAnd,
            KotlinBinaryOp::BitOr => KotlinAssignOp::BitOr,
            KotlinBinaryOp::BitXor => KotlinAssignOp::BitXor,
            KotlinBinaryOp::ShiftLeft => KotlinAssignOp::ShiftLeft,
            KotlinBinaryOp::ShiftRight => KotlinAssignOp::ShiftRight,
            KotlinBinaryOp::UnsignedShiftRight => KotlinAssignOp::UnsignedShiftRight,
            KotlinBinaryOp::LogicalAnd
            | KotlinBinaryOp::LogicalOr
            | KotlinBinaryOp::Equal
            | KotlinBinaryOp::NotEqual
            | KotlinBinaryOp::ReferentialEqual
            | KotlinBinaryOp::ReferentialNotEqual
            | KotlinBinaryOp::Less
            | KotlinBinaryOp::GreaterEqual
            | KotlinBinaryOp::Greater
            | KotlinBinaryOp::LessEqual => return None,
        })
    }
}

struct KotlinArithmetic;

impl KotlinArithmetic {
    fn binary(left: KotlinExpr, operator: KotlinBinaryOp, right: KotlinExpr) -> KotlinExpr {
        let (operator, right) = Self::normalize_sign(operator, right);
        KotlinExpr::Binary {
            left: Box::new(left),
            op: operator,
            right: Box::new(right),
        }
    }

    fn normalize_sign(operator: KotlinBinaryOp, right: KotlinExpr) -> (KotlinBinaryOp, KotlinExpr) {
        let Some(positive) = Self::positive_integer(&right) else {
            return (operator, right);
        };
        match operator {
            KotlinBinaryOp::Add => (KotlinBinaryOp::Subtract, positive),
            KotlinBinaryOp::Subtract => (KotlinBinaryOp::Add, positive),
            _ => (operator, right),
        }
    }

    fn positive_integer(value: &KotlinExpr) -> Option<KotlinExpr> {
        let literal = match value {
            KotlinExpr::Literal(KotlinLiteral::Integer(value)) if *value < 0 => {
                KotlinLiteral::Integer(value.checked_neg()?)
            }
            KotlinExpr::Literal(KotlinLiteral::Long(value)) if *value < 0 => {
                KotlinLiteral::Long(value.checked_neg()?)
            }
            _ => return None,
        };
        Some(KotlinExpr::Literal(literal))
    }
}

impl DexKotlinDialect {
    #[track_caller]
    fn missing_reference() -> KotlinLoweringError {
        KotlinLoweringError::MissingReference {
            caller: std::panic::Location::caller(),
        }
    }

    fn field(reference: Option<&MemberReference>) -> Result<&FieldReference, KotlinLoweringError> {
        let reference = reference.ok_or_else(|| Self::missing_reference())?;
        let MemberReference::Field(reference) = reference else {
            return Err(KotlinLoweringError::InvalidReferenceKind);
        };
        Ok(reference)
    }

    fn method(
        reference: Option<&MemberReference>,
    ) -> Result<&MethodReference, KotlinLoweringError> {
        let reference = reference.ok_or_else(|| Self::missing_reference())?;
        let MemberReference::Method(reference) = reference else {
            return Err(KotlinLoweringError::InvalidReferenceKind);
        };
        Ok(reference)
    }

    #[track_caller]
    fn source_type(&self, ty: &ArgType) -> Result<KotlinType, KotlinLoweringError> {
        if let Some(source_type) = self.source_types.get(ty) {
            return Ok(self.kotlin_source_type(ty, source_type.clone()));
        }
        if let Some(source_type) = self
            .generic_type_projection
            .as_deref()
            .and_then(|projection| projection.resolve_type(ty))
        {
            return Ok(self.kotlin_source_type(ty, source_type));
        }
        Ok(match ty {
            ArgType::Primitive(primitive) => KotlinType::Primitive(match primitive {
                PrimitiveType::Void => KotlinPrimitiveType::Void,
                PrimitiveType::Boolean => KotlinPrimitiveType::Boolean,
                PrimitiveType::Byte => KotlinPrimitiveType::Byte,
                PrimitiveType::Short => KotlinPrimitiveType::Short,
                PrimitiveType::Char => KotlinPrimitiveType::Char,
                PrimitiveType::Int => KotlinPrimitiveType::Int,
                PrimitiveType::Long => KotlinPrimitiveType::Long,
                PrimitiveType::Float => KotlinPrimitiveType::Float,
                PrimitiveType::Double => KotlinPrimitiveType::Double,
                PrimitiveType::Object | PrimitiveType::Array => {
                    return Err(KotlinLoweringError::UnresolvedSourceType {
                        ty: ty.clone(),
                        caller: std::panic::Location::caller(),
                    });
                }
            }),
            ArgType::Object(_) => return Err(KotlinLoweringError::MissingSourceType(ty.clone())),
            ArgType::Array(element) => KotlinType::array(self.source_type(element)?),
            ArgType::Unknown(_) => {
                return Err(KotlinLoweringError::UnresolvedSourceType {
                    ty: ty.clone(),
                    caller: std::panic::Location::caller(),
                });
            }
        })
    }

    fn static_owner_type(&self, ty: &ArgType) -> Result<KotlinType, KotlinLoweringError> {
        if let Some(owner) = ty.as_object().and_then(KotlinJvmBuiltins::static_namespace) {
            return Ok(owner);
        }
        self.source_type(ty)
    }

    fn kotlin_source_type(&self, erased: &ArgType, mut source: KotlinType) -> KotlinType {
        let Some(parameters) = self
            .generic_type_projection
            .as_deref()
            .and_then(|projection| projection.declared_type_parameters(erased))
            .filter(|parameters| !parameters.is_empty())
        else {
            return source;
        };
        let KotlinType::Class(class) = &mut source else {
            return source;
        };
        let Some(segment) = class.segments.last_mut() else {
            return source;
        };
        if segment.arguments.is_empty() {
            segment.arguments = vec![KotlinTypeArgument::Any; parameters.len()];
        }
        source
    }

    fn binary_operator(operator: ArithOp) -> (KotlinBinaryOp, bool) {
        match operator {
            ArithOp::Add => (KotlinBinaryOp::Add, false),
            ArithOp::Sub => (KotlinBinaryOp::Subtract, false),
            ArithOp::Rsub => (KotlinBinaryOp::Subtract, true),
            ArithOp::Mul => (KotlinBinaryOp::Multiply, false),
            ArithOp::Div => (KotlinBinaryOp::Divide, false),
            ArithOp::Rem => (KotlinBinaryOp::Remainder, false),
            ArithOp::And => (KotlinBinaryOp::BitAnd, false),
            ArithOp::Or => (KotlinBinaryOp::BitOr, false),
            ArithOp::Xor => (KotlinBinaryOp::BitXor, false),
            ArithOp::Shl => (KotlinBinaryOp::ShiftLeft, false),
            ArithOp::Shr => (KotlinBinaryOp::ShiftRight, false),
            ArithOp::Ushr => (KotlinBinaryOp::UnsignedShiftRight, false),
        }
    }

    fn assignment_operator(operator: ArithOp) -> Result<KotlinAssignOp, KotlinLoweringError> {
        Ok(match operator {
            ArithOp::Add => KotlinAssignOp::Add,
            ArithOp::Sub => KotlinAssignOp::Subtract,
            ArithOp::Rsub => return Err(KotlinLoweringError::InvalidAssignmentOperator(operator)),
            ArithOp::Mul => KotlinAssignOp::Multiply,
            ArithOp::Div => KotlinAssignOp::Divide,
            ArithOp::Rem => KotlinAssignOp::Remainder,
            ArithOp::And => KotlinAssignOp::BitAnd,
            ArithOp::Or => KotlinAssignOp::BitOr,
            ArithOp::Xor => KotlinAssignOp::BitXor,
            ArithOp::Shl => KotlinAssignOp::ShiftLeft,
            ArithOp::Shr => KotlinAssignOp::ShiftRight,
            ArithOp::Ushr => KotlinAssignOp::UnsignedShiftRight,
        })
    }

    fn comparison_operator(operator: IfOp) -> KotlinBinaryOp {
        match operator {
            IfOp::Eq => KotlinBinaryOp::Equal,
            IfOp::Ne => KotlinBinaryOp::NotEqual,
            IfOp::Lt => KotlinBinaryOp::Less,
            IfOp::Ge => KotlinBinaryOp::GreaterEqual,
            IfOp::Gt => KotlinBinaryOp::Greater,
            IfOp::Le => KotlinBinaryOp::LessEqual,
        }
    }

    fn referential_comparison_operator(operator: IfOp) -> KotlinBinaryOp {
        match operator {
            IfOp::Eq => KotlinBinaryOp::ReferentialEqual,
            IfOp::Ne => KotlinBinaryOp::ReferentialNotEqual,
            _ => Self::comparison_operator(operator),
        }
    }

    fn literal(literal: &crate::ir::LiteralArg) -> Result<KotlinLiteral, KotlinLoweringError> {
        Ok(match literal.ty.as_primitive() {
            Some(PrimitiveType::Boolean) => KotlinLiteral::Boolean(literal.value != 0),
            Some(PrimitiveType::Long) => KotlinLiteral::Long(literal.value),
            Some(PrimitiveType::Float) => {
                KotlinLiteral::Float(f32::from_bits(literal.value as u32))
            }
            Some(PrimitiveType::Double) => {
                KotlinLiteral::Double(f64::from_bits(literal.value as u64))
            }
            Some(PrimitiveType::Char) => {
                let value = u16::try_from(literal.value)
                    .map_err(|_| KotlinLoweringError::InvalidCharLiteral(literal.value))?;
                KotlinLiteral::Character(value)
            }
            _ if literal.value == 0
                && matches!(literal.ty, ArgType::Object(_) | ArgType::Array(_)) =>
            {
                KotlinLiteral::Null
            }
            _ => KotlinLiteral::Integer(
                i32::try_from(literal.value)
                    .map_err(|_| KotlinLoweringError::InvalidIntegerLiteral(literal.value))?,
            ),
        })
    }

    fn constant(arg: &SemanticExpression) -> Option<i64> {
        let mut current = arg;
        loop {
            match current {
                SemanticExpression::Literal(literal) => return Some(literal.value),
                SemanticExpression::Operation(insn)
                    if matches!(insn.insn_type, InsnType::Const | InsnType::Move) =>
                {
                    current = insn.operands().first()?;
                }
                SemanticExpression::Register(_)
                | SemanticExpression::Operation(_)
                | SemanticExpression::Select { .. } => return None,
            }
        }
    }
}
