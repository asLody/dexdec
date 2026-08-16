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
    JavaAssignOp, JavaBinaryOp, JavaConstructorTarget, JavaExpr, JavaIdentifier, JavaLiteral,
    JavaNameScope, JavaPrimitiveType, JavaStmt, JavaType, JavaTypeArgument, JavaUnaryOp,
};
use super::declarations::{DeclarationAnalysis, DeclarationError, SourceVariable};
use super::lower::{JavaCatchBinding, JavaDialect, JavaStructuralError};
use super::syntax::primitives::JavaPrimitiveSemantics;

mod input;

use super::members::JavaMemberNames;
use super::source_types::{
    invocation_expression_signature, GenericInvocationCompatibility, GenericTypeEvidence,
    GenericTypeProjection, GenericTypeRelation, GenericTypeSolver, JavaTypeRelations,
    SourceTypeFlow,
};
use input::JavaInputVerifier;

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
    target: &'a JavaType,
    erased: &'a JavaType,
    erased_bridge: bool,
}

impl<'a> GenericCast<'a> {
    fn new(target: &'a JavaType, erased: &'a JavaType) -> Self {
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

    fn is_parameterized(ty: &JavaType) -> bool {
        match ty {
            JavaType::Class(class) => class
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_empty()),
            JavaType::Array(element) => Self::is_parameterized(element),
            JavaType::Primitive(_) | JavaType::Variable(_) => false,
        }
    }

    fn has_generic_evidence(ty: &JavaType) -> bool {
        match ty {
            JavaType::Variable(_) => true,
            JavaType::Array(element) => Self::has_generic_evidence(element),
            JavaType::Class(class) => class
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_empty()),
            JavaType::Primitive(_) => false,
        }
    }

    fn has_wildcard(ty: &JavaType) -> bool {
        match ty {
            JavaType::Array(element) => Self::has_wildcard(element),
            JavaType::Class(class) => class.segments.iter().any(|segment| {
                segment.arguments.iter().any(|argument| match argument {
                    JavaTypeArgument::Any
                    | JavaTypeArgument::Extends(_)
                    | JavaTypeArgument::Super(_) => true,
                    JavaTypeArgument::Exact(ty) => Self::has_wildcard(ty),
                })
            }),
            JavaType::Primitive(_) | JavaType::Variable(_) => false,
        }
    }

    fn lower(self, expression: JavaExpr) -> JavaExpr {
        let value = if self.erased_bridge
            && !matches!(&expression, JavaExpr::Cast { ty, .. } if ty == self.erased)
        {
            JavaExpr::Cast {
                ty: self.erased.clone(),
                value: Box::new(expression),
            }
        } else {
            expression
        };
        if matches!(&value, JavaExpr::Cast { ty, .. } if ty == self.target) {
            value
        } else {
            JavaExpr::Cast {
                ty: self.target.clone(),
                value: Box::new(value),
            }
        }
    }
}

#[derive(Clone)]
pub struct DexJavaDialect {
    names: BTreeMap<SourceVariable, JavaIdentifier>,
    source_names: BTreeMap<u32, JavaIdentifier>,
    binding_types: JavaBindingTypes,
    source_variable_definition_types: BTreeMap<u32, JavaType>,
    source_value_definition_types: BTreeMap<crate::ir::analysis::SsaVar, JavaType>,
    source_variable_types: BTreeMap<u32, JavaType>,
    source_value_types: BTreeMap<crate::ir::analysis::SsaVar, JavaType>,
    source_variable_requirements: BTreeMap<u32, JavaType>,
    source_value_requirements: BTreeMap<crate::ir::analysis::SsaVar, JavaType>,
    primitive_expression_types: RefCell<BTreeMap<InstructionId, Option<PrimitiveType>>>,
    source_field_types: Arc<BTreeMap<FieldReference, JavaType>>,
    generic_fields: Arc<BTreeMap<FieldReference, GenericFieldContract>>,
    source_object_types: Arc<BTreeMap<ArgType, JavaType>>,
    generic_methods: Arc<BTreeMap<MethodReference, GenericMethodContract>>,
    generic_type_projection: Option<Arc<dyn GenericTypeProjection>>,
    declared: BTreeSet<JavaIdentifier>,
    locals: BTreeMap<JavaIdentifier, JavaType>,
    current_type: Option<ArgType>,
    source_current_type: Option<JavaType>,
    source_super_type: Option<JavaType>,
    return_type: Option<ArgType>,
    source_return_type: Option<JavaType>,
    source_type_erasures: BTreeMap<JavaIdentifier, ArgType>,
    source_type_bounds: BTreeMap<JavaIdentifier, JavaType>,
    generic_throw_types: Vec<JavaSourceErasure>,
    this_code_var: Option<u32>,
    types: SourceTypeEnvironment,
    source_types: BTreeMap<ArgType, JavaType>,
    inline_declarations: BTreeSet<SourceVariable>,
    catch_storage: BTreeSet<SourceVariable>,
    name_scope: JavaNameScope,
    member_names: Arc<JavaMemberNames>,
    outer_instance: Option<OuterInstanceBinding>,
    outer_instance_fields: BTreeMap<FieldReference, JavaType>,
    observer: Arc<dyn crate::ir::AnalysisObserver>,
}

#[derive(Debug, Clone, Default)]
struct JavaBindingTypes {
    variables: BTreeMap<u32, JavaType>,
    names: BTreeMap<JavaIdentifier, JavaType>,
}

impl JavaBindingTypes {
    fn bind_variable(&mut self, variable: u32, name: Option<&JavaIdentifier>, ty: JavaType) {
        self.variables.insert(variable, ty.clone());
        if let Some(name) = name {
            self.names.insert(name.clone(), ty);
        }
    }

    fn bind_name(&mut self, name: JavaIdentifier, ty: JavaType) {
        self.names.insert(name, ty);
    }

    fn name_type(&self, name: &JavaIdentifier) -> Option<&JavaType> {
        self.names.get(name)
    }

    fn variable_type(&self, variable: u32) -> Option<&JavaType> {
        self.variables.get(&variable)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JavaSourceErasure {
    source: JavaType,
    erased: ArgType,
}

impl JavaSourceErasure {
    pub fn new(source: JavaType, erased: ArgType) -> Self {
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

fn is_register_style_name(name: &str) -> bool {
    name.strip_prefix('v').is_some_and(|digits| {
        !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
    })
}

impl DexJavaDialect {
    pub fn new(
        is_static: bool,
        this_code_var: Option<u32>,
        parameter_code_vars: &[Option<u32>],
        parameter_names: &[JavaIdentifier],
        types: &SourceTypeEnvironment,
        source_types: BTreeMap<ArgType, JavaType>,
        member_names: Arc<JavaMemberNames>,
    ) -> Result<Self, JavaLoweringError> {
        if parameter_code_vars.len() != parameter_names.len() {
            return Err(JavaLoweringError::ParameterBindingArity {
                variables: parameter_code_vars.len(),
                names: parameter_names.len(),
            });
        }
        let mut values = Self {
            names: BTreeMap::new(),
            source_names: BTreeMap::new(),
            binding_types: JavaBindingTypes::default(),
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
            name_scope: JavaNameScope::default(),
            member_names,
            outer_instance: None,
            outer_instance_fields: BTreeMap::new(),
            observer: Arc::new(crate::ir::NullAnalysisObserver),
        };
        if !is_static && this_code_var.is_none() {
            return Err(JavaLoweringError::MissingThisSourceVariable);
        }
        for (index, (code_var, name)) in parameter_code_vars.iter().zip(parameter_names).enumerate()
        {
            let code_var =
                (*code_var).ok_or(JavaLoweringError::MissingParameterSourceVariable(index))?;
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

    pub fn with_source_current_type(mut self, current_type: Option<JavaType>) -> Self {
        self.source_current_type = current_type;
        self
    }

    pub fn with_source_super_type(mut self, super_type: Option<JavaType>) -> Self {
        self.source_super_type = super_type;
        self
    }

    pub fn with_source_field_types(
        mut self,
        types: Arc<BTreeMap<FieldReference, JavaType>>,
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

    pub fn with_source_object_types(mut self, types: Arc<BTreeMap<ArgType, JavaType>>) -> Self {
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
        types: &[Option<JavaType>],
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

    pub fn with_source_return_type(mut self, return_type: Option<JavaType>) -> Self {
        self.source_return_type = return_type;
        self
    }

    pub fn with_source_type_erasures(
        mut self,
        erasures: BTreeMap<JavaIdentifier, ArgType>,
    ) -> Self {
        self.source_type_erasures = erasures;
        self
    }

    pub fn with_source_type_bounds(mut self, bounds: BTreeMap<JavaIdentifier, JavaType>) -> Self {
        self.source_type_bounds = bounds;
        self
    }

    pub fn with_generic_throw_types(mut self, types: Vec<JavaSourceErasure>) -> Self {
        self.generic_throw_types = types;
        self
    }

    pub fn with_outer_instance(mut self, outer_instance: Option<OuterInstanceBinding>) -> Self {
        self.outer_instance = outer_instance;
        self
    }

    pub fn with_outer_instance_fields(
        mut self,
        fields: BTreeMap<FieldReference, JavaType>,
    ) -> Self {
        self.outer_instance_fields = fields;
        self
    }

    pub fn with_reserved_local_names(
        mut self,
        names: impl IntoIterator<Item = JavaIdentifier>,
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

    pub fn with_semantic_names(mut self, names: BTreeMap<u32, JavaIdentifier>) -> Self {
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
    ) -> Result<JavaIdentifier, JavaLoweringError> {
        if register.code_var == self.this_code_var && self.this_code_var.is_some() {
            return Err(JavaLoweringError::InvalidThisLvalue);
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
        let name = self.name_scope.claim(self.fallback_local_name(register));
        self.names.insert(key, name.clone());
        Ok(name)
    }

    fn fallback_local_name(&self, register: &RegisterArg) -> JavaIdentifier {
        self.source_register_type(register)
            .and_then(Self::fallback_name_for_type)
            .unwrap_or_else(|| JavaIdentifier::from_hint("value"))
    }

    fn fallback_name_for_type(ty: &JavaType) -> Option<JavaIdentifier> {
        match ty {
            JavaType::Class(class) => {
                let name = &class.segments.last()?.name;
                let source = name.as_str();
                (source != "Object" && !is_register_style_name(source)).then(|| {
                    let mut characters = source.chars();
                    let Some(first) = characters.next() else {
                        return JavaIdentifier::from_hint("value");
                    };
                    let mut lowered = first.to_lowercase().collect::<String>();
                    lowered.extend(characters);
                    JavaIdentifier::from_hint(&lowered)
                })
            }
            JavaType::Array(_) => Some(JavaIdentifier::from_hint("values")),
            JavaType::Primitive(crate::language::java::JavaPrimitiveType::Boolean) => {
                Some(JavaIdentifier::from_hint("flag"))
            }
            _ => None,
        }
    }

    fn arg(&mut self, arg: &SemanticExpression) -> Result<JavaExpr, JavaLoweringError> {
        if matches!(arg, SemanticExpression::Select { .. })
            && self.expression_type(arg)? == &ArgType::BOOLEAN
        {
            return self.boolean_value(arg);
        }
        match arg {
            SemanticExpression::Register(register)
                if register.code_var == self.this_code_var && self.this_code_var.is_some() =>
            {
                Ok(JavaExpr::This)
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
                Ok(JavaExpr::QualifiedThis(self.source_type(&outer)?))
            }
            SemanticExpression::Register(register) => {
                Ok(JavaExpr::Name(self.register_name(register)?))
            }
            SemanticExpression::Literal(literal) => Ok(JavaExpr::Literal(Self::literal(literal)?)),
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
    ) -> Result<JavaExpr, JavaLoweringError> {
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
                        || self
                            .generic_type_projection
                            .as_deref()
                            .is_none_or(|projection| {
                                projection.subtype_relation(actual, expected)
                                    == crate::ir::analysis::SubtypeRelation::No
                            }))
            });
            if invocation_requires_conversion {
                let source = self.source_type(expected)?.into_raw();
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
    ) -> Result<JavaExpr, JavaLoweringError> {
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
        source: &JavaType,
    ) -> Result<JavaExpr, JavaLoweringError> {
        let actual = self.cast_source_type(value);
        let expression = self.arg_as_with_source_type(value, erased, source)?;
        if matches!(source, JavaType::Primitive(_)) {
            return Ok(expression);
        }
        let erased_type = self.source_type(erased)?.into_raw();
        let emitted_type = self.emitted_expression_type(&expression);
        let emitted_requires_parameterized_binding = GenericCast::is_parameterized(source)
            && emitted_type.as_ref().is_some_and(|emitted| {
                Self::same_erasure(emitted, source) && self.is_raw_generic_type(emitted)
            });
        // Conversion legality is determined by the Java expression's static type.
        // DEX-level source information is erased and is only a fallback when the
        // emitted expression cannot establish a type of its own.
        let conversion_type = emitted_type.as_ref().or(actual.as_ref());
        let accepts_target = !emitted_requires_parameterized_binding
            && (conversion_type.is_some_and(|actual| self.source_assignable_to(actual, source))
                || (emitted_type.is_none() && self.accepts_target_type(value, source)));
        let actual_is_incompatible = emitted_requires_parameterized_binding
            || conversion_type.is_some_and(|actual| !self.source_assignable_to(actual, source));
        if (!Self::source_return_requires_cast(source, &erased_type) && !actual_is_incompatible)
            || matches!(expression, JavaExpr::Literal(JavaLiteral::Null))
            || matches!(&expression, JavaExpr::Cast { ty, .. } if ty == source)
            || accepts_target
        {
            return Ok(expression);
        }
        Ok(self.source_cast(expression, value, actual.as_ref(), source, &erased_type))
    }

    fn emitted_expression_type(&self, expression: &JavaExpr) -> Option<JavaType> {
        match expression {
            JavaExpr::Name(name) => self.binding_types.name_type(name).cloned(),
            JavaExpr::Cast { ty, .. } => Some(ty.clone()),
            JavaExpr::New {
                ty, target_type, ..
            } => target_type
                .clone()
                .filter(|target| Self::same_erasure(target, ty))
                .or_else(|| Some(ty.clone())),
            JavaExpr::NewArray { element_type, .. } => Some(JavaType::array(element_type.clone())),
            JavaExpr::Conditional {
                when_true,
                when_false,
                ..
            } => self
                .emitted_expression_type(when_true)
                .zip(self.emitted_expression_type(when_false))
                .and_then(|(left, right)| {
                    (left == right)
                        .then_some(left.clone())
                        .or_else(|| self.type_relations().least_upper_bound(&left, &right))
                }),
            JavaExpr::Assignment { target, .. } => self.emitted_expression_type(target),
            _ => None,
        }
    }

    fn definition_value(
        &mut self,
        result: &RegisterArg,
        value: &SemanticExpression,
        erased: &ArgType,
    ) -> Result<JavaExpr, JavaLoweringError> {
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
    ) -> Result<JavaExpr, JavaLoweringError> {
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
        expected: &JavaType,
    ) -> Result<JavaExpr, JavaLoweringError> {
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
        expected: &JavaType,
    ) -> Result<JavaExpr, JavaLoweringError> {
        let when_true = self.select_branch_with_source_type(when_true, &erased, expected)?;
        let when_false = self.select_branch_with_source_type(when_false, &erased, expected)?;
        self.select_expression(condition, when_true, when_false)
    }

    fn select_branch_with_source_type(
        &mut self,
        branch: &SemanticExpression,
        erased: &ArgType,
        expected: &JavaType,
    ) -> Result<JavaExpr, JavaLoweringError> {
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
            && !matches!(&expression, JavaExpr::Cast { ty, .. } if ty == expected)
        {
            Ok(JavaExpr::Cast {
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
        mut when_true: JavaExpr,
        mut when_false: JavaExpr,
    ) -> Result<JavaExpr, JavaLoweringError> {
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
        Ok(JavaExpr::Conditional {
            condition: Box::new(positive),
            when_true: Box::new(when_true),
            when_false: Box::new(when_false),
        })
    }

    fn coerce(&self, expression: JavaExpr, expected: &ArgType) -> JavaExpr {
        match (expected, expression) {
            (
                ArgType::Primitive(PrimitiveType::Boolean),
                JavaExpr::Literal(JavaLiteral::Integer(value)),
            ) => JavaExpr::Literal(JavaLiteral::Boolean(value != 0)),
            (
                ArgType::Primitive(PrimitiveType::Long),
                JavaExpr::Literal(JavaLiteral::Integer(value)),
            ) => JavaExpr::Literal(JavaLiteral::Long(i64::from(value))),
            (
                ArgType::Primitive(PrimitiveType::Char),
                JavaExpr::Literal(JavaLiteral::Integer(value)),
            ) => JavaExpr::Literal(JavaLiteral::Character(value as u16)),
            (
                ArgType::Primitive(primitive @ (PrimitiveType::Byte | PrimitiveType::Short)),
                expression @ JavaExpr::Literal(JavaLiteral::Integer(_)),
            ) => JavaExpr::Cast {
                ty: JavaType::Primitive(match primitive {
                    PrimitiveType::Byte => JavaPrimitiveType::Byte,
                    PrimitiveType::Short => JavaPrimitiveType::Short,
                    _ => unreachable!(),
                }),
                value: Box::new(expression),
            },
            (
                ArgType::Primitive(PrimitiveType::Float),
                JavaExpr::Literal(JavaLiteral::Integer(value)),
            ) => JavaExpr::Literal(JavaLiteral::Float(f32::from_bits(value as u32))),
            (
                ArgType::Primitive(PrimitiveType::Double),
                JavaExpr::Literal(JavaLiteral::Long(value)),
            ) => JavaExpr::Literal(JavaLiteral::Double(f64::from_bits(value as u64))),
            (
                ArgType::Object(_) | ArgType::Array(_),
                JavaExpr::Literal(JavaLiteral::Integer(0)),
            ) => JavaExpr::Literal(JavaLiteral::Null),
            (
                expected,
                JavaExpr::Conditional {
                    condition,
                    when_true,
                    when_false,
                },
            ) => JavaExpr::Conditional {
                condition,
                when_true: Box::new(self.coerce(*when_true, expected)),
                when_false: Box::new(self.coerce(*when_false, expected)),
            },
            (_, expression) => expression,
        }
    }

    fn coerce_typed(
        &self,
        expression: JavaExpr,
        actual: Option<PrimitiveType>,
        expected: &ArgType,
    ) -> JavaExpr {
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
                let materialized = JavaExpr::Conditional {
                    condition: Box::new(self.coerce(expression, &ArgType::BOOLEAN)),
                    when_true: Box::new(Self::integral_literal(*primitive, 1)),
                    when_false: Box::new(Self::integral_literal(*primitive, 0)),
                };
                if matches!(
                    primitive,
                    PrimitiveType::Byte | PrimitiveType::Short | PrimitiveType::Char
                ) {
                    JavaExpr::Cast {
                        ty: JavaType::Primitive(Self::narrowing_primitive(*primitive)),
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
                JavaExpr::Literal(JavaLiteral::Integer(value)) => {
                    JavaExpr::Literal(JavaLiteral::Boolean(value != 0))
                }
                JavaExpr::Literal(JavaLiteral::Long(value)) => {
                    JavaExpr::Literal(JavaLiteral::Boolean(value != 0))
                }
                expression => JavaExpr::Binary {
                    left: Box::new(expression),
                    op: JavaBinaryOp::NotEqual,
                    right: Box::new(Self::integral_literal(actual, 0)),
                },
            },
            (Some(actual), ArgType::Primitive(expected))
                if Self::requires_narrowing_conversion(actual, *expected)
                    && !matches!(&expression, JavaExpr::Literal(_)) =>
            {
                JavaExpr::Cast {
                    ty: JavaType::Primitive(Self::narrowing_primitive(*expected)),
                    value: Box::new(expression),
                }
            }
            _ => self.coerce(expression, expected),
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

    fn narrowing_primitive(primitive: PrimitiveType) -> JavaPrimitiveType {
        match primitive {
            PrimitiveType::Byte => JavaPrimitiveType::Byte,
            PrimitiveType::Short => JavaPrimitiveType::Short,
            PrimitiveType::Char => JavaPrimitiveType::Char,
            _ => unreachable!("narrowing conversion only targets byte, short, or char"),
        }
    }

    fn integral_literal(primitive: PrimitiveType, value: i64) -> JavaExpr {
        match primitive {
            PrimitiveType::Long => JavaExpr::Literal(JavaLiteral::Long(value)),
            PrimitiveType::Byte
            | PrimitiveType::Short
            | PrimitiveType::Char
            | PrimitiveType::Int => JavaExpr::Literal(JavaLiteral::Integer(value as i32)),
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
                if let Some(primitive) = JavaPrimitiveSemantics::arithmetic_result(
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
            if let Some(JavaType::Primitive(primitive)) = operation
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
                JavaType::Primitive(primitive) => Some(Self::erased_primitive(*primitive)),
                JavaType::Class(_) | JavaType::Variable(_) | JavaType::Array(_) => None,
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
    ) -> Result<bool, JavaLoweringError> {
        if self.expression_type(left)?.is_reference() || self.expression_type(right)?.is_reference()
        {
            return Ok(false);
        }
        Ok([left, right].into_iter().any(|value| {
            Self::intrinsic_primitive_type(value)
                .is_some_and(|primitive| primitive != PrimitiveType::Boolean)
        }))
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

    fn erased_primitive(primitive: JavaPrimitiveType) -> PrimitiveType {
        match primitive {
            JavaPrimitiveType::Void => PrimitiveType::Void,
            JavaPrimitiveType::Boolean => PrimitiveType::Boolean,
            JavaPrimitiveType::Byte => PrimitiveType::Byte,
            JavaPrimitiveType::Short => PrimitiveType::Short,
            JavaPrimitiveType::Char => PrimitiveType::Char,
            JavaPrimitiveType::Int => PrimitiveType::Int,
            JavaPrimitiveType::Long => PrimitiveType::Long,
            JavaPrimitiveType::Float => PrimitiveType::Float,
            JavaPrimitiveType::Double => PrimitiveType::Double,
        }
    }

    fn source_return_requires_cast(source: &JavaType, erased: &JavaType) -> bool {
        source != erased && !matches!(source, JavaType::Primitive(_))
    }

    fn source_cast(
        &self,
        expression: JavaExpr,
        value: &SemanticExpression,
        actual: Option<&JavaType>,
        target: &JavaType,
        erased: &JavaType,
    ) -> JavaExpr {
        let existing_erased_bridge = matches!(&expression, JavaExpr::Cast { ty, .. }
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
            return JavaExpr::Cast {
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
    ) -> Result<JavaExpr, JavaLoweringError> {
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

    fn is_boolean_arg(&self, arg: &SemanticExpression) -> Result<bool, JavaLoweringError> {
        Ok(self.source_primitive_type(arg) == Some(PrimitiveType::Boolean))
    }

    fn is_reference_arg(&self, arg: &SemanticExpression) -> Result<bool, JavaLoweringError> {
        Ok(matches!(
            self.expression_type(arg)?,
            ArgType::Object(_) | ArgType::Array(_)
        ))
    }

    fn expression_type<'a>(
        &'a self,
        expression: &'a SemanticExpression,
    ) -> Result<&'a ArgType, JavaLoweringError> {
        match expression {
            SemanticExpression::Register(register) => Ok(self.types.register_type(register)?),
            SemanticExpression::Literal(literal) => Ok(&literal.ty),
            SemanticExpression::Operation(operation) => operation
                .result
                .as_ref()
                .map(|result| self.types.register_type(result))
                .transpose()?
                .or_else(|| Self::declared_expression_erasure(expression))
                .ok_or(JavaLoweringError::UnresolvedOperationType {
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
    ) -> Result<&'a ArgType, JavaLoweringError> {
        match expression {
            SemanticExpression::Register(register) => Ok(self.types.ssa_type(register)?),
            SemanticExpression::Literal(literal) => Ok(&literal.ty),
            SemanticExpression::Operation(operation) => operation
                .result
                .as_ref()
                .map(|result| self.types.ssa_type(result))
                .transpose()?
                .or_else(|| Self::declared_expression_erasure(expression))
                .ok_or(JavaLoweringError::UnresolvedOperationType {
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
        expected_source_type: Option<&JavaType>,
    ) -> Result<JavaExpr, JavaLoweringError> {
        match insn.insn_type {
            InsnType::Const => {
                let argument = insn
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                self.arg(argument)
            }
            InsnType::ConstStr => Ok(JavaExpr::Literal(JavaLiteral::String(
                insn.payload
                    .string_value
                    .as_ref()
                    .ok_or(JavaLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "string_value",
                    })?
                    .clone(),
            ))),
            InsnType::ConstClass => Ok(JavaExpr::ClassLiteral(
                self.source_type(insn.payload.class_type.as_ref().ok_or(
                    JavaLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "class_type",
                    },
                )?)?,
            )),
            InsnType::Move => self.arg(
                insn.operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
            ),
            InsnType::Phi => Err(JavaLoweringError::UnrecoveredPhi(insn.offset)),
            InsnType::MoveResult => Err(JavaLoweringError::UnrecoveredMoveResult(insn.offset)),
            InsnType::MoveException => {
                Err(JavaLoweringError::UnrecoveredExceptionValue(insn.offset))
            }
            InsnType::MonitorEnter | InsnType::MonitorExit => {
                Err(JavaLoweringError::UnrecoveredMonitor(insn.offset))
            }
            InsnType::Arith => {
                let operator = insn
                    .payload
                    .arith_op
                    .ok_or(JavaLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "arith_op",
                    })?;
                let result_type = if self.arithmetic_is_boolean(insn) {
                    ArgType::BOOLEAN
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
                        .ok_or(JavaLoweringError::UnresolvedOperationType {
                            instruction: insn.insn_type,
                            offset: insn.offset,
                            domain: "arithmetic",
                        })?
                };
                let mut left = self.arg_as(
                    insn.operands()
                        .first()
                        .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
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
                        .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                    &right_type,
                )?;
                let (operator, reverse) = Self::binary_operator(operator);
                if reverse {
                    std::mem::swap(&mut left, &mut right);
                }
                Ok(JavaArithmetic::binary(left, operator, right))
            }
            InsnType::StringConcat => {
                let mut args = insn.operands().iter();
                let first = args
                    .next()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                let mut expression = self.arg(first)?;
                for arg in args {
                    expression = JavaExpr::Binary {
                        left: Box::new(expression),
                        op: JavaBinaryOp::Add,
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
                Ok(JavaExpr::Unary {
                    op: if insn.insn_type == InsnType::Neg {
                        JavaUnaryOp::Negate
                    } else if boolean {
                        JavaUnaryOp::LogicalNot
                    } else {
                        JavaUnaryOp::BitwiseNot
                    },
                    operand: Box::new(
                        self.arg(
                            insn.operands()
                                .first()
                                .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                        )?,
                    ),
                })
            }
            InsnType::Cast | InsnType::CheckCast => {
                let target = insn
                    .conversion_type()
                    .ok_or(JavaLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "conversion_type",
                    })?;
                let operand = insn
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                if insn.insn_type == InsnType::CheckCast
                    && target.is_reference()
                    && Self::constant(operand) == Some(0)
                {
                    Ok(JavaExpr::Literal(JavaLiteral::Null))
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
                    Ok(JavaExpr::Cast {
                        ty: source_target.unwrap_or(self.source_type(target)?),
                        value: Box::new(value),
                    })
                }
            }
            InsnType::InstanceOf => Ok(JavaExpr::InstanceOf {
                value: Box::new(
                    self.arg(
                        insn.operands()
                            .first()
                            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
                ty: self.source_type(insn.payload.class_type.as_ref().ok_or(
                    JavaLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "class_type",
                    },
                )?)?,
            }),
            InsnType::ArrayLength => Ok(JavaExpr::Field {
                owner: Box::new(
                    self.arg(
                        insn.operands()
                            .first()
                            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
                name: JavaIdentifier::from_dex("length"),
            }),
            InsnType::Aget => Ok(JavaExpr::ArrayAccess {
                array: Box::new(
                    self.arg(
                        insn.operands()
                            .first()
                            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
                index: Box::new(
                    self.arg(
                        insn.operands()
                            .get(1)
                            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                    )?,
                ),
            }),
            InsnType::Iget => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                let owner = insn
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                let owner_expression = self.arg(owner)?;
                if self.outer_instance(field, owner).is_some()
                    || self.outer_instance_fields.contains_key(field)
                {
                    if self.is_implicit_enclosing_instance(&owner_expression, Some(&field.owner)) {
                        return Ok(JavaExpr::QualifiedThis(
                            self.source_type(&field.field_type)?,
                        ));
                    }
                }
                Ok(JavaExpr::Field {
                    owner: Box::new(owner_expression),
                    name: self.member_names.field(field),
                })
            }
            InsnType::Sget => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                Ok(JavaExpr::StaticField {
                    owner: self.source_type(&field.owner)?,
                    name: self.member_names.field(field),
                })
            }
            InsnType::Invoke => self.invoke(insn, None),
            InsnType::Constructor => {
                let method = Self::method(insn.payload.reference.as_ref())?;
                let allocation_owner = insn.allocation_type().unwrap_or(&method.owner);
                let analyzed_allocation_type = insn
                    .result
                    .as_ref()
                    .and_then(crate::ir::analysis::SsaVar::from_reg)
                    .and_then(|value| self.source_value_definition_types.get(&value))
                    .filter(|ty| self.source_erasure(ty).as_ref() == Some(allocation_owner))
                    .filter(|ty| !self.is_raw_generic_type(ty))
                    .cloned();
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
                        if let Some(allocation_type) = analyzed_allocation_type
                            .as_ref()
                            .or(contextual_allocation_type.as_ref())
                        {
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
                let needs_inferred_allocation = analyzed_allocation_type.is_some()
                    || contextual_allocation_type.is_some()
                    || insn
                        .operands()
                        .iter()
                        .skip(1)
                        .any(|argument| self.is_function_object_expression(argument));
                let inferred_allocation_type = analyzed_allocation_type
                    .or_else(|| {
                        needs_inferred_allocation
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
                    })
                    .filter(|ty| self.source_erasure(ty).as_ref() == Some(allocation_owner));
                let explicit_function_targets = inferred_allocation_type.is_none();
                drop(constraints);
                let hidden = self
                    .member_names
                    .hidden_constructor_parameters(method)
                    .cloned();
                let enclosing_parameter = self.member_names.enclosing_constructor_parameter(method);
                let mut enclosing = None;
                let mut enclosing_type = None;
                let args = insn
                    .operands()
                    .iter()
                    .skip(1)
                    .enumerate()
                    .filter_map(|(index, arg)| {
                        if !hidden
                            .as_ref()
                            .is_some_and(|hidden| hidden.contains(&index))
                        {
                            return Some(match method.descriptor.parameters.get(index) {
                                Some(expected) => {
                                    match argument_source_types.get(index).cloned().flatten() {
                                        Some(source) => self
                                            .arg_as_source_target(arg, expected, &source)
                                            .map(|expression| {
                                                if explicit_function_targets
                                                    && self.is_function_object_expression(arg)
                                                {
                                                    JavaExpr::Cast {
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
                            });
                        }
                        if enclosing_parameter == Some(index) {
                            let expression = self.arg(arg);
                            enclosing = Some(expression);
                            enclosing_type = method.descriptor.parameters.get(index).cloned();
                        }
                        None
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let enclosing = enclosing.transpose()?.filter(|expression| {
                    !self.is_implicit_enclosing_instance(expression, enclosing_type.as_ref())
                });
                let concrete_type = self.source_type(allocation_owner)?;
                let allocation_type =
                    Self::instantiation_type(inferred_allocation_type.unwrap_or(concrete_type));
                Ok(JavaExpr::New {
                    enclosing: enclosing.map(Box::new),
                    ty: allocation_type,
                    target_type: None,
                    args,
                    anonymous_body: None,
                })
            }
            InsnType::NewInstance => Err(JavaLoweringError::UnrecoveredObjectInitialization(
                insn.offset,
            )),
            InsnType::NewArray => Ok(JavaExpr::NewArray {
                element_type: self.source_type(self.array_element_type(insn)?)?,
                dimensions: vec![self.arg(
                    insn.operands()
                        .first()
                        .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                )?],
                initializer: Vec::new(),
            }),
            InsnType::FilledNewArray => Ok(JavaExpr::NewArray {
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
                let condition = predicate.ok_or(JavaLoweringError::MissingCondition)?;
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
                Ok(JavaExpr::Conditional {
                    condition: Box::new(condition),
                    when_true: Box::new(
                        self.arg(
                            insn.operands()
                                .first()
                                .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                        )?,
                    ),
                    when_false: Box::new(
                        self.arg(
                            insn.operands()
                                .get(1)
                                .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                        )?,
                    ),
                })
            }
            InsnType::Cmp => self.comparison(insn),
            _ => Err(JavaLoweringError::UnsupportedExpression(insn.insn_type)),
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
        expected: Option<&JavaType>,
    ) -> Option<JavaType> {
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

    fn invoke(
        &mut self,
        insn: &SemanticOperation,
        expected_source_type: Option<&JavaType>,
    ) -> Result<JavaExpr, JavaLoweringError> {
        let method = Self::method(insn.payload.reference.as_ref())?;
        let invoke_type = insn
            .payload
            .invoke_type
            .ok_or(JavaLoweringError::MissingPayload {
                instruction: insn.insn_type,
                field: "invoke_type",
            })?;
        let is_static = invoke_type == InvokeType::Static;
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
            .is_some_and(|receiver| {
                matches!(receiver.insn_type, InsnType::Invoke | InsnType::Constructor)
            });
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
        let receiver_value = (!is_static).then(|| insn.operands().first()).flatten();
        let receiver_actual_type =
            receiver_value.and_then(|receiver| self.source_receiver_type(receiver));
        let raw_receiver_type = (!is_static)
            .then(|| self.source_type(&method.owner).ok())
            .flatten()
            .map(JavaType::into_raw);
        let receiver_actual_is_source_compatible =
            receiver_actual_type.as_ref().is_some_and(|actual| {
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
        let receiver_accepts_inferred_type = receiver_value
            .zip(inferred_receiver_source_type.as_ref())
            .is_some_and(|(receiver, expected)| self.accepts_target_type(receiver, expected));
        let receiver_is_source_compatible =
            receiver_actual_is_source_compatible || receiver_accepts_inferred_type;
        let receiver_source_type = if receiver_requires_capture_conversion {
            raw_receiver_type.clone()
        } else if receiver_actual_is_source_compatible {
            receiver_actual_type.clone()
        } else if receiver_accepts_inferred_type {
            inferred_receiver_source_type
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
        let capture_witness_targets = contract
            .as_ref()
            .and_then(|contract| {
                constraints.capture_witness_specialization(
                    &contract.signature.type_parameters,
                    &contract.signature.parameter_types,
                )
            })
            .map(|specialized| {
                contract
                    .as_ref()
                    .expect("capture witness requires a generic contract")
                    .signature
                    .parameter_types
                    .iter()
                    .map(|formal| specialized.invocation_input_type(formal))
                    .collect::<Vec<_>>()
            });
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
            None => {
                if let Some(targets) = capture_witness_targets {
                    argument_source_types = targets;
                }
                Vec::new()
            }
        };
        drop(constraints);
        let receiver = match invoke_type {
            InvokeType::Static => None,
            InvokeType::Super => Some(Box::new(JavaExpr::Super)),
            _ => {
                let receiver = insn
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
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
                            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                        let erased = self.source_type(&method.owner)?.into_raw();
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
        let call_arguments = insn
            .operands()
            .iter()
            .skip(usize::from(!is_static))
            .cloned()
            .collect::<Vec<_>>();
        let overload_casts = self.overload_argument_casts(method, &call_arguments);
        let args = insn
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
                        JavaExpr::Cast {
                            ty: self.source_type(expected)?.into_raw(),
                            value: Box::new(self.arg(arg)?),
                        }
                    }
                    None => self.arg_as(arg, expected)?,
                };
                let expression = match (&target_type, &expression) {
                    (Some(target), JavaExpr::Cast { ty, .. })
                        if GenericCast::is_parameterized(target)
                            && !GenericCast::has_wildcard(target)
                            && !GenericCast::is_parameterized(ty)
                            && Self::same_erasure(ty, target) =>
                    {
                        JavaExpr::Cast {
                            ty: target.clone(),
                            value: Box::new(expression),
                        }
                    }
                    (Some(target), JavaExpr::Name(name)) => {
                        let actual = self.binding_types.name_type(name).cloned();
                        if actual
                            .as_ref()
                            .is_some_and(|actual| !self.source_assignable_to(actual, target))
                        {
                            let erased = self.source_type(expected)?.into_raw();
                            self.source_cast(expression, arg, actual.as_ref(), target, &erased)
                        } else {
                            expression
                        }
                    }
                    _ => expression,
                };
                let expression = if unresolved_poly_select
                    && !matches!(&expression, JavaExpr::Cast { ty, .. } if self.source_erasure(ty).as_ref() == Some(expected))
                {
                    JavaExpr::Cast {
                        ty: self.source_type(expected)?.into_raw(),
                        value: Box::new(expression),
                    }
                } else {
                    expression
                };
                let expression = if overload_casts.contains(&index)
                    && !matches!(&expression, JavaExpr::Cast { ty, .. } if self.source_erasure(ty).as_ref() == Some(expected))
                {
                    JavaExpr::Cast {
                        ty: self.overload_cast_type(expected, target_type.as_ref())?,
                        value: Box::new(expression),
                    }
                } else {
                    expression
                };
                self.disambiguate_null_argument(method, index, expected, expression)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(JavaExpr::Call {
            receiver,
            owner: if is_static {
                Some(self.source_type(&method.owner)?)
            } else {
                None
            },
            type_arguments: invocation_type_arguments,
            method: self.member_names.method(method),
            args,
        })
    }

    fn overload_cast_type(
        &self,
        erased: &ArgType,
        inferred: Option<&JavaType>,
    ) -> Result<JavaType, JavaLoweringError> {
        if let Some(inferred) = inferred {
            if self.source_erasure(inferred).as_ref() == Some(erased) {
                return Ok(inferred.clone());
            }
        }
        Ok(self.source_type(erased)?.into_raw())
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
                        && !matches!(target, JavaType::Primitive(_))
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
        targets: &[Option<JavaType>],
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
        expression: JavaExpr,
    ) -> Result<JavaExpr, JavaLoweringError> {
        if !matches!(expression, JavaExpr::Literal(JavaLiteral::Null))
            || !self.member_names.null_argument_requires_cast(method, index)
        {
            return Ok(expression);
        }
        Ok(JavaExpr::Cast {
            ty: self.source_type(expected)?,
            value: Box::new(expression),
        })
    }

    /// Method-select receivers are standalone expressions in Java. A generic
    /// invocation used as a receiver cannot consume the selected method's owner
    /// type as target-typing evidence, so an explicit DEX check-cast remains
    /// necessary unless the operand is independently assignable.
    fn preserve_standalone_check_cast(
        &self,
        value: &SemanticExpression,
        expression: JavaExpr,
    ) -> JavaExpr {
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
        if matches!(&expression, JavaExpr::Cast { ty, .. }
                if ty == &target
                    || (!GenericCast::has_generic_evidence(&target)
                        && GenericCast::has_generic_evidence(ty)
                        && Self::same_erasure(ty, &target)))
            || self.source_check_cast_is_redundant(operation, &target)
        {
            return expression;
        }
        JavaExpr::Cast {
            ty: target,
            value: Box::new(expression),
        }
    }

    fn specialize_standalone_invocation(
        &self,
        value: &SemanticExpression,
        expected: &JavaType,
        expression: &mut JavaExpr,
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
        if let JavaExpr::Call {
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
        expected: &JavaType,
    ) -> Result<JavaExpr, JavaLoweringError> {
        if expected == &JavaType::boolean() {
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
                        .ok_or(JavaLoweringError::MissingPayload {
                            instruction: operation.insn_type,
                            field: "conversion_type",
                        })?;
                let operand = operation
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(operation.insn_type))?;
                let source_target = target
                    .is_reference()
                    .then(|| self.reference_cast_source_type(operation))
                    .flatten();
                if target.is_reference() && Self::constant(operand) == Some(0) {
                    Ok(JavaExpr::Literal(JavaLiteral::Null))
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
                    let erased = self.source_type(target)?.into_raw();
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
                    let erased = self.source_type(target)?.into_raw();
                    Ok(self.source_cast(expression, operand, actual.as_ref(), expected, &erased))
                } else {
                    Ok(JavaExpr::Cast {
                        ty: self.source_type(target)?,
                        value: Box::new(self.arg_with_source_type(operand, expected)?),
                    })
                }
            }
            _ => self.arg(value),
        }?;
        self.specialize_construction(&mut expression, expected);
        Ok(expression)
    }

    fn arg_as_with_source_type(
        &mut self,
        value: &SemanticExpression,
        erased: &ArgType,
        expected: &JavaType,
    ) -> Result<JavaExpr, JavaLoweringError> {
        let source_erasure = matches!(expected, JavaType::Primitive(_))
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
        self.specialize_construction(&mut expression, expected);
        Ok(expression)
    }

    fn specialize_construction(&self, expression: &mut JavaExpr, expected: &JavaType) {
        let JavaExpr::New {
            ty, target_type, ..
        } = expression
        else {
            return;
        };
        let expected = Self::instantiation_type(expected.clone());
        if Self::same_erasure(ty, &expected) && self.is_raw_generic_type(ty) {
            *ty = expected.clone();
        }
        *target_type = Some(expected);
    }

    fn instantiation_type(mut ty: JavaType) -> JavaType {
        if let JavaType::Class(class) = &mut ty {
            for segment in &mut class.segments {
                if segment
                    .arguments
                    .iter()
                    .any(|argument| matches!(argument, JavaTypeArgument::Any))
                {
                    segment.arguments.clear();
                    continue;
                }
                segment.arguments = std::mem::take(&mut segment.arguments)
                    .into_iter()
                    .map(|argument| {
                        let value = match argument {
                            JavaTypeArgument::Any => unreachable!(),
                            JavaTypeArgument::Exact(value)
                            | JavaTypeArgument::Extends(value)
                            | JavaTypeArgument::Super(value) => value,
                        };
                        JavaTypeArgument::Exact(value)
                    })
                    .collect();
            }
        }
        ty
    }

    fn source_expression_type(&self, value: &SemanticExpression) -> Option<JavaType> {
        if self.is_this(value) {
            return self.source_current_type.clone();
        }
        if let SemanticExpression::Select {
            when_true,
            when_false,
            ..
        } = value
        {
            let true_type = self.source_expression_type(when_true);
            let false_type = self.source_expression_type(when_false);
            let is_reference = |ty: &JavaType| !matches!(ty, JavaType::Primitive(_));
            if when_false.literal_value() == Some(0) && true_type.as_ref().is_some_and(is_reference)
            {
                return true_type;
            }
            if when_true.literal_value() == Some(0) && false_type.as_ref().is_some_and(is_reference)
            {
                return false_type;
            }
            let is_null = |branch: &SemanticExpression| {
                branch.literal_value() == Some(0)
                    && branch.declared_type().is_some_and(ArgType::is_reference)
            };
            let joined = match (is_null(when_true), is_null(when_false)) {
                (true, false) => false_type,
                (false, true) => true_type,
                _ => true_type.zip(false_type).and_then(|(left, right)| {
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

    fn source_requirement_type(&self, value: &SemanticExpression) -> Option<&JavaType> {
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

    fn declared_operation_source_type(&self, operation: &SemanticOperation) -> Option<JavaType> {
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
    ) -> Option<JavaType> {
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

    fn intrinsic_invocation_source_type(&self, operation: &SemanticOperation) -> Option<JavaType> {
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
    ) -> Option<JavaType> {
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
    ) -> Option<JavaType> {
        self.generic_argument_source_type(value, erased_formal)
            .filter(|ty| !self.is_raw_generic_type(ty))
    }

    fn is_raw_generic_type(&self, ty: &JavaType) -> bool {
        match ty {
            JavaType::Array(element) => self.is_raw_generic_type(element),
            JavaType::Class(class) => {
                let Some(erased) = self.source_erasure(ty) else {
                    return false;
                };
                self.generic_type_projection
                    .as_deref()
                    .and_then(|projection| projection.declared_type_parameters(&erased))
                    .is_some_and(|parameters| {
                        !parameters.is_empty()
                            && class
                                .segments
                                .last()
                                .is_some_and(|segment| segment.arguments.is_empty())
                    })
            }
            JavaType::Variable(_) | JavaType::Primitive(_) => false,
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
    ) -> Option<JavaType> {
        let requirement = self.generic_argument_source_type(value, erased)?;
        if !self.has_generic_argument_evidence(&requirement) {
            return None;
        }
        let erased = self.source_type(erased).ok()?.into_raw();
        Self::source_return_requires_cast(&requirement, &erased).then_some(requirement)
    }

    fn intrinsic_source_type(&self, value: &SemanticExpression) -> Option<JavaType> {
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
                        JavaType::Array(element) => Some(*element),
                        JavaType::Class(_) | JavaType::Variable(_) | JavaType::Primitive(_) => None,
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

    fn cast_source_type(&self, value: &SemanticExpression) -> Option<JavaType> {
        self.definition_source_type(value)
            .or_else(|| self.intrinsic_source_type(value))
            .or_else(|| self.source_expression_type(value))
    }

    fn definition_source_type(&self, value: &SemanticExpression) -> Option<JavaType> {
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

    fn reference_cast_source_type(&self, operation: &SemanticOperation) -> Option<JavaType> {
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
        target: &JavaType,
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

    fn class_literal_source_type(&self, represented: &ArgType) -> Option<JavaType> {
        let represented = self.source_type(represented).ok()?.into_raw();
        let JavaType::Class(mut class) = self
            .source_type(&ArgType::object("java/lang/Class"))
            .ok()?
            .into_raw()
        else {
            return None;
        };
        class.segments.last_mut()?.arguments = vec![JavaTypeArgument::Exact(represented)];
        Some(JavaType::Class(class))
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

    fn source_erasure(&self, source: &JavaType) -> Option<ArgType> {
        self.type_relations().erasure_of(source)
    }

    fn source_assignable_to(&self, source: &JavaType, target: &JavaType) -> bool {
        self.type_relations().is_assignable(source, target)
    }

    fn type_relations(&self) -> JavaTypeRelations<'_> {
        JavaTypeRelations::new(
            &self.source_types,
            &self.source_type_erasures,
            self.generic_type_projection.as_deref(),
        )
        .with_direct_supertypes(Some(self.source_object_types.as_ref()))
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

    fn accepts_target_type(&self, value: &SemanticExpression, target: &JavaType) -> bool {
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
        if operation.insn_type == InsnType::Constructor {
            let Some(owner) = operation.allocation_type() else {
                return false;
            };
            return self.source_erasure(target).as_ref() == Some(owner)
                || self
                    .generic_type_projection
                    .as_deref()
                    .is_some_and(|projection| {
                        projection.specialize_subtype(owner, target).is_some()
                    });
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
        let mut inferred_receiver_target = None;
        if constraints.owner_is_raw(&contract.owner) {
            let Some(receiver) = (!is_static).then(|| operation.operands().first()).flatten()
            else {
                return false;
            };
            let Some(inferred) =
                self.owner_inferred_from_arguments(operation, method, contract, Some(target))
            else {
                return false;
            };
            if !self.accepts_target_type(receiver, &inferred) {
                return false;
            }
            constraints.constrain_owner(&contract.owner, &inferred);
            if constraints.owner_is_raw(&contract.owner) {
                return false;
            }
            inferred_receiver_target = Some(inferred);
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
                if receiver.as_operation().is_some_and(|receiver| {
                    matches!(receiver.insn_type, InsnType::Invoke | InsnType::Constructor)
                }) {
                    if let Some(owner) = inferred_receiver_target.or_else(|| {
                        self.owner_inferred_from_arguments(
                            operation,
                            method,
                            contract,
                            Some(target),
                        )
                        .or_else(|| constraints.owner_type(&contract.owner))
                    }) {
                        if !self.accepts_target_type(receiver, &owner) {
                            return false;
                        }
                    }
                }
            }
        }
        constraints
            .instantiate(&contract.signature.return_type)
            .is_some_and(|actual| self.source_assignable_to(&actual, target))
    }

    fn source_receiver_type(&self, value: &SemanticExpression) -> Option<JavaType> {
        self.source_expression_type(value)
    }

    fn same_erasure(left: &JavaType, right: &JavaType) -> bool {
        match (left, right) {
            (JavaType::Class(left), JavaType::Class(right)) => left.name() == right.name(),
            (JavaType::Array(left), JavaType::Array(right)) => Self::same_erasure(left, right),
            (JavaType::Primitive(left), JavaType::Primitive(right)) => left == right,
            _ => left == right,
        }
    }

    fn has_generic_argument_evidence(&self, ty: &JavaType) -> bool {
        let JavaType::Class(class) = ty else {
            return matches!(ty, JavaType::Variable(_) | JavaType::Array(_));
        };
        class.segments.iter().any(|segment| {
            segment.arguments.iter().any(|argument| match argument {
                JavaTypeArgument::Any => false,
                JavaTypeArgument::Exact(value)
                | JavaTypeArgument::Extends(value)
                | JavaTypeArgument::Super(value) => self.type_argument_has_evidence(value),
            })
        })
    }

    fn type_argument_has_evidence(&self, ty: &JavaType) -> bool {
        match ty {
            JavaType::Variable(_) | JavaType::Primitive(_) => true,
            JavaType::Array(element) => self.type_argument_has_evidence(element),
            JavaType::Class(class) => {
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

    fn has_only_default_type_arguments(&self, ty: &JavaType) -> bool {
        let JavaType::Class(class) = ty else {
            return false;
        };
        let arguments = class
            .segments
            .iter()
            .flat_map(|segment| &segment.arguments)
            .collect::<Vec<_>>();
        !arguments.is_empty()
            && arguments.into_iter().all(|argument| {
                let JavaTypeArgument::Exact(JavaType::Class(value)) = argument else {
                    return false;
                };
                let value = JavaType::Class(value.clone());
                !GenericCast::is_parameterized(&value)
                    && self.source_erasure(&value) == Some(ArgType::object("java/lang/Object"))
            })
    }

    fn target_has_source_erasure(&self, source: &JavaType, erased: &ArgType) -> bool {
        match (source, erased) {
            (JavaType::Variable(variable), erased)
                if self.source_type_erasures.get(variable) == Some(erased) =>
            {
                return true;
            }
            (JavaType::Array(source), ArgType::Array(erased))
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

    fn source_register_type(&self, register: &RegisterArg) -> Option<&JavaType> {
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

    fn source_definition_type(&self, register: &RegisterArg) -> Option<JavaType> {
        let variable_type = self.source_register_type(register);
        let value_type = crate::ir::analysis::SsaVar::from_reg(register)
            .and_then(|value| self.source_value_types.get(&value));
        match (variable_type, value_type) {
            (Some(variable), Some(value))
                if Self::same_erasure(variable, value)
                    && !self.source_assignable_to(value, variable)
                    && self.source_assignable_to(variable, value) =>
            {
                Some(value.clone())
            }
            (Some(variable), Some(value))
                if Self::same_erasure(variable, value)
                    && !self.source_assignable_to(value, variable)
                    && !self.source_assignable_to(variable, value) =>
            {
                Some(variable.clone().into_raw())
            }
            (Some(variable), _) => Some(variable.clone()),
            (None, Some(value)) => Some(value.clone()),
            (None, None) => None,
        }
    }

    fn constructor_invocation(
        &mut self,
        insn: &SemanticOperation,
    ) -> Result<JavaStmt, JavaLoweringError> {
        let method = Self::method(insn.payload.reference.as_ref())?;
        let receiver = insn
            .operands()
            .first()
            .and_then(SemanticExpression::as_register)
            .ok_or(JavaLoweringError::InvalidConstructorReceiver)?;
        if receiver.code_var != self.this_code_var {
            return Err(JavaLoweringError::UnrecoveredObjectInitialization(
                insn.offset,
            ));
        }
        let target = if self.current_type.as_ref() == Some(&method.owner) {
            JavaConstructorTarget::This
        } else {
            JavaConstructorTarget::Super
        };
        let hidden = self
            .member_names
            .hidden_constructor_parameters(method)
            .cloned()
            .unwrap_or_default();
        let source_argument_types = self
            .invocation_solver(insn)
            .map(|(mut solver, _, contract)| {
                if matches!(target, JavaConstructorTarget::Super) {
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
        Ok(JavaStmt::ConstructorInvocation {
            target,
            args: insn
                .operands()
                .iter()
                .skip(1)
                .enumerate()
                .filter_map(|(index, arg)| {
                    if hidden.contains(&index) {
                        return None;
                    }
                    Some(match method.descriptor.parameters.get(index) {
                        Some(expected) => {
                            let target_type =
                                source_argument_types.get(index).and_then(Option::as_ref).cloned();
                            let expression = match target_type.as_ref() {
                                Some(source) => self.arg_as_source_target(arg, expected, source),
                                None => self.arg_as(arg, expected),
                            };
                            expression.and_then(|expression| {
                                let needs_overload_cast = overload_casts.contains(&index)
                                    && !matches!(&expression, JavaExpr::Cast { ty, .. } if self.source_erasure(ty).as_ref() == Some(expected));
                                let needs_null_cast = expected.is_reference()
                                    && matches!(
                                        &expression,
                                        JavaExpr::Literal(JavaLiteral::Null)
                                    );
                                let expression = if needs_overload_cast || needs_null_cast {
                                    JavaExpr::Cast {
                                        ty: if needs_overload_cast {
                                            self.overload_cast_type(
                                                expected,
                                                target_type.as_ref(),
                                            )?
                                        } else {
                                            target_type
                                                .clone()
                                                .unwrap_or(self.source_type(expected)?)
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
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn comparison(&mut self, insn: &SemanticOperation) -> Result<JavaExpr, JavaLoweringError> {
        let left_arg = insn
            .operands()
            .first()
            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
        let right_arg = insn
            .operands()
            .get(1)
            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
        let comparison_type = self.expression_type(left_arg)?.clone();
        let left = self.arg_as(left_arg, &comparison_type)?;
        let right = self.arg_as(right_arg, &comparison_type)?;
        let owner = match &comparison_type {
            ArgType::Primitive(PrimitiveType::Float) => "java/lang/Float",
            ArgType::Primitive(PrimitiveType::Double) => "java/lang/Double",
            ArgType::Primitive(PrimitiveType::Long) => "java/lang/Long",
            other => return Err(JavaLoweringError::InvalidComparisonType(other.clone())),
        };
        let owner_type = self.source_type(&ArgType::object(owner))?;
        if owner == "java/lang/Long" {
            return Ok(JavaExpr::Call {
                receiver: None,
                owner: Some(owner_type),
                type_arguments: Vec::new(),
                method: JavaIdentifier::from_dex("compare"),
                args: vec![left, right],
            });
        }
        let nan_value = match insn.payload.cmp_bias {
            Some(crate::ir::CmpBias::Lt) => -1,
            Some(crate::ir::CmpBias::Gt) => 1,
            Some(crate::ir::CmpBias::None) | None => {
                return Err(JavaLoweringError::MissingPayload {
                    instruction: insn.insn_type,
                    field: "cmp_bias",
                });
            }
        };
        let is_nan = |value| JavaExpr::Call {
            receiver: None,
            owner: Some(owner_type.clone()),
            type_arguments: Vec::new(),
            method: JavaIdentifier::from_dex("isNaN"),
            args: vec![value],
        };
        Ok(JavaExpr::Conditional {
            condition: Box::new(JavaExpr::Binary {
                left: Box::new(is_nan(left.clone())),
                op: JavaBinaryOp::LogicalOr,
                right: Box::new(is_nan(right.clone())),
            }),
            when_true: Box::new(JavaExpr::Literal(JavaLiteral::Integer(nan_value))),
            when_false: Box::new(JavaExpr::Conditional {
                condition: Box::new(JavaExpr::Binary {
                    left: Box::new(left.clone()),
                    op: JavaBinaryOp::Less,
                    right: Box::new(right.clone()),
                }),
                when_true: Box::new(JavaExpr::Literal(JavaLiteral::Integer(-1))),
                when_false: Box::new(JavaExpr::Conditional {
                    condition: Box::new(JavaExpr::Binary {
                        left: Box::new(left),
                        op: JavaBinaryOp::Equal,
                        right: Box::new(right),
                    }),
                    when_true: Box::new(JavaExpr::Literal(JavaLiteral::Integer(0))),
                    when_false: Box::new(JavaExpr::Literal(JavaLiteral::Integer(1))),
                }),
            }),
        })
    }

    fn array_element_type<'a>(
        &'a self,
        insn: &'a SemanticOperation,
    ) -> Result<&'a ArgType, JavaLoweringError> {
        let array_type = match &insn.result {
            Some(result) => self.types.ssa_type(result)?,
            None => insn
                .payload
                .class_type
                .as_ref()
                .ok_or(JavaLoweringError::MissingPayload {
                    instruction: insn.insn_type,
                    field: "result or class_type",
                })?,
        };
        array_type
            .as_array_element()
            .ok_or_else(|| JavaLoweringError::InvalidArrayType {
                instruction: insn.insn_type,
                offset: insn.offset,
                ty: array_type.clone(),
            })
    }

    fn fill_array(&mut self, insn: &SemanticOperation) -> Result<JavaStmt, JavaLoweringError> {
        let array_arg = insn
            .operands()
            .first()
            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
        let array = self.arg(array_arg)?;
        let array_type = self.ssa_expression_type(array_arg)?.clone();
        let element = array_type
            .as_array_element()
            .ok_or_else(|| JavaLoweringError::InvalidArrayType {
                instruction: insn.insn_type,
                offset: insn.offset,
                ty: array_type.clone(),
            })?
            .clone();
        let data = insn
            .payload
            .fill_array_data
            .as_ref()
            .ok_or(JavaLoweringError::MissingArrayData)?;
        let width = usize::from(data.element_width);
        if !matches!(width, 1 | 2 | 4 | 8) {
            return Err(JavaLoweringError::InvalidArrayElementWidth(
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
                    .map_err(|_| JavaLoweringError::InvalidIntegerLiteral(index as i64))?;
                let bits = bytes.iter().enumerate().fold(0u64, |value, (shift, byte)| {
                    value | (u64::from(*byte) << (shift * 8))
                });
                let shift = 64 - width * 8;
                let signed = ((bits << shift) as i64) >> shift;
                let literal = if width == 8 {
                    JavaLiteral::Long(signed)
                } else {
                    JavaLiteral::Integer(
                        i32::try_from(signed)
                            .map_err(|_| JavaLoweringError::InvalidIntegerLiteral(signed))?,
                    )
                };
                Ok(JavaStmt::Assign {
                    target: JavaExpr::ArrayAccess {
                        array: Box::new(array.clone()),
                        index: Box::new(JavaExpr::Literal(JavaLiteral::Integer(index))),
                    },
                    op: JavaAssignOp::Assign,
                    value: self.coerce(JavaExpr::Literal(literal), &element),
                })
            })
            .collect::<Result<Vec<_>, JavaLoweringError>>()?;
        Ok(JavaStmt::Block(statements))
    }

    fn predicate(&mut self, condition: &SemanticPredicate) -> Result<JavaExpr, JavaLoweringError> {
        let mut pending = vec![JavaPredicateTask::Visit(condition)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                JavaPredicateTask::Visit(condition) => match condition {
                    SemanticPredicate::True => {
                        results.push(JavaExpr::Literal(JavaLiteral::Boolean(true)))
                    }
                    SemanticPredicate::False => {
                        results.push(JavaExpr::Literal(JavaLiteral::Boolean(false)))
                    }
                    SemanticPredicate::Test(test) => {
                        results.push(self.test_condition(test, false)?)
                    }
                    SemanticPredicate::Not(inner) => match inner.as_ref() {
                        SemanticPredicate::Test(test) => {
                            results.push(self.test_condition(test, true)?)
                        }
                        inner => {
                            pending.push(JavaPredicateTask::Not);
                            pending.push(JavaPredicateTask::Visit(inner));
                        }
                    },
                    SemanticPredicate::And(terms) | SemanticPredicate::Or(terms) => {
                        let conjunction = matches!(condition, SemanticPredicate::And(_));
                        pending.push(JavaPredicateTask::Junction {
                            count: terms.len(),
                            conjunction,
                        });
                        pending.extend(terms.iter().rev().map(JavaPredicateTask::Visit));
                    }
                },
                JavaPredicateTask::Not => {
                    let operand = results.pop().ok_or(JavaLoweringError::MalformedPredicate)?;
                    results.push(Self::negate_boolean(operand));
                }
                JavaPredicateTask::Junction { count, conjunction } => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(JavaLoweringError::MalformedPredicate)?;
                    let mut terms = results.drain(start..).collect::<Vec<_>>();
                    if terms.is_empty() {
                        results.push(JavaExpr::Literal(JavaLiteral::Boolean(conjunction)));
                        continue;
                    }
                    let operator = if conjunction {
                        JavaBinaryOp::LogicalAnd
                    } else {
                        JavaBinaryOp::LogicalOr
                    };
                    while terms.len() > 1 {
                        let mut next = Vec::with_capacity(terms.len().div_ceil(2));
                        let mut current = std::mem::take(&mut terms).into_iter();
                        while let Some(left) = current.next() {
                            next.push(match current.next() {
                                Some(right) => JavaExpr::Binary {
                                    left: Box::new(left),
                                    op: operator,
                                    right: Box::new(right),
                                },
                                None => left,
                            });
                        }
                        terms = next;
                    }
                    results.push(terms.pop().ok_or(JavaLoweringError::MalformedPredicate)?);
                }
            }
        }
        if results.len() != 1 {
            return Err(JavaLoweringError::MalformedPredicate);
        }
        results.pop().ok_or(JavaLoweringError::MalformedPredicate)
    }

    fn semantic_value(
        &mut self,
        value: &SemanticExpression,
        expected: &ArgType,
    ) -> Result<JavaExpr, JavaLoweringError> {
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
                JavaExpr::Conditional {
                    condition: Box::new(condition),
                    when_true: Box::new(when_true),
                    when_false: Box::new(when_false),
                }
            });
        }
        self.arg_as(value, expected)
    }

    fn boolean_value(&mut self, value: &SemanticExpression) -> Result<JavaExpr, JavaLoweringError> {
        if let Some(value) = Self::semantic_constant(value) {
            if matches!(value, 0 | 1) {
                return Ok(JavaExpr::Literal(JavaLiteral::Boolean(value != 0)));
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
                JavaExpr::Literal(JavaLiteral::Boolean(true)),
                JavaExpr::Literal(JavaLiteral::Boolean(false)),
            ) => condition,
            (
                JavaExpr::Literal(JavaLiteral::Boolean(false)),
                JavaExpr::Literal(JavaLiteral::Boolean(true)),
            ) => Self::negate_boolean(condition),
            (JavaExpr::Literal(JavaLiteral::Boolean(true)), _) => JavaExpr::Binary {
                left: Box::new(condition),
                op: JavaBinaryOp::LogicalOr,
                right: Box::new(when_false),
            },
            (JavaExpr::Literal(JavaLiteral::Boolean(false)), _) => JavaExpr::Binary {
                left: Box::new(Self::negate_boolean(condition)),
                op: JavaBinaryOp::LogicalAnd,
                right: Box::new(when_false),
            },
            (_, JavaExpr::Literal(JavaLiteral::Boolean(true))) => JavaExpr::Binary {
                left: Box::new(Self::negate_boolean(condition)),
                op: JavaBinaryOp::LogicalOr,
                right: Box::new(when_true),
            },
            (_, JavaExpr::Literal(JavaLiteral::Boolean(false))) => JavaExpr::Binary {
                left: Box::new(condition),
                op: JavaBinaryOp::LogicalAnd,
                right: Box::new(when_true),
            },
            _ => JavaExpr::Conditional {
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
    ) -> Result<JavaExpr, JavaLoweringError> {
        let mut op = condition
            .payload
            .if_op
            .ok_or(JavaLoweringError::MissingPayload {
                instruction: condition.insn_type,
                field: "if_op",
            })?;
        if inverted {
            op = op.invert();
        }
        let left_arg = condition
            .operands()
            .first()
            .ok_or(JavaLoweringError::MissingArgument(InsnType::If))?;
        let right_arg = condition
            .operands()
            .get(1)
            .ok_or(JavaLoweringError::MissingArgument(InsnType::If))?;
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
                return Ok(JavaExpr::Binary {
                    left: Box::new(self.boolean_value(left_arg)?),
                    op: if op == IfOp::Eq {
                        JavaBinaryOp::Equal
                    } else {
                        JavaBinaryOp::NotEqual
                    },
                    right: Box::new(self.boolean_value(right_arg)?),
                });
            }
        }
        if let Some(comparison) = self.direct_comparison(left_arg, right_arg, op)? {
            return Ok(comparison);
        }
        if self.has_intrinsic_numeric_comparison_domain(left_arg, right_arg)? {
            return Ok(JavaExpr::Binary {
                left: Box::new(self.arg(left_arg)?),
                op: Self::comparison_operator(op),
                right: Box::new(self.arg(right_arg)?),
            });
        }
        let mut left = self.comparison_arg(left_arg, right_arg)?;
        let right = self.comparison_arg(right_arg, left_arg)?;
        if matches!(op, IfOp::Eq | IfOp::Ne) {
            if let Some(bridge) = self.equality_bridge_type(left_arg, right_arg) {
                left = JavaExpr::Cast {
                    ty: bridge,
                    value: Box::new(left),
                };
            }
        }
        Ok(JavaExpr::Binary {
            left: Box::new(left),
            op: Self::comparison_operator(op),
            right: Box::new(right),
        })
    }

    fn boolean_test(
        &mut self,
        value: &SemanticExpression,
        literal: &SemanticExpression,
        op: IfOp,
    ) -> Result<Option<JavaExpr>, JavaLoweringError> {
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
    ) -> Option<JavaType> {
        let left = self.source_expression_type(left)?;
        let right = self.source_expression_type(right)?;
        if self.source_assignable_to(&left, &right) || self.source_assignable_to(&right, &left) {
            return None;
        }
        let left_erasure = self.source_erasure(&left)?;
        let right_erasure = self.source_erasure(&right)?;
        (left_erasure == right_erasure && left_erasure.is_reference())
            .then(|| self.source_type(&left_erasure).ok().map(JavaType::into_raw))
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
    ) -> Result<bool, JavaLoweringError> {
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
    ) -> Result<Option<JavaExpr>, JavaLoweringError> {
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
            .ok_or(JavaLoweringError::MissingArgument(InsnType::Cmp))?;
        let right = comparison
            .operands()
            .get(1)
            .ok_or(JavaLoweringError::MissingArgument(InsnType::Cmp))?;
        let comparison_type = self.expression_type(left)?.clone();
        let Some(test) =
            ComparisonSemantics::recover(comparison.payload.cmp_bias, &comparison_type, op)
        else {
            return Ok(None);
        };
        let expression = JavaExpr::Binary {
            left: Box::new(self.arg_as(left, &comparison_type)?),
            op: Self::comparison_operator(test.operator),
            right: Box::new(self.arg_as(right, &comparison_type)?),
        };
        Ok(Some(if test.negated {
            JavaExpr::Unary {
                op: JavaUnaryOp::LogicalNot,
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

    fn negate_boolean(expression: JavaExpr) -> JavaExpr {
        expression.negated()
    }

    fn assignment(
        &mut self,
        result: &RegisterArg,
        value: JavaExpr,
    ) -> Result<JavaStmt, JavaLoweringError> {
        let inferred_type = self.types.register_type(result)?.clone();
        let value = self.coerce(value, &inferred_type);
        let name = self.register_name(result)?;
        let key = SourceVariable::of(result)?;
        if !self.declared.contains(&name) {
            let ty = self
                .source_definition_type(result)
                .map(Ok)
                .unwrap_or_else(|| self.source_type(&inferred_type))?;
            if self.inline_declarations.contains(&key) {
                self.declared.insert(name.clone());
                self.binding_types.bind_name(name.clone(), ty.clone());
                return Ok(JavaStmt::Variable {
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
        expression: &JavaExpr,
        expected: Option<&ArgType>,
    ) -> bool {
        let Some(expected) = expected else {
            return false;
        };
        match expression {
            JavaExpr::QualifiedThis(outer) => self
                .source_type(expected)
                .is_ok_and(|expected| expected == *outer),
            JavaExpr::This => self.current_type.as_ref().is_some_and(|current| {
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

enum JavaPredicateTask<'a> {
    Visit(&'a SemanticPredicate),
    Not,
    Junction { count: usize, conjunction: bool },
}

impl JavaDialect for DexJavaDialect {
    type Error = JavaLoweringError;

    fn condition(&mut self, condition: &SemanticPredicate) -> Result<JavaExpr, Self::Error> {
        self.predicate(condition)
    }

    fn negated_condition(
        &mut self,
        condition: &SemanticPredicate,
    ) -> Result<JavaExpr, Self::Error> {
        self.predicate(&condition.clone().negate())
    }

    fn expression(&mut self, value: &SemanticExpression) -> Result<JavaExpr, Self::Error> {
        self.arg(value)
    }

    fn iterable_expression(
        &mut self,
        element_type: &JavaType,
        value: &SemanticExpression,
    ) -> Result<JavaExpr, Self::Error> {
        if matches!(value.declared_type(), Some(ArgType::Array(_))) {
            return self.arg(value);
        }
        let erased_type = ArgType::object("java/lang/Iterable");
        let erased_source = self.source_type(&erased_type)?;
        let JavaType::Class(mut iterable) = erased_source.clone() else {
            unreachable!("a source class always lowers to a class type");
        };
        let Some(segment) = iterable.segments.last_mut() else {
            return self.arg(value);
        };
        segment.arguments = vec![match element_type {
            JavaType::Primitive(_) => JavaTypeArgument::Exact(element_type.clone()),
            _ => JavaTypeArgument::Extends(element_type.clone()),
        }];
        let expected = JavaType::Class(iterable);
        let compatible = self.cast_source_type(value).is_some_and(|actual| {
            self.source_assignable_to(&actual, &expected)
                || self
                    .generic_type_projection
                    .as_deref()
                    .and_then(|projection| projection.project_supertype(&actual, &erased_type))
                    .is_some_and(|projected| self.source_assignable_to(&projected, &expected))
        });
        if compatible || self.accepts_target_type(value, &expected) {
            return self.arg(value);
        }
        let JavaType::Class(mut recovery_type) = expected else {
            unreachable!("an Iterable source type is always a class type");
        };
        recovery_type
            .segments
            .last_mut()
            .expect("Iterable has a source type segment")
            .arguments = vec![JavaTypeArgument::Exact(element_type.clone())];
        self.arg_as_source_target(value, &erased_type, &JavaType::Class(recovery_type))
    }

    fn return_expression(
        &mut self,
        value: &SemanticExpression,
        condition: Option<&SemanticPredicate>,
    ) -> Result<JavaExpr, Self::Error> {
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

    fn throw_expression(&mut self, value: &SemanticExpression) -> Result<JavaExpr, Self::Error> {
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
            || matches!(&expression, JavaExpr::Cast { ty, .. } if ty == &candidate.source)
        {
            return Ok(expression);
        }
        Ok(JavaExpr::Cast {
            ty: candidate.source.clone(),
            value: Box::new(expression),
        })
    }

    fn loop_variable(
        &mut self,
        register: &RegisterArg,
    ) -> Result<(JavaType, JavaIdentifier), Self::Error> {
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
            // A source variable can span disjoint DEX register lifetimes. Do
            // not let an earlier primitive lifetime type a reference-valued
            // enhanced-for binding (or vice versa).
            .filter(|source| {
                let source_is_primitive = matches!(source, JavaType::Primitive(_));
                !(source_is_primitive && binding_type.is_reference()
                    || !source_is_primitive && binding_type.is_primitive())
            })
            .cloned()
            .map(Ok)
            .unwrap_or_else(|| self.source_type(binding_type))?;
        self.binding_types.bind_name(name.clone(), ty.clone());
        Ok((ty, name))
    }

    fn synthetic_variable(&mut self, hint: &str) -> JavaIdentifier {
        self.name_scope.claim(JavaIdentifier::from_dex(hint))
    }

    fn statement(&mut self, statement: &SemanticStatement) -> Result<JavaStmt, Self::Error> {
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
                    JavaStmt::Expression(
                        self.insn_expr(insn, None, None)?,
                    )
                }
            }
            InsnType::FilledNewArray => {
                let ty = self.source_type(insn.payload.class_type.as_ref().ok_or(
                    JavaLoweringError::MissingPayload {
                        instruction: insn.insn_type,
                        field: "class_type",
                    },
                )?)?;
                JavaStmt::Variable {
                    ty,
                    name: self.synthetic_variable("unusedArray"),
                    value: Some(self.insn_expr(insn, None, None)?),
                }
            }
            InsnType::Iput => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                let value = insn
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                let owner = insn
                    .operands()
                    .get(1)
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                if self.outer_instance(field, owner).is_some_and(|binding| {
                    value
                        .as_register()
                        .and_then(|register| register.code_var)
                        == binding.constructor_parameter
                        && binding.constructor_parameter.is_some()
                }) {
                    return Ok(JavaStmt::Empty);
                }
                JavaStmt::Assign {
                    target: JavaExpr::Field {
                        owner: Box::new(self.arg(owner)?),
                        name: self.member_names.field(field),
                    },
                    op: JavaAssignOp::Assign,
                    value: self.arg_as_field(value, field, Some(owner))?,
                }
            }
            InsnType::Sput => {
                let field = Self::field(insn.payload.reference.as_ref())?;
                JavaStmt::Assign {
                    target: JavaExpr::StaticField {
                        owner: self.source_type(&field.owner)?,
                        name: self.member_names.field(field),
                    },
                    op: JavaAssignOp::Assign,
                    value: self.arg_as_field(
                        insn.operands()
                            .first()
                            .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                        field,
                        None,
                    )?,
                }
            }
            InsnType::Aput => {
                let array_arg = insn
                    .operands()
                    .get(1)
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                let array_type = self.ssa_expression_type(array_arg)?.clone();
                let element = array_type
                    .as_array_element()
                    .ok_or_else(|| JavaLoweringError::InvalidArrayType {
                        instruction: insn.insn_type,
                        offset: insn.offset,
                        ty: array_type.clone(),
                    })?
                    .clone();
                let source_element = self.source_expression_type(array_arg).and_then(|ty| match ty {
                    JavaType::Array(element) => Some(*element),
                    JavaType::Primitive(_) | JavaType::Class(_) | JavaType::Variable(_) => None,
                });
                let value = insn
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                JavaStmt::Assign {
                    target: JavaExpr::ArrayAccess {
                        array: Box::new(self.arg(array_arg)?),
                        index: Box::new(
                            self.arg(
                                insn.operands().get(2).ok_or(
                                    JavaLoweringError::MissingArgument(insn.insn_type),
                                )?,
                            )?,
                        ),
                    },
                    op: JavaAssignOp::Assign,
                    value: match source_element.as_ref() {
                        Some(source) => self.arg_as_source_target(value, &element, source)?,
                        None => self.arg_as(value, &element)?,
                    },
                }
            }
            InsnType::CompoundAssign => JavaStmt::Assign {
                target: self.arg(
                    insn.compound_target()
                        .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                )?,
                op: Self::assignment_operator(
                    insn.payload
                        .arith_op
                        .ok_or(JavaLoweringError::MissingPayload {
                            instruction: insn.insn_type,
                            field: "arith_op",
                        })?,
                )?,
                value: self.arg(
                    insn.operands()
                        .last()
                        .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?,
                )?,
            },
            InsnType::FillArray => self.fill_array(insn)?,
            InsnType::CheckCast => {
                let value = insn
                    .operands()
                    .first()
                    .ok_or(JavaLoweringError::MissingArgument(insn.insn_type))?;
                let target = self.arg(value)?;
                JavaStmt::Assign {
                    target: target.clone(),
                    op: JavaAssignOp::Assign,
                    value: JavaExpr::Cast {
                        ty: self.source_type(
                            insn.conversion_type()
                                .ok_or(JavaLoweringError::MissingPayload {
                                    instruction: insn.insn_type,
                                    field: "conversion_type",
                                })?,
                        )?,
                        value: Box::new(target),
                    },
                }
            }
            InsnType::Nop => Err(JavaLoweringError::UnsupportedStatement(InsnType::Nop))?,
            InsnType::Phi => Err(JavaLoweringError::UnrecoveredPhi(insn.offset))?,
            InsnType::MoveResult => {
                Err(JavaLoweringError::UnrecoveredMoveResult(insn.offset))?
            }
            InsnType::MoveException => {
                Err(JavaLoweringError::UnrecoveredExceptionValue(insn.offset))?
            }
            InsnType::MonitorEnter | InsnType::MonitorExit => {
                Err(JavaLoweringError::UnrecoveredMonitor(insn.offset))?
            }
            _ => Err(JavaLoweringError::UnsupportedStatement(insn.insn_type))?,
            }
        };
        Ok(lowered)
    }

    fn catch_binding(
        &mut self,
        register: Option<&RegisterArg>,
    ) -> Result<JavaCatchBinding, Self::Error> {
        let Some(register) = register else {
            return Ok(JavaCatchBinding::local(
                self.name_scope.claim(JavaIdentifier::from_dex("e")),
            ));
        };
        let variable = SourceVariable::of(register)?;
        let name = self.register_name(register)?;
        if self.catch_storage.contains(&variable) {
            let parameter = self.name_scope.claim(JavaIdentifier::from_dex("e"));
            return Ok(JavaCatchBinding::stored(parameter, name));
        }
        self.declared.insert(name.clone());
        self.locals.remove(&name);
        Ok(JavaCatchBinding::local(name))
    }

    fn type_name(&mut self, ty: &ArgType) -> Result<JavaType, Self::Error> {
        self.source_type(ty)
    }

    fn take_declarations(&mut self) -> Vec<JavaStmt> {
        std::mem::take(&mut self.locals)
            .into_iter()
            .map(|(name, ty)| JavaStmt::Variable {
                ty,
                name,
                value: None,
            })
            .collect()
    }

    fn prepare(&mut self, root: &crate::ir::SemanticNode) -> Result<(), Self::Error> {
        crate::profile_scope!("java_prepare.verify", JavaInputVerifier::verify(root))?;
        let diagnostics_enabled = self
            .observer
            .is_enabled(crate::ir::AnalysisEventKind::SourceTypes);
        let source_types = crate::profile_scope!("java_prepare.source_types", {
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
        let declarations = crate::profile_scope!("java_prepare.declarations", {
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use crate::ir::analysis::SourceTypeEnvironment;
    use crate::ir::{ArgType, LiteralArg, RegisterArg, SemanticExpression, SemanticPredicate};

    use super::{DexJavaDialect, JavaDialect, JavaMemberNames, JavaType};

    #[test]
    fn foreach_binding_ignores_a_reused_primitive_source_variable_type() {
        let erased = ArgType::object("java/util/ArrayList");
        let reference = JavaType::source_class("java.util.ArrayList");
        let mut dialect = DexJavaDialect::new(
            true,
            None,
            &[],
            &[],
            &SourceTypeEnvironment::default(),
            BTreeMap::from([(erased.clone(), reference.clone())]),
            Arc::new(JavaMemberNames::default()),
        )
        .expect("static dialect");
        dialect.source_variable_types.insert(6, JavaType::int());
        let register = RegisterArg {
            reg_num: 1,
            ty: erased,
            ssa_version: Some(3),
            code_var: Some(6),
        };

        let (ty, _) = JavaDialect::loop_variable(&mut dialect, &register)
            .expect("reference-valued foreach binding");

        assert_eq!(ty, reference);
    }

    #[test]
    fn foreach_binding_keeps_a_reference_source_type_over_object_erasure() {
        let erased = ArgType::object("java/lang/Object");
        let reference = JavaType::source_class("example.Element");
        let mut dialect = DexJavaDialect::new(
            true,
            None,
            &[],
            &[],
            &SourceTypeEnvironment::default(),
            BTreeMap::from([(erased.clone(), JavaType::source_class("java.lang.Object"))]),
            Arc::new(JavaMemberNames::default()),
        )
        .expect("static dialect");
        dialect.source_variable_types.insert(6, reference.clone());
        let register = RegisterArg {
            reg_num: 1,
            ty: erased,
            ssa_version: Some(3),
            code_var: Some(6),
        };

        let (ty, _) =
            JavaDialect::loop_variable(&mut dialect, &register).expect("reference source type");

        assert_eq!(ty, reference);
    }

    #[test]
    fn select_types_an_integer_zero_as_null_against_a_reference_branch() {
        let string = ArgType::string();
        let source_string = JavaType::source_class("java.lang.String");
        let dialect = DexJavaDialect::new(
            true,
            None,
            &[],
            &[],
            &SourceTypeEnvironment::default(),
            BTreeMap::from([(string.clone(), source_string.clone())]),
            Arc::new(JavaMemberNames::default()),
        )
        .expect("static dialect");
        let select = SemanticExpression::select(
            SemanticPredicate::True,
            SemanticExpression::Literal(LiteralArg::int(0)),
            SemanticExpression::Register(RegisterArg {
                reg_num: 1,
                ty: string,
                ssa_version: Some(1),
                code_var: None,
            }),
        );

        assert_eq!(dialect.source_expression_type(&select), Some(source_string));
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
pub enum JavaLoweringError {
    Structure(JavaStructuralError),
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

impl From<JavaStructuralError> for JavaLoweringError {
    fn from(source: JavaStructuralError) -> Self {
        Self::Structure(source)
    }
}

impl From<DeclarationError> for JavaLoweringError {
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

impl From<TypeConstraintError> for JavaLoweringError {
    fn from(source: TypeConstraintError) -> Self {
        Self::Type(source)
    }
}

impl fmt::Display for JavaLoweringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Structure(source) => write!(f, "Java structure is invalid: {source}"),
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
                write!(f, "required Java reference is missing at {caller}")
            }
            Self::InvalidReferenceKind => {
                f.write_str("instruction has the wrong member-reference kind")
            }
            Self::MissingCondition => f.write_str("conditional value has no predicate"),
            Self::UnexpectedCondition(instruction) => {
                write!(f, "{instruction:?} carries a conditional-value predicate")
            }
            Self::MalformedPredicate => f.write_str("Java predicate tree is malformed"),
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
                write!(f, "{operator:?} has no Java compound-assignment form")
            }
            Self::InvalidIntegerLiteral(value) => {
                write!(f, "{value} is outside the Java int literal range")
            }
            Self::InvalidCharLiteral(value) => {
                write!(f, "{value} is not a valid Java char literal")
            }
            Self::InvalidConstructorReceiver => {
                f.write_str("constructor invocation has no receiver")
            }
            Self::InvalidThisLvalue => f.write_str("`this` cannot be used as a Java lvalue"),
            Self::UnrecoveredObjectInitialization(offset) => {
                write!(f, "object initialization at {offset:#x} was not recovered")
            }
            Self::UnrecoveredPhi(offset) => {
                write!(f, "SSA phi at {offset:#x} reached Java lowering")
            }
            Self::UnrecoveredMoveResult(offset) => {
                write!(f, "move-result at {offset:#x} reached Java lowering")
            }
            Self::UnrecoveredExceptionValue(offset) => {
                write!(f, "move-exception at {offset:#x} reached Java lowering")
            }
            Self::UnsupportedExpression(instruction) => {
                write!(f, "{instruction:?} has no Java expression form")
            }
            Self::UnsupportedStatement(instruction) => {
                write!(f, "{instruction:?} has no Java statement form")
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
                "Java source type is unresolved: {ty} (requested at {}:{})",
                caller.file(),
                caller.line()
            ),
            Self::MissingSourceType(ty) => {
                write!(f, "Java source naming cannot represent {ty}")
            }
            Self::Type(source) => write!(f, "type recovery failed: {source}"),
        }
    }
}

impl std::error::Error for JavaLoweringError {
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
        operator: JavaAssignOp,
        value: JavaExpr,
    },
    Update(super::JavaUpdateOp),
}

impl LocalAssignment {
    fn recover(target: &JavaIdentifier, value: JavaExpr) -> Self {
        let JavaExpr::Binary { left, op, right } = value else {
            return Self::plain(value);
        };
        if left.as_ref() != &JavaExpr::Name(target.clone()) {
            return Self::plain(JavaExpr::Binary { left, op, right });
        }
        let Some(operator) = Self::compound_operator(op) else {
            return Self::plain(JavaExpr::Binary { left, op, right });
        };
        let value = *right;
        if Self::is_one(&value) {
            if operator == JavaAssignOp::Add {
                return Self::Update(super::JavaUpdateOp::Increment);
            }
            if operator == JavaAssignOp::Subtract {
                return Self::Update(super::JavaUpdateOp::Decrement);
            }
        }
        Self::Assignment { operator, value }
    }

    fn plain(value: JavaExpr) -> Self {
        Self::Assignment {
            operator: JavaAssignOp::Assign,
            value,
        }
    }

    fn into_statement(self, name: JavaIdentifier) -> JavaStmt {
        let target = JavaExpr::Name(name);
        match self {
            Self::Assignment { operator, value } => JavaStmt::Assign {
                target,
                op: operator,
                value,
            },
            Self::Update(op) => JavaStmt::Expression(JavaExpr::Update {
                op,
                target: Box::new(target),
                prefix: false,
            }),
        }
    }

    fn is_one(value: &JavaExpr) -> bool {
        matches!(
            value,
            JavaExpr::Literal(JavaLiteral::Integer(1) | JavaLiteral::Long(1))
        )
    }

    fn compound_operator(operator: JavaBinaryOp) -> Option<JavaAssignOp> {
        Some(match operator {
            JavaBinaryOp::Add => JavaAssignOp::Add,
            JavaBinaryOp::Subtract => JavaAssignOp::Subtract,
            JavaBinaryOp::Multiply => JavaAssignOp::Multiply,
            JavaBinaryOp::Divide => JavaAssignOp::Divide,
            JavaBinaryOp::Remainder => JavaAssignOp::Remainder,
            JavaBinaryOp::BitAnd => JavaAssignOp::BitAnd,
            JavaBinaryOp::BitOr => JavaAssignOp::BitOr,
            JavaBinaryOp::BitXor => JavaAssignOp::BitXor,
            JavaBinaryOp::ShiftLeft => JavaAssignOp::ShiftLeft,
            JavaBinaryOp::ShiftRight => JavaAssignOp::ShiftRight,
            JavaBinaryOp::UnsignedShiftRight => JavaAssignOp::UnsignedShiftRight,
            JavaBinaryOp::LogicalAnd
            | JavaBinaryOp::LogicalOr
            | JavaBinaryOp::Equal
            | JavaBinaryOp::NotEqual
            | JavaBinaryOp::Less
            | JavaBinaryOp::GreaterEqual
            | JavaBinaryOp::Greater
            | JavaBinaryOp::LessEqual => return None,
        })
    }
}

struct JavaArithmetic;

impl JavaArithmetic {
    fn binary(left: JavaExpr, operator: JavaBinaryOp, right: JavaExpr) -> JavaExpr {
        let (operator, right) = Self::normalize_sign(operator, right);
        JavaExpr::Binary {
            left: Box::new(left),
            op: operator,
            right: Box::new(right),
        }
    }

    fn normalize_sign(operator: JavaBinaryOp, right: JavaExpr) -> (JavaBinaryOp, JavaExpr) {
        let Some(positive) = Self::positive_integer(&right) else {
            return (operator, right);
        };
        match operator {
            JavaBinaryOp::Add => (JavaBinaryOp::Subtract, positive),
            JavaBinaryOp::Subtract => (JavaBinaryOp::Add, positive),
            _ => (operator, right),
        }
    }

    fn positive_integer(value: &JavaExpr) -> Option<JavaExpr> {
        let literal = match value {
            JavaExpr::Literal(JavaLiteral::Integer(value)) if *value < 0 => {
                JavaLiteral::Integer(value.checked_neg()?)
            }
            JavaExpr::Literal(JavaLiteral::Long(value)) if *value < 0 => {
                JavaLiteral::Long(value.checked_neg()?)
            }
            _ => return None,
        };
        Some(JavaExpr::Literal(literal))
    }
}

impl DexJavaDialect {
    #[track_caller]
    fn missing_reference() -> JavaLoweringError {
        JavaLoweringError::MissingReference {
            caller: std::panic::Location::caller(),
        }
    }

    fn field(reference: Option<&MemberReference>) -> Result<&FieldReference, JavaLoweringError> {
        let reference = reference.ok_or_else(|| Self::missing_reference())?;
        let MemberReference::Field(reference) = reference else {
            return Err(JavaLoweringError::InvalidReferenceKind);
        };
        Ok(reference)
    }

    fn method(reference: Option<&MemberReference>) -> Result<&MethodReference, JavaLoweringError> {
        let reference = reference.ok_or_else(|| Self::missing_reference())?;
        let MemberReference::Method(reference) = reference else {
            return Err(JavaLoweringError::InvalidReferenceKind);
        };
        Ok(reference)
    }

    #[track_caller]
    fn source_type(&self, ty: &ArgType) -> Result<JavaType, JavaLoweringError> {
        if let Some(source_type) = self.source_types.get(ty) {
            return Ok(source_type.clone());
        }
        if let Some(source_type) = self
            .generic_type_projection
            .as_deref()
            .and_then(|projection| projection.resolve_type(ty))
        {
            return Ok(source_type);
        }
        Ok(match ty {
            ArgType::Primitive(primitive) => JavaType::Primitive(match primitive {
                PrimitiveType::Void => JavaPrimitiveType::Void,
                PrimitiveType::Boolean => JavaPrimitiveType::Boolean,
                PrimitiveType::Byte => JavaPrimitiveType::Byte,
                PrimitiveType::Short => JavaPrimitiveType::Short,
                PrimitiveType::Char => JavaPrimitiveType::Char,
                PrimitiveType::Int => JavaPrimitiveType::Int,
                PrimitiveType::Long => JavaPrimitiveType::Long,
                PrimitiveType::Float => JavaPrimitiveType::Float,
                PrimitiveType::Double => JavaPrimitiveType::Double,
                PrimitiveType::Object | PrimitiveType::Array => {
                    return Err(JavaLoweringError::UnresolvedSourceType {
                        ty: ty.clone(),
                        caller: std::panic::Location::caller(),
                    });
                }
            }),
            ArgType::Object(_) => return Err(JavaLoweringError::MissingSourceType(ty.clone())),
            ArgType::Array(element) => JavaType::array(self.source_type(element)?),
            ArgType::Unknown(_) => {
                return Err(JavaLoweringError::UnresolvedSourceType {
                    ty: ty.clone(),
                    caller: std::panic::Location::caller(),
                });
            }
        })
    }

    fn binary_operator(operator: ArithOp) -> (JavaBinaryOp, bool) {
        match operator {
            ArithOp::Add => (JavaBinaryOp::Add, false),
            ArithOp::Sub => (JavaBinaryOp::Subtract, false),
            ArithOp::Rsub => (JavaBinaryOp::Subtract, true),
            ArithOp::Mul => (JavaBinaryOp::Multiply, false),
            ArithOp::Div => (JavaBinaryOp::Divide, false),
            ArithOp::Rem => (JavaBinaryOp::Remainder, false),
            ArithOp::And => (JavaBinaryOp::BitAnd, false),
            ArithOp::Or => (JavaBinaryOp::BitOr, false),
            ArithOp::Xor => (JavaBinaryOp::BitXor, false),
            ArithOp::Shl => (JavaBinaryOp::ShiftLeft, false),
            ArithOp::Shr => (JavaBinaryOp::ShiftRight, false),
            ArithOp::Ushr => (JavaBinaryOp::UnsignedShiftRight, false),
        }
    }

    fn assignment_operator(operator: ArithOp) -> Result<JavaAssignOp, JavaLoweringError> {
        Ok(match operator {
            ArithOp::Add => JavaAssignOp::Add,
            ArithOp::Sub => JavaAssignOp::Subtract,
            ArithOp::Rsub => return Err(JavaLoweringError::InvalidAssignmentOperator(operator)),
            ArithOp::Mul => JavaAssignOp::Multiply,
            ArithOp::Div => JavaAssignOp::Divide,
            ArithOp::Rem => JavaAssignOp::Remainder,
            ArithOp::And => JavaAssignOp::BitAnd,
            ArithOp::Or => JavaAssignOp::BitOr,
            ArithOp::Xor => JavaAssignOp::BitXor,
            ArithOp::Shl => JavaAssignOp::ShiftLeft,
            ArithOp::Shr => JavaAssignOp::ShiftRight,
            ArithOp::Ushr => JavaAssignOp::UnsignedShiftRight,
        })
    }

    fn comparison_operator(operator: IfOp) -> JavaBinaryOp {
        match operator {
            IfOp::Eq => JavaBinaryOp::Equal,
            IfOp::Ne => JavaBinaryOp::NotEqual,
            IfOp::Lt => JavaBinaryOp::Less,
            IfOp::Ge => JavaBinaryOp::GreaterEqual,
            IfOp::Gt => JavaBinaryOp::Greater,
            IfOp::Le => JavaBinaryOp::LessEqual,
        }
    }

    fn literal(literal: &crate::ir::LiteralArg) -> Result<JavaLiteral, JavaLoweringError> {
        Ok(match literal.ty.as_primitive() {
            Some(PrimitiveType::Boolean) => JavaLiteral::Boolean(literal.value != 0),
            Some(PrimitiveType::Long) => JavaLiteral::Long(literal.value),
            Some(PrimitiveType::Float) => JavaLiteral::Float(f32::from_bits(literal.value as u32)),
            Some(PrimitiveType::Double) => {
                JavaLiteral::Double(f64::from_bits(literal.value as u64))
            }
            Some(PrimitiveType::Char) => {
                let value = u16::try_from(literal.value)
                    .map_err(|_| JavaLoweringError::InvalidCharLiteral(literal.value))?;
                JavaLiteral::Character(value)
            }
            _ if literal.value == 0
                && matches!(literal.ty, ArgType::Object(_) | ArgType::Array(_)) =>
            {
                JavaLiteral::Null
            }
            _ => JavaLiteral::Integer(
                i32::try_from(literal.value)
                    .map_err(|_| JavaLoweringError::InvalidIntegerLiteral(literal.value))?,
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
