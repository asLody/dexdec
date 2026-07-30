//! Constraint-graph type recovery for SSA values.

#[path = "types/constraints.rs"]
mod constraints;
#[path = "types/hierarchy.rs"]
mod hierarchy;
#[path = "types/lattice.rs"]
mod lattice;

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use crate::ir::{
    analysis::{SsaValueGraph, SsaVar},
    ArgType, InsnArg, InsnType, PrimitiveType, RegisterArg, CFG,
};

use constraints::TypeConstraintGraph;
use lattice::TypeLattice;

pub use hierarchy::{ClassHierarchyIndex, ReferenceTypeInfo, SubtypeRelation, TypeHierarchy};

#[derive(Debug, Clone)]
pub enum TypeConstraintError {
    MissingReference {
        offset: u32,
        instruction: InsnType,
    },
    InvalidReferenceKind {
        offset: u32,
        instruction: InsnType,
    },
    MissingInvokeType(u32),
    InvokeArity {
        offset: u32,
        expected: usize,
        actual: usize,
    },
    UnresolvedValue {
        register: u32,
        version: Option<u32>,
    },
    UnresolvedArgument,
    WrappedValueWithoutResult(u32),
    ConflictingSourceVariable {
        variable: u32,
        left: ArgType,
        right: ArgType,
    },
    ConflictingSourceValues {
        variable: u32,
        left_value: SsaVar,
        left: ArgType,
        right_value: SsaVar,
        right: ArgType,
    },
}

impl fmt::Display for TypeConstraintError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingReference {
                offset,
                instruction,
            } => write!(
                formatter,
                "{instruction:?} at {offset} has no member reference"
            ),
            Self::InvalidReferenceKind {
                offset,
                instruction,
            } => write!(
                formatter,
                "{instruction:?} at {offset} has the wrong member reference kind"
            ),
            Self::MissingInvokeType(offset) => {
                write!(formatter, "invoke at {offset} has no dispatch kind")
            }
            Self::InvokeArity {
                offset,
                expected,
                actual,
            } => write!(
                formatter,
                "invoke at {offset} has {actual} arguments, expected {expected}"
            ),
            Self::UnresolvedValue { register, version } => {
                write!(formatter, "type of v{register}_{version:?} is unresolved")
            }
            Self::UnresolvedArgument => formatter.write_str("argument type is unresolved"),
            Self::WrappedValueWithoutResult(offset) => write!(
                formatter,
                "wrapped instruction at {offset} has no value result"
            ),
            Self::ConflictingSourceVariable {
                variable,
                left,
                right,
            } => write!(
                formatter,
                "source variable v{variable} combines incompatible types {left:?} and {right:?}"
            ),
            Self::ConflictingSourceValues {
                variable,
                left_value,
                left,
                right_value,
                right,
            } => write!(
                formatter,
                "source variable v{variable} combines {left_value:?} ({left:?}) with {right_value:?} ({right:?})"
            ),
        }
    }
}

impl std::error::Error for TypeConstraintError {}

#[derive(Debug, Clone, Default)]
pub struct SsaTypeEnvironment {
    types: BTreeMap<SsaVar, ArgType>,
}

impl SsaTypeEnvironment {
    pub fn value_type(&self, value: SsaVar) -> Option<&ArgType> {
        self.types.get(&value)
    }

    pub fn known_types(&self) -> impl Iterator<Item = &ArgType> {
        self.types.values()
    }

    #[track_caller]
    pub fn register_type<'a>(
        &'a self,
        register: &'a RegisterArg,
    ) -> Result<&'a ArgType, TypeConstraintError> {
        if let Some(ty) = SsaVar::from_reg(register).and_then(|value| self.types.get(&value)) {
            return Ok(ty);
        }
        if register.ty.is_known() {
            return Ok(&register.ty);
        }
        Err(TypeConstraintError::UnresolvedValue {
            register: register.reg_num,
            version: register.ssa_version,
        })
    }

    pub fn argument_type<'a>(
        &'a self,
        argument: &'a InsnArg,
    ) -> Result<&'a ArgType, TypeConstraintError> {
        match argument {
            InsnArg::Reg(register) => self.register_type(register),
            InsnArg::Lit(literal) if literal.ty.is_known() => Ok(&literal.ty),
            InsnArg::Lit(_) => Err(TypeConstraintError::UnresolvedArgument),
            InsnArg::Wrapped(instruction) => {
                let result = instruction.result.as_ref().ok_or(
                    TypeConstraintError::WrappedValueWithoutResult(instruction.offset),
                )?;
                self.register_type(result)
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct SourceTypeEnvironment {
    ssa: SsaTypeEnvironment,
    variables: BTreeMap<u32, ArgType>,
}

impl SourceTypeEnvironment {
    pub(super) fn from_ssa(
        ssa: SsaTypeEnvironment,
        variables: &super::CodeVariables,
        values: &super::SsaValueGraph,
        constants: &BTreeMap<SsaVar, InsnArg>,
        hierarchy: &dyn TypeHierarchy,
    ) -> Result<Self, TypeConstraintError> {
        let lattice = SourceTypeLattice::new(hierarchy);
        let mut source_types = BTreeMap::<u32, (ArgType, SsaVar)>::new();
        for (&value, &variable) in variables.assignments() {
            let observed_types = values.value(value).map(|value| &value.observed_types);
            let observed = observed_types.and_then(|types| lattice.select_observed(types));
            let null_reference = (constants.get(&value).and_then(InsnArg::literal_value)
                == Some(0))
            .then(|| {
                observed_types
                    .into_iter()
                    .flatten()
                    .filter(|ty| ty.is_reference())
                    .cloned()
                    .collect::<BTreeSet<_>>()
            })
            .filter(|types| !types.is_empty())
            .and_then(|types| lattice.select_observed(&types));
            let inferred = match (ssa.value_type(value).cloned(), observed) {
                (Some(inferred), Some(observed)) => {
                    lattice.meet(&inferred, &observed).or(Some(inferred))
                }
                (Some(inferred), None) => Some(inferred),
                (None, observed) => observed,
            };
            let selected = null_reference.or(inferred);
            let Some(ty) = selected else {
                continue;
            };
            if let Some((existing, existing_value)) = source_types.get_mut(&variable) {
                let Some(joined) = lattice.join(existing, &ty) else {
                    return Err(TypeConstraintError::ConflictingSourceValues {
                        variable,
                        left_value: *existing_value,
                        left: existing.clone(),
                        right_value: value,
                        right: ty,
                    });
                };
                *existing = joined;
            } else {
                source_types.insert(variable, (ty, value));
            }
        }
        Ok(Self {
            ssa,
            variables: source_types
                .into_iter()
                .map(|(variable, (ty, _))| (variable, ty))
                .collect(),
        })
    }

    pub(super) fn bind_variable(
        &mut self,
        variable: u32,
        ty: ArgType,
    ) -> Result<(), TypeConstraintError> {
        match self.variables.get(&variable) {
            Some(existing) if existing != &ty => {
                Err(TypeConstraintError::ConflictingSourceVariable {
                    variable,
                    left: existing.clone(),
                    right: ty,
                })
            }
            Some(_) => Ok(()),
            None => {
                self.variables.insert(variable, ty);
                Ok(())
            }
        }
    }

    pub(super) fn bind_declared_variable(
        &mut self,
        variable: u32,
        ty: ArgType,
        hierarchy: &dyn TypeHierarchy,
    ) -> Result<(), TypeConstraintError> {
        if let Some(existing) = self.variables.get(&variable) {
            SourceTypeLattice::new(hierarchy)
                .join(existing, &ty)
                .ok_or_else(|| TypeConstraintError::ConflictingSourceVariable {
                    variable,
                    left: existing.clone(),
                    right: ty.clone(),
                })?;
        }
        self.variables.insert(variable, ty);
        Ok(())
    }

    pub(super) fn merge_variable(
        &mut self,
        variable: u32,
        ty: ArgType,
        hierarchy: &dyn TypeHierarchy,
    ) -> Result<(), TypeConstraintError> {
        let Some(existing) = self.variables.get(&variable).cloned() else {
            self.variables.insert(variable, ty);
            return Ok(());
        };
        let joined = SourceTypeLattice::new(hierarchy)
            .join(&existing, &ty)
            .ok_or(TypeConstraintError::ConflictingSourceVariable {
                variable,
                left: existing,
                right: ty,
            })?;
        self.variables.insert(variable, joined);
        Ok(())
    }

    pub(super) fn bind_exception_type(
        &mut self,
        variable: u32,
        ty: ArgType,
    ) -> Result<(), TypeConstraintError> {
        if let Some(existing) = self.variables.get(&variable) {
            if !existing.is_reference() || !ty.is_reference() {
                return Err(TypeConstraintError::ConflictingSourceVariable {
                    variable,
                    left: existing.clone(),
                    right: ty,
                });
            }
        }
        self.variables.insert(variable, ty);
        Ok(())
    }

    pub(crate) fn refine_booleans(&mut self, variables: impl IntoIterator<Item = u32>) {
        for variable in variables {
            let Some(ty) = self.variables.get_mut(&variable) else {
                continue;
            };
            if matches!(
                ty,
                ArgType::Primitive(PrimitiveType::Boolean | PrimitiveType::Int)
            ) {
                *ty = ArgType::BOOLEAN;
            }
        }
    }

    pub fn known_types(&self) -> impl Iterator<Item = &ArgType> {
        self.variables.values().chain(self.ssa.known_types())
    }

    pub fn ssa_type<'a>(
        &'a self,
        register: &'a RegisterArg,
    ) -> Result<&'a ArgType, TypeConstraintError> {
        self.ssa.register_type(register)
    }

    #[track_caller]
    pub fn register_type<'a>(
        &'a self,
        register: &'a RegisterArg,
    ) -> Result<&'a ArgType, TypeConstraintError> {
        if let Some(ty) = register
            .code_var
            .and_then(|variable| self.variables.get(&variable))
        {
            return Ok(ty);
        }
        self.ssa.register_type(register)
    }

    pub fn argument_type<'a>(
        &'a self,
        argument: &'a InsnArg,
    ) -> Result<&'a ArgType, TypeConstraintError> {
        match argument {
            InsnArg::Reg(register) => self.register_type(register),
            InsnArg::Lit(literal) if literal.ty.is_known() => Ok(&literal.ty),
            InsnArg::Lit(_) => Err(TypeConstraintError::UnresolvedArgument),
            InsnArg::Wrapped(instruction) => {
                let result = instruction.result.as_ref().ok_or(
                    TypeConstraintError::WrappedValueWithoutResult(instruction.offset),
                )?;
                self.register_type(result)
            }
        }
    }
}

pub(super) struct SourceTypeLattice<'a> {
    hierarchy: &'a dyn TypeHierarchy,
}

impl<'a> SourceTypeLattice<'a> {
    pub(super) fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self { hierarchy }
    }

    pub(super) fn select_observed(
        &self,
        types: &std::collections::BTreeSet<ArgType>,
    ) -> Option<ArgType> {
        let mut known = types.iter().filter(|ty| ty.is_known());
        let mut selected = known.next()?.clone();
        for ty in known {
            selected = self.meet(&selected, ty)?;
        }
        Some(selected)
    }

    pub(super) fn meet(&self, left: &ArgType, right: &ArgType) -> Option<ArgType> {
        if left == right {
            return Some(left.clone());
        }
        if Self::narrow_integral(left) && Self::narrow_integral(right) {
            return Some(ArgType::INT);
        }
        if self.assignable(left, right) {
            return Some(left.clone());
        }
        self.assignable(right, left).then(|| right.clone())
    }

    pub(super) fn join(&self, left: &ArgType, right: &ArgType) -> Option<ArgType> {
        if left == right {
            return Some(left.clone());
        }
        if Self::narrow_integral(left) && Self::narrow_integral(right) {
            return Some(ArgType::INT);
        }
        if self.assignable(left, right) {
            return Some(right.clone());
        }
        if self.assignable(right, left) {
            return Some(left.clone());
        }
        match (left, right) {
            (ArgType::Object(left), ArgType::Object(right)) => self
                .hierarchy
                .least_common_supertype(left, right)
                .map(|ty| ArgType::object(&ty)),
            (ArgType::Array(_), ArgType::Array(_))
            | (ArgType::Array(_), ArgType::Object(_))
            | (ArgType::Object(_), ArgType::Array(_)) => Some(ArgType::object("java/lang/Object")),
            _ => None,
        }
    }

    fn assignable(&self, value: &ArgType, expected: &ArgType) -> bool {
        match (value, expected) {
            (ArgType::Object(value), ArgType::Object(expected)) => {
                self.hierarchy.subtype_relation(value, expected) == SubtypeRelation::Yes
            }
            (ArgType::Array(value), ArgType::Array(expected)) => value == expected,
            (ArgType::Array(_), ArgType::Object(expected)) => matches!(
                expected.as_str(),
                "java/lang/Object" | "java/lang/Cloneable" | "java/io/Serializable"
            ),
            _ => false,
        }
    }

    fn narrow_integral(ty: &ArgType) -> bool {
        matches!(
            ty,
            ArgType::Primitive(
                PrimitiveType::Boolean
                    | PrimitiveType::Byte
                    | PrimitiveType::Short
                    | PrimitiveType::Char
                    | PrimitiveType::Int
            )
        )
    }
}

pub struct TypeSolver<'a> {
    hierarchy: &'a dyn TypeHierarchy,
}

impl<'a> TypeSolver<'a> {
    pub fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self { hierarchy }
    }

    pub fn solve(
        self,
        cfg: &CFG,
        values: &SsaValueGraph,
        constants: &BTreeMap<SsaVar, InsnArg>,
    ) -> Result<SsaTypeEnvironment, TypeConstraintError> {
        let constraints = TypeConstraintGraph::collect(cfg, values, constants)?.normalize();
        Ok(SsaTypeEnvironment {
            types: TypeLattice::solve(&constraints, self.hierarchy),
        })
    }
}
