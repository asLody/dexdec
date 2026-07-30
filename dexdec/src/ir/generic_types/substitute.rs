use super::{
    ClassTypeSignature, InnerClassTypeSignature, JvmTypeSignature, SignatureSubstitutionError,
    TypeArgument, TypeSubstitution,
};

pub(super) struct SignatureSubstitution<'a> {
    values: &'a TypeSubstitution,
}

impl<'a> SignatureSubstitution<'a> {
    pub(super) fn new(values: &'a TypeSubstitution) -> Self {
        Self { values }
    }

    pub(super) fn ty(
        &self,
        signature: &JvmTypeSignature,
    ) -> Result<JvmTypeSignature, SignatureSubstitutionError> {
        self.apply(Task::Type(signature))?.into_type()
    }

    pub(super) fn class(
        &self,
        signature: &ClassTypeSignature,
    ) -> Result<ClassTypeSignature, SignatureSubstitutionError> {
        let JvmTypeSignature::ClassType(signature) =
            self.apply(Task::Class(signature))?.into_type()?
        else {
            return Err(SignatureSubstitutionError::ChangedClassKind);
        };
        Ok(signature)
    }

    pub(super) fn argument(
        &self,
        argument: &TypeArgument,
    ) -> Result<TypeArgument, SignatureSubstitutionError> {
        self.apply(Task::Argument(argument))?.into_argument()
    }

    fn apply<'signature>(
        &self,
        root: Task<'signature>,
    ) -> Result<Value, SignatureSubstitutionError> {
        let mut pending = vec![root];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::Type(signature) => self.schedule_type(signature, &mut pending, &mut results),
                Task::Class(class) => Self::schedule_class(class, &mut pending),
                Task::Argument(argument) => {
                    self.schedule_argument(argument, &mut pending, &mut results)
                }
                Task::Array => {
                    let element = Self::pop(&mut results, "array element")?.into_type()?;
                    results.push(Value::Type(JvmTypeSignature::Array(Box::new(element))));
                }
                Task::BuildArgument(variance) => {
                    let signature = Self::pop(&mut results, "type argument")?.into_type()?;
                    results.push(Value::Argument(match variance {
                        Variance::Extends => TypeArgument::Extends(signature),
                        Variance::Super => TypeArgument::Super(signature),
                        Variance::Exact => TypeArgument::Exact(signature),
                    }));
                }
                Task::BuildClass {
                    raw_name,
                    top_arguments,
                    inner,
                } => {
                    let count = top_arguments + inner.iter().map(|(_, count)| count).sum::<usize>();
                    let start = results.len().checked_sub(count).ok_or(
                        SignatureSubstitutionError::MissingOperand("class arguments"),
                    )?;
                    let arguments = results
                        .drain(start..)
                        .map(Value::into_argument)
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut arguments = arguments.into_iter();
                    let type_arguments = arguments.by_ref().take(top_arguments).collect();
                    let mut inner_segments = Vec::with_capacity(inner.len());
                    for (simple_name, count) in inner {
                        inner_segments.push(InnerClassTypeSignature {
                            simple_name,
                            type_arguments: arguments.by_ref().take(count).collect(),
                        });
                    }
                    results.push(Value::Type(JvmTypeSignature::ClassType(
                        ClassTypeSignature {
                            raw_name,
                            type_arguments,
                            inner_segments,
                        },
                    )));
                }
            }
        }
        if results.len() != 1 {
            return Err(SignatureSubstitutionError::ResultArity(results.len()));
        }
        Self::pop(&mut results, "root result")
    }

    fn pop(
        results: &mut Vec<Value>,
        context: &'static str,
    ) -> Result<Value, SignatureSubstitutionError> {
        results
            .pop()
            .ok_or(SignatureSubstitutionError::MissingOperand(context))
    }

    fn schedule_type<'signature>(
        &self,
        signature: &'signature JvmTypeSignature,
        pending: &mut Vec<Task<'signature>>,
        results: &mut Vec<Value>,
    ) {
        match signature {
            JvmTypeSignature::ClassType(class) => pending.push(Task::Class(class)),
            JvmTypeSignature::TypeVariable(name) => results.push(Value::Type(
                self.values
                    .get(name)
                    .and_then(Self::argument_type)
                    .unwrap_or_else(|| signature.clone()),
            )),
            JvmTypeSignature::Array(element) => {
                pending.push(Task::Array);
                pending.push(Task::Type(element));
            }
            JvmTypeSignature::BaseType(_) => results.push(Value::Type(signature.clone())),
        }
    }

    fn schedule_class<'signature>(
        class: &'signature ClassTypeSignature,
        pending: &mut Vec<Task<'signature>>,
    ) {
        let inner = class
            .inner_segments
            .iter()
            .map(|segment| (segment.simple_name.clone(), segment.type_arguments.len()))
            .collect();
        pending.push(Task::BuildClass {
            raw_name: class.raw_name.clone(),
            top_arguments: class.type_arguments.len(),
            inner,
        });
        let arguments = class.type_arguments.iter().chain(
            class
                .inner_segments
                .iter()
                .flat_map(|segment| segment.type_arguments.iter()),
        );
        pending.extend(arguments.rev().map(Task::Argument));
    }

    fn schedule_argument<'signature>(
        &self,
        argument: &'signature TypeArgument,
        pending: &mut Vec<Task<'signature>>,
        results: &mut Vec<Value>,
    ) {
        let (variance, signature) = match argument {
            TypeArgument::Unbounded => {
                results.push(Value::Argument(TypeArgument::Unbounded));
                return;
            }
            TypeArgument::Extends(signature) => (Variance::Extends, signature),
            TypeArgument::Super(signature) => (Variance::Super, signature),
            TypeArgument::Exact(signature) => (Variance::Exact, signature),
        };
        if let JvmTypeSignature::TypeVariable(name) = signature {
            if let Some(value) = self.values.get(name) {
                results.push(Value::Argument(Self::compose_argument(variance, value)));
                return;
            }
        }
        pending.push(Task::BuildArgument(variance));
        pending.push(Task::Type(signature));
    }

    fn argument_type(argument: &TypeArgument) -> Option<JvmTypeSignature> {
        match argument {
            TypeArgument::Exact(signature)
            | TypeArgument::Extends(signature)
            | TypeArgument::Super(signature) => Some(signature.clone()),
            TypeArgument::Unbounded => None,
        }
    }

    fn compose_argument(variance: Variance, argument: &TypeArgument) -> TypeArgument {
        match (variance, argument) {
            (Variance::Exact, argument) => argument.clone(),
            (Variance::Extends, TypeArgument::Exact(signature))
            | (Variance::Extends, TypeArgument::Extends(signature)) => {
                TypeArgument::Extends(signature.clone())
            }
            (Variance::Super, TypeArgument::Exact(signature))
            | (Variance::Super, TypeArgument::Super(signature)) => {
                TypeArgument::Super(signature.clone())
            }
            (Variance::Extends, TypeArgument::Super(_) | TypeArgument::Unbounded)
            | (Variance::Super, TypeArgument::Extends(_) | TypeArgument::Unbounded) => {
                TypeArgument::Unbounded
            }
        }
    }
}

enum Task<'a> {
    Type(&'a JvmTypeSignature),
    Class(&'a ClassTypeSignature),
    Argument(&'a TypeArgument),
    Array,
    BuildArgument(Variance),
    BuildClass {
        raw_name: String,
        top_arguments: usize,
        inner: Vec<(String, usize)>,
    },
}

enum Value {
    Type(JvmTypeSignature),
    Argument(TypeArgument),
}

impl Value {
    fn into_type(self) -> Result<JvmTypeSignature, SignatureSubstitutionError> {
        match self {
            Self::Type(signature) => Ok(signature),
            Self::Argument(_) => Err(SignatureSubstitutionError::ExpectedType),
        }
    }

    fn into_argument(self) -> Result<TypeArgument, SignatureSubstitutionError> {
        match self {
            Self::Argument(argument) => Ok(argument),
            Self::Type(_) => Err(SignatureSubstitutionError::ExpectedArgument),
        }
    }
}

#[derive(Clone, Copy)]
enum Variance {
    Extends,
    Super,
    Exact,
}
