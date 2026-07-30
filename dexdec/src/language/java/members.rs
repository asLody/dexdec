//! Class-wide Java member symbol allocation.
//!
//! DEX permits field and method sets that Java source cannot declare without
//! renaming (for example fields distinguished only by type, or methods
//! distinguished only by return type). Allocation is deterministic and every
//! body reference consumes the same symbol table as its declaration.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{ArgType, FieldReference, MethodDescriptor, MethodReference};

use super::{JavaIdentifier, JavaNameScope};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct JavaFieldSymbol {
    pub owner: ArgType,
    pub name: JavaIdentifier,
    pub field_type: ArgType,
}

impl JavaFieldSymbol {
    pub fn new(owner: ArgType, name: JavaIdentifier, field_type: ArgType) -> Self {
        Self {
            owner,
            name,
            field_type,
        }
    }

    fn key(&self) -> FieldSymbolKey {
        FieldSymbolKey {
            owner: self.owner.clone(),
            name: self.name.clone(),
            field_type: self.field_type.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct JavaMethodSymbol {
    pub owner: ArgType,
    pub name: JavaIdentifier,
    pub descriptor: MethodDescriptor,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct JavaConstructorLayout {
    owner: ArgType,
    descriptor: MethodDescriptor,
    hidden_parameters: BTreeSet<usize>,
    enclosing_parameter: Option<usize>,
}

impl JavaConstructorLayout {
    pub fn new(
        owner: ArgType,
        descriptor: MethodDescriptor,
        hidden_parameters: impl IntoIterator<Item = usize>,
    ) -> Self {
        Self {
            owner,
            descriptor,
            hidden_parameters: hidden_parameters.into_iter().collect(),
            enclosing_parameter: None,
        }
    }

    pub fn with_enclosing_parameter(mut self, parameter: usize) -> Self {
        self.hidden_parameters.insert(parameter);
        self.enclosing_parameter = Some(parameter);
        self
    }

    pub fn matches(&self, reference: &MethodReference) -> bool {
        reference.name == "<init>"
            && self.owner == reference.owner
            && self.descriptor == reference.descriptor
    }

    fn key(&self) -> ConstructorKey {
        ConstructorKey {
            owner: self.owner.clone(),
            descriptor: self.descriptor.clone(),
        }
    }
}

impl JavaMethodSymbol {
    pub fn new(owner: ArgType, name: JavaIdentifier, descriptor: MethodDescriptor) -> Self {
        Self {
            owner,
            name,
            descriptor,
        }
    }

    fn key(&self) -> MethodSymbolKey {
        MethodSymbolKey {
            owner: self.owner.clone(),
            name: self.name.clone(),
            descriptor: self.descriptor.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FieldSymbolKey {
    owner: ArgType,
    name: JavaIdentifier,
    field_type: ArgType,
}

impl From<&FieldReference> for FieldSymbolKey {
    fn from(reference: &FieldReference) -> Self {
        Self {
            owner: reference.owner.clone(),
            name: JavaIdentifier::from_dex(&reference.name),
            field_type: reference.field_type.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct MethodSymbolKey {
    owner: ArgType,
    name: JavaIdentifier,
    descriptor: MethodDescriptor,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct MethodOverloadKey {
    owner: ArgType,
    name: JavaIdentifier,
    arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ConstructorKey {
    owner: ArgType,
    descriptor: MethodDescriptor,
}

impl From<&MethodReference> for ConstructorKey {
    fn from(reference: &MethodReference) -> Self {
        Self {
            owner: reference.owner.clone(),
            descriptor: reference.descriptor.clone(),
        }
    }
}

impl From<&MethodReference> for MethodSymbolKey {
    fn from(reference: &MethodReference) -> Self {
        Self {
            owner: reference.owner.clone(),
            name: JavaIdentifier::from_dex(&reference.name),
            descriptor: reference.descriptor.clone(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct JavaMemberNames {
    fields: BTreeMap<FieldSymbolKey, JavaIdentifier>,
    methods: BTreeMap<MethodSymbolKey, JavaIdentifier>,
    overloads: BTreeMap<MethodOverloadKey, BTreeSet<MethodDescriptor>>,
    constructors: BTreeMap<ConstructorKey, ConstructorSourceLayout>,
}

#[derive(Debug, Clone, Default)]
struct ConstructorSourceLayout {
    hidden_parameters: BTreeSet<usize>,
    enclosing_parameter: Option<usize>,
}

impl JavaMemberNames {
    pub fn allocate(
        fields: impl IntoIterator<Item = JavaFieldSymbol>,
        methods: impl IntoIterator<Item = JavaMethodSymbol>,
    ) -> Self {
        let fields = fields.into_iter().collect::<BTreeSet<_>>();
        let methods = methods.into_iter().collect::<BTreeSet<_>>();
        let method_names = MethodNameAllocation::new(&methods).allocate(methods.clone());
        let mut overloads = BTreeMap::<MethodOverloadKey, BTreeSet<MethodDescriptor>>::new();
        for method in &methods {
            let name = method_names
                .get(&method.key())
                .cloned()
                .unwrap_or_else(|| method.name.clone());
            overloads
                .entry(MethodOverloadKey {
                    owner: method.owner.clone(),
                    name,
                    arity: method.descriptor.parameters.len(),
                })
                .or_default()
                .insert(method.descriptor.clone());
        }
        Self {
            fields: FieldNameAllocation::new(&fields).allocate(fields),
            methods: method_names,
            overloads,
            constructors: BTreeMap::new(),
        }
    }

    pub fn with_constructor_layouts(
        mut self,
        layouts: impl IntoIterator<Item = JavaConstructorLayout>,
    ) -> Self {
        for layout in layouts {
            self.overloads
                .entry(MethodOverloadKey {
                    owner: layout.owner.clone(),
                    name: JavaIdentifier::from_dex("<init>"),
                    arity: layout.descriptor.parameters.len(),
                })
                .or_default()
                .insert(layout.descriptor.clone());
            self.constructors.insert(
                layout.key(),
                ConstructorSourceLayout {
                    hidden_parameters: layout.hidden_parameters,
                    enclosing_parameter: layout.enclosing_parameter,
                },
            );
        }
        self
    }

    pub fn with_overloads(mut self, methods: impl IntoIterator<Item = MethodReference>) -> Self {
        for method in methods {
            self.overloads
                .entry(MethodOverloadKey {
                    owner: method.owner.clone(),
                    name: self.method(&method),
                    arity: method.descriptor.parameters.len(),
                })
                .or_default()
                .insert(method.descriptor);
        }
        self
    }

    pub fn hidden_constructor_parameters(
        &self,
        reference: &MethodReference,
    ) -> Option<&BTreeSet<usize>> {
        self.constructors
            .get(&ConstructorKey::from(reference))
            .map(|layout| &layout.hidden_parameters)
    }

    pub fn enclosing_constructor_parameter(&self, reference: &MethodReference) -> Option<usize> {
        self.constructors
            .get(&ConstructorKey::from(reference))
            .and_then(|layout| layout.enclosing_parameter)
    }

    pub fn field(&self, reference: &FieldReference) -> JavaIdentifier {
        let key = FieldSymbolKey::from(reference);
        self.fields.get(&key).cloned().unwrap_or(key.name)
    }

    pub fn field_symbol(&self, symbol: &JavaFieldSymbol) -> JavaIdentifier {
        self.fields
            .get(&symbol.key())
            .cloned()
            .unwrap_or_else(|| symbol.name.clone())
    }

    pub fn field_names(&self, owner: &ArgType) -> BTreeSet<JavaIdentifier> {
        self.fields
            .iter()
            .filter(|(field, _)| &field.owner == owner)
            .map(|(_, name)| name.clone())
            .collect()
    }

    pub fn method(&self, reference: &MethodReference) -> JavaIdentifier {
        let key = MethodSymbolKey::from(reference);
        self.methods.get(&key).cloned().unwrap_or(key.name)
    }

    pub fn null_argument_requires_cast(
        &self,
        reference: &MethodReference,
        parameter: usize,
    ) -> bool {
        let expected = match reference.descriptor.parameters.get(parameter) {
            Some(expected) if expected.is_reference() => expected,
            _ => return false,
        };
        let key = MethodOverloadKey {
            owner: reference.owner.clone(),
            name: self.method(reference),
            arity: reference.descriptor.parameters.len(),
        };
        self.overloads.get(&key).is_some_and(|overloads| {
            overloads.iter().any(|descriptor| {
                descriptor != &reference.descriptor
                    && descriptor
                        .parameters
                        .get(parameter)
                        .is_some_and(|candidate| candidate != expected)
            })
        })
    }

    pub fn overloads(&self, reference: &MethodReference) -> Option<&BTreeSet<MethodDescriptor>> {
        self.overloads.get(&MethodOverloadKey {
            owner: reference.owner.clone(),
            name: self.method(reference),
            arity: reference.descriptor.parameters.len(),
        })
    }

    pub fn method_symbol(&self, symbol: &JavaMethodSymbol) -> JavaIdentifier {
        self.methods
            .get(&symbol.key())
            .cloned()
            .unwrap_or_else(|| symbol.name.clone())
    }
}

struct FieldNameAllocation {
    scopes: BTreeMap<ArgType, JavaNameScope>,
}

impl FieldNameAllocation {
    fn new(fields: &BTreeSet<JavaFieldSymbol>) -> Self {
        let mut scopes = BTreeMap::<ArgType, JavaNameScope>::new();
        for field in fields {
            scopes
                .entry(field.owner.clone())
                .or_default()
                .reserve(field.name.clone());
        }
        Self { scopes }
    }

    fn allocate(
        mut self,
        fields: BTreeSet<JavaFieldSymbol>,
    ) -> BTreeMap<FieldSymbolKey, JavaIdentifier> {
        let mut occurrences = BTreeMap::<(ArgType, JavaIdentifier), usize>::new();
        fields
            .into_iter()
            .map(|field| {
                let group = (field.owner.clone(), field.name.clone());
                let occurrence = occurrences.entry(group).or_default();
                let name = if *occurrence == 0 {
                    field.name.clone()
                } else {
                    self.scopes.entry(field.owner.clone()).or_default().claim(
                        JavaIdentifier::from_dex(&format!("{}${}", field.name, *occurrence + 1)),
                    )
                };
                *occurrence += 1;
                (field.key(), name)
            })
            .collect()
    }
}

struct MethodNameAllocation {
    scopes: BTreeMap<ArgType, JavaNameScope>,
}

impl MethodNameAllocation {
    fn new(methods: &BTreeSet<JavaMethodSymbol>) -> Self {
        let mut scopes = BTreeMap::<ArgType, JavaNameScope>::new();
        for method in methods {
            scopes
                .entry(method.owner.clone())
                .or_default()
                .reserve(method.name.clone());
        }
        Self { scopes }
    }

    fn allocate(
        mut self,
        methods: BTreeSet<JavaMethodSymbol>,
    ) -> BTreeMap<MethodSymbolKey, JavaIdentifier> {
        let mut occurrences = BTreeMap::<(ArgType, JavaIdentifier, Vec<ArgType>), usize>::new();
        methods
            .into_iter()
            .map(|method| {
                let signature = (
                    method.owner.clone(),
                    method.name.clone(),
                    method.descriptor.parameters.clone(),
                );
                let occurrence = occurrences.entry(signature).or_default();
                let name = if *occurrence == 0 {
                    method.name.clone()
                } else {
                    self.scopes.entry(method.owner.clone()).or_default().claim(
                        JavaIdentifier::from_dex(&format!("{}${}", method.name, *occurrence + 1)),
                    )
                };
                *occurrence += 1;
                (method.key(), name)
            })
            .collect()
    }
}
