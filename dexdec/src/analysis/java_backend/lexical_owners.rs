use std::collections::{BTreeMap, BTreeSet};

use crate::language::java::{
    JavaAnonymousClassBody, JavaAstRewriter, JavaClassName, JavaClassType, JavaClassTypeSegment,
    JavaExpr, JavaIdentifier, JavaMethodDeclarationKind, JavaModifier, JavaStmt, JavaType,
    JavaTypeDeclaration,
};

/// Makes references to enclosing declarations immune to inherited member-type
/// shadowing while retaining short names for unrelated types.
pub(super) struct LexicalOwners;

impl LexicalOwners {
    pub(super) fn recover_outer_aliases(
        root: &mut JavaTypeDeclaration,
        known: impl IntoIterator<Item = (JavaType, JavaIdentifier, JavaType)>,
    ) {
        let mut aliases = known
            .into_iter()
            .map(|(owner, field, outer)| (LexicalField::new(&owner, field), outer.into_raw()))
            .collect::<BTreeMap<_, _>>();
        let root_path = vec![root.name.clone()];
        Self::collect_aliases(root, root_path.clone(), true, &mut aliases);
        Self::rewrite_aliases(root, root_path, true, &aliases);
    }

    pub(super) fn qualify(root: &mut JavaTypeDeclaration) {
        Self::declaration(root, &mut Vec::new());
    }

    fn declaration(declaration: &mut JavaTypeDeclaration, path: &mut Vec<JavaIdentifier>) {
        path.push(declaration.name.clone());
        let mut qualifier = EnclosingOwnerQualifier { path };
        for field in &mut declaration.fields {
            field.initializer = field
                .initializer
                .take()
                .map(|value| qualifier.rewrite_expression(value));
        }
        for method in &mut declaration.methods {
            if let Some(body) = &mut method.body {
                qualifier.rewrite_body(body);
            }
        }
        for nested in &mut declaration.nested {
            Self::declaration(nested, path);
        }
        path.pop();
    }

    fn collect_aliases(
        declaration: &mut JavaTypeDeclaration,
        owner_path: Vec<JavaIdentifier>,
        root: bool,
        aliases: &mut BTreeMap<LexicalField, JavaType>,
    ) {
        let owner = source_type(&owner_path);
        aliases.extend(LexicalAliasAnalysis::analyze(declaration, &owner));
        for nested in &mut declaration.nested {
            let mut nested_path = if root { Vec::new() } else { owner_path.clone() };
            nested_path.push(nested.name.clone());
            Self::collect_aliases(nested, nested_path, false, aliases);
        }
    }

    fn rewrite_aliases(
        declaration: &mut JavaTypeDeclaration,
        owner_path: Vec<JavaIdentifier>,
        root: bool,
        aliases: &BTreeMap<LexicalField, JavaType>,
    ) {
        let owner = source_type(&owner_path);
        let owner_key = owner.clone().into_raw().to_string();
        let owned = aliases
            .keys()
            .filter(|field| field.owner == owner_key)
            .map(|field| field.name.clone())
            .collect::<BTreeSet<_>>();
        declaration
            .fields
            .retain(|field| !owned.contains(&field.name));
        for method in &mut declaration.methods {
            if let Some(body) = &mut method.body {
                AliasStoreRemoval {
                    owner: &owner,
                    aliases,
                }
                .rewrite_body(body);
                AliasLoadRewriter {
                    owner: &owner,
                    aliases,
                }
                .rewrite_body(body);
            }
        }
        for nested in &mut declaration.nested {
            let mut nested_path = if root { Vec::new() } else { owner_path.clone() };
            nested_path.push(nested.name.clone());
            Self::rewrite_aliases(nested, nested_path, false, aliases);
        }
    }
}

fn source_type(path: &[JavaIdentifier]) -> JavaType {
    JavaType::Class(JavaClassType::raw(JavaClassName::from_identifiers(
        path.iter().cloned(),
    )))
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct LexicalField {
    owner: String,
    name: JavaIdentifier,
}

impl LexicalField {
    fn new(owner: &JavaType, name: JavaIdentifier) -> Self {
        Self {
            owner: owner.clone().into_raw().to_string(),
            name,
        }
    }
}

struct LexicalAliasAnalysis;

impl LexicalAliasAnalysis {
    fn analyze(
        declaration: &mut JavaTypeDeclaration,
        owner: &JavaType,
    ) -> BTreeMap<LexicalField, JavaType> {
        let candidates = declaration
            .fields
            .iter()
            .filter(|field| {
                field.initializer.is_none() && field.modifiers.contains(&JavaModifier::Final)
            })
            .map(|field| (field.name.clone(), field.ty.clone().into_raw()))
            .collect::<BTreeMap<_, _>>();
        if candidates.is_empty() {
            return BTreeMap::new();
        }

        let mut constructor_count = 0usize;
        let mut assignments = candidates
            .keys()
            .cloned()
            .map(|name| (name, Vec::new()))
            .collect::<BTreeMap<_, Vec<Option<JavaType>>>>();
        let mut invalid = BTreeSet::new();
        for method in &mut declaration.methods {
            let mut writes = AliasWriteCollector::default();
            if let Some(body) = &mut method.body {
                writes.rewrite_body(body);
            }
            let constructor = method.kind == JavaMethodDeclarationKind::Constructor;
            constructor_count += usize::from(constructor);
            for name in candidates.keys() {
                let field_writes = writes.fields.remove(name).unwrap_or_default();
                if constructor && field_writes.len() == 1 {
                    assignments
                        .get_mut(name)
                        .expect("candidate assignment inventory")
                        .push(field_writes[0].clone());
                } else if (constructor && field_writes.len() != 1)
                    || (!constructor && !field_writes.is_empty())
                {
                    invalid.insert(name.clone());
                }
            }
        }
        if constructor_count == 0 {
            return BTreeMap::new();
        }

        candidates
            .into_iter()
            .filter_map(|(name, field_type)| {
                if invalid.contains(&name) {
                    return None;
                }
                let values = assignments.remove(&name)?;
                let outer = values.first()?.clone()?;
                (values.len() == constructor_count
                    && values.iter().all(|value| value.as_ref() == Some(&outer))
                    && field_type == outer.clone().into_raw())
                .then(|| (LexicalField::new(owner, name), outer))
            })
            .collect()
    }
}

#[derive(Default)]
struct AliasWriteCollector {
    fields: BTreeMap<JavaIdentifier, Vec<Option<JavaType>>>,
}

impl AliasWriteCollector {
    fn record(&mut self, target: &JavaExpr, value: &JavaExpr) {
        let JavaExpr::Field { owner, name } = target else {
            return;
        };
        if !matches!(owner.as_ref(), JavaExpr::This) {
            return;
        }
        let outer = match value {
            JavaExpr::QualifiedThis(outer) => Some(outer.clone().into_raw()),
            _ => None,
        };
        self.fields.entry(name.clone()).or_default().push(outer);
    }
}

impl JavaAstRewriter for AliasWriteCollector {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        if let JavaStmt::Assign { target, value, .. } = &statement {
            self.record(target, value);
        }
        statement
    }

    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        if let JavaExpr::Assignment { target, value, .. } = &expression {
            self.record(target, value);
        }
        expression
    }

    fn rewrite_anonymous_body(&mut self, _body: &mut JavaAnonymousClassBody) {}
}

struct AliasStoreRemoval<'a> {
    owner: &'a JavaType,
    aliases: &'a BTreeMap<LexicalField, JavaType>,
}

impl AliasStoreRemoval<'_> {
    fn is_alias_store(&self, target: &JavaExpr, value: &JavaExpr) -> bool {
        let JavaExpr::Field { owner, name } = target else {
            return false;
        };
        if !matches!(owner.as_ref(), JavaExpr::This) {
            return false;
        }
        let Some(outer) = self
            .aliases
            .get(&LexicalField::new(self.owner, name.clone()))
        else {
            return false;
        };
        matches!(value, JavaExpr::QualifiedThis(value) if value.clone().into_raw() == *outer)
    }
}

impl JavaAstRewriter for AliasStoreRemoval<'_> {
    fn finish_statement(&mut self, statement: JavaStmt) -> JavaStmt {
        let JavaStmt::Assign { target, value, .. } = &statement else {
            return statement;
        };
        if self.is_alias_store(target, value) {
            JavaStmt::Empty
        } else {
            statement
        }
    }

    fn rewrite_anonymous_body(&mut self, _body: &mut JavaAnonymousClassBody) {}
}

struct AliasLoadRewriter<'a> {
    owner: &'a JavaType,
    aliases: &'a BTreeMap<LexicalField, JavaType>,
}

impl JavaAstRewriter for AliasLoadRewriter<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        let JavaExpr::Field { owner, name } = expression else {
            return expression;
        };
        let field_owner = match owner.as_ref() {
            JavaExpr::This => self.owner,
            JavaExpr::QualifiedThis(owner) => owner,
            _ => return JavaExpr::Field { owner, name },
        };
        self.aliases
            .get(&LexicalField::new(field_owner, name.clone()))
            .cloned()
            .map(JavaExpr::QualifiedThis)
            .unwrap_or(JavaExpr::Field { owner, name })
    }

    fn rewrite_anonymous_body(&mut self, _body: &mut JavaAnonymousClassBody) {}
}

struct EnclosingOwnerQualifier<'a> {
    path: &'a [JavaIdentifier],
}

impl EnclosingOwnerQualifier<'_> {
    fn owner(&self, owner: JavaType) -> JavaType {
        let JavaType::Class(class) = owner else {
            return owner;
        };
        let [segment] = class.segments.as_slice() else {
            return JavaType::Class(class);
        };
        let Some(index) = self.path.iter().rposition(|name| name == &segment.name) else {
            return JavaType::Class(class);
        };
        let arguments = segment.arguments.clone();
        JavaType::Class(JavaClassType {
            segments: self
                .path
                .iter()
                .take(index + 1)
                .enumerate()
                .map(|(position, name)| JavaClassTypeSegment {
                    name: name.clone(),
                    arguments: (position == index)
                        .then(|| arguments.clone())
                        .unwrap_or_default(),
                })
                .collect(),
        })
    }
}

impl JavaAstRewriter for EnclosingOwnerQualifier<'_> {
    fn finish_expression(&mut self, expression: JavaExpr) -> JavaExpr {
        match expression {
            JavaExpr::Call {
                receiver,
                owner: Some(owner),
                type_arguments,
                method,
                args,
            } => JavaExpr::Call {
                receiver,
                owner: Some(self.owner(owner)),
                type_arguments,
                method,
                args,
            },
            JavaExpr::StaticField { owner, name } => JavaExpr::StaticField {
                owner: self.owner(owner),
                name,
            },
            expression => expression,
        }
    }
}
