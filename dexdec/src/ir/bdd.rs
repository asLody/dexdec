//! Method-local reduced ordered binary decision diagrams.
//!
//! Handles carry their arena identity, so control domains from independent
//! methods cannot be mixed accidentally. All externally supplied handles and
//! expression symbols are validated before graph operations are evaluated.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ir::bool_expr::{BoolExpr, BoolVariable};

static NEXT_CONTEXT: AtomicU64 = AtomicU64::new(1);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bdd {
    context: u64,
    node: usize,
}

impl Bdd {
    pub fn is_false(self) -> bool {
        self.node == 0
    }

    pub fn is_true(self) -> bool {
        self.node == 1
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BddError {
    UnknownVariable(BoolVariable),
    ForeignHandle,
    InvalidHandle(usize),
    MalformedEvaluation,
    ResourceLimit { resource: BddResource, limit: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BddResource {
    Nodes,
    CacheEntries,
    Operations,
}

impl fmt::Display for BddError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownVariable(variable) => {
                write!(formatter, "boolean domain does not contain {variable:?}")
            }
            Self::ForeignHandle => formatter.write_str("BDD handle belongs to a different context"),
            Self::InvalidHandle(node) => write!(formatter, "BDD node {node} does not exist"),
            Self::MalformedEvaluation => formatter.write_str("malformed BDD evaluation work stack"),
            Self::ResourceLimit { resource, limit } => {
                write!(
                    formatter,
                    "BDD {resource:?} resource limit {limit} exceeded"
                )
            }
        }
    }
}

impl std::error::Error for BddError {}

impl BddError {
    pub fn is_resource_limit(&self) -> bool {
        matches!(self, Self::ResourceLimit { .. })
    }
}

#[derive(Debug, Clone, Copy)]
struct Node {
    variable: usize,
    low: Bdd,
    high: Bdd,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum BinaryOp {
    And,
    Or,
}

struct Manager {
    context: u64,
    nodes: Vec<Node>,
    unique: HashMap<(usize, Bdd, Bdd), Bdd>,
    binary_cache: HashMap<(BinaryOp, Bdd, Bdd), Bdd>,
    not_cache: HashMap<Bdd, Bdd>,
    implication_cache: HashMap<(Bdd, Bdd), bool>,
    limits: BddLimits,
    operations_used: usize,
}

impl Manager {
    fn new(context: u64, limits: BddLimits) -> Self {
        let falsity = Bdd { context, node: 0 };
        let truth = Bdd { context, node: 1 };
        let terminal = Node {
            variable: usize::MAX,
            low: falsity,
            high: truth,
        };
        Self {
            context,
            nodes: vec![terminal, terminal],
            unique: HashMap::new(),
            binary_cache: HashMap::new(),
            not_cache: HashMap::from([(falsity, truth), (truth, falsity)]),
            implication_cache: HashMap::new(),
            limits,
            operations_used: 0,
        }
    }

    fn handle(&self, node: usize) -> Bdd {
        Bdd {
            context: self.context,
            node,
        }
    }

    fn validate(&self, value: Bdd) -> Result<Node, BddError> {
        if value.context != self.context {
            return Err(BddError::ForeignHandle);
        }
        self.nodes
            .get(value.node)
            .copied()
            .ok_or(BddError::InvalidHandle(value.node))
    }

    fn variable(&mut self, variable: usize) -> Result<Bdd, BddError> {
        self.node(variable, self.handle(0), self.handle(1))
    }

    fn node(&mut self, variable: usize, low: Bdd, high: Bdd) -> Result<Bdd, BddError> {
        self.validate(low)?;
        self.validate(high)?;
        if low == high {
            return Ok(low);
        }
        let key = (variable, low, high);
        if let Some(existing) = self.unique.get(&key) {
            return Ok(*existing);
        }
        if self.nodes.len() >= self.limits.nodes {
            return Err(BddError::ResourceLimit {
                resource: BddResource::Nodes,
                limit: self.limits.nodes,
            });
        }
        let id = self.handle(self.nodes.len());
        self.nodes.push(Node {
            variable,
            low,
            high,
        });
        self.unique.insert(key, id);
        Ok(id)
    }

    fn and(&mut self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        self.apply(BinaryOp::And, left, right)
    }

    fn or(&mut self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        self.apply(BinaryOp::Or, left, right)
    }

    fn apply(&mut self, operation: BinaryOp, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        self.validate(left)?;
        self.validate(right)?;
        let mut tasks = vec![ApplyTask::Visit(left, right)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ApplyTask::Visit(left, right) => {
                    let (left, right) = ordered(left, right);
                    if let Some(result) = self.terminal(operation, left, right) {
                        results.push(result);
                        continue;
                    }
                    let key = (operation, left, right);
                    if let Some(result) = self.binary_cache.get(&key) {
                        results.push(*result);
                        continue;
                    }
                    self.charge_operation()?;
                    let variable = self.top_variable(left, right)?;
                    let (left_low, left_high) = self.cofactors(left, variable)?;
                    let (right_low, right_high) = self.cofactors(right, variable)?;
                    tasks.push(ApplyTask::Combine { key, variable });
                    tasks.push(ApplyTask::Visit(left_high, right_high));
                    tasks.push(ApplyTask::Visit(left_low, right_low));
                }
                ApplyTask::Combine { key, variable } => {
                    let high = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let low = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let result = self.node(variable, low, high)?;
                    self.reserve_cache_entries(if self.binary_cache.contains_key(&key) {
                        0
                    } else {
                        1
                    })?;
                    self.binary_cache.insert(key, result);
                    results.push(result);
                }
            }
        }
        if results.len() != 1 {
            return Err(BddError::MalformedEvaluation);
        }
        results.pop().ok_or(BddError::MalformedEvaluation)
    }

    fn negate(&mut self, value: Bdd) -> Result<Bdd, BddError> {
        self.validate(value)?;
        if let Some(result) = self.not_cache.get(&value) {
            return Ok(*result);
        }
        let mut tasks = vec![NotTask::Visit(value)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                NotTask::Visit(value) => {
                    if let Some(result) = self.not_cache.get(&value) {
                        results.push(*result);
                        continue;
                    }
                    self.charge_operation()?;
                    let node = self.validate(value)?;
                    tasks.push(NotTask::Combine {
                        value,
                        variable: node.variable,
                    });
                    tasks.push(NotTask::Visit(node.high));
                    tasks.push(NotTask::Visit(node.low));
                }
                NotTask::Combine { value, variable } => {
                    let high = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let low = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let result = self.node(variable, low, high)?;
                    let additional = (if self.not_cache.contains_key(&value) {
                        0
                    } else {
                        1
                    }) + (if self.not_cache.contains_key(&result) {
                        0
                    } else {
                        1
                    });
                    self.reserve_cache_entries(additional)?;
                    self.not_cache.insert(value, result);
                    self.not_cache.insert(result, value);
                    results.push(result);
                }
            }
        }
        if results.len() != 1 {
            return Err(BddError::MalformedEvaluation);
        }
        results.pop().ok_or(BddError::MalformedEvaluation)
    }

    fn restrict(
        &mut self,
        value: Bdd,
        assignments: &BTreeMap<usize, bool>,
    ) -> Result<Bdd, BddError> {
        self.validate(value)?;
        let mut tasks = vec![RestrictTask::Visit(value)];
        let mut results = Vec::new();
        let mut memo = BTreeMap::<Bdd, Bdd>::new();
        while let Some(task) = tasks.pop() {
            match task {
                RestrictTask::Visit(value) => {
                    if let Some(result) = memo.get(&value) {
                        results.push(*result);
                        continue;
                    }
                    if value.is_false() || value.is_true() {
                        memo.insert(value, value);
                        results.push(value);
                        continue;
                    }
                    self.charge_operation()?;
                    let node = self.validate(value)?;
                    if let Some(high) = assignments.get(&node.variable) {
                        tasks.push(RestrictTask::Alias(value));
                        tasks.push(RestrictTask::Visit(if *high {
                            node.high
                        } else {
                            node.low
                        }));
                    } else {
                        tasks.push(RestrictTask::Combine {
                            value,
                            variable: node.variable,
                        });
                        tasks.push(RestrictTask::Visit(node.high));
                        tasks.push(RestrictTask::Visit(node.low));
                    }
                }
                RestrictTask::Alias(value) => {
                    let result = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    memo.insert(value, result);
                    results.push(result);
                }
                RestrictTask::Combine { value, variable } => {
                    let high = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let low = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let result = self.node(variable, low, high)?;
                    memo.insert(value, result);
                    results.push(result);
                }
            }
        }
        if results.len() != 1 {
            return Err(BddError::MalformedEvaluation);
        }
        results.pop().ok_or(BddError::MalformedEvaluation)
    }

    fn exists(&mut self, value: Bdd, variables: &BTreeSet<usize>) -> Result<Bdd, BddError> {
        self.validate(value)?;
        let mut tasks = vec![ExistsTask::Visit(value)];
        let mut results = Vec::new();
        let mut memo = BTreeMap::<Bdd, Bdd>::new();
        while let Some(task) = tasks.pop() {
            match task {
                ExistsTask::Visit(value) => {
                    if let Some(result) = memo.get(&value) {
                        results.push(*result);
                        continue;
                    }
                    if value.is_false() || value.is_true() {
                        memo.insert(value, value);
                        results.push(value);
                        continue;
                    }
                    self.charge_operation()?;
                    let node = self.validate(value)?;
                    tasks.push(ExistsTask::Combine {
                        value,
                        variable: node.variable,
                        quantified: variables.contains(&node.variable),
                    });
                    tasks.push(ExistsTask::Visit(node.high));
                    tasks.push(ExistsTask::Visit(node.low));
                }
                ExistsTask::Combine {
                    value,
                    variable,
                    quantified,
                } => {
                    let high = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let low = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let result = if quantified {
                        self.or(low, high)?
                    } else {
                        self.node(variable, low, high)?
                    };
                    memo.insert(value, result);
                    results.push(result);
                }
            }
        }
        if results.len() != 1 {
            return Err(BddError::MalformedEvaluation);
        }
        results.pop().ok_or(BddError::MalformedEvaluation)
    }

    fn constrain(&mut self, value: Bdd, care: Bdd) -> Result<Bdd, BddError> {
        self.validate(value)?;
        self.validate(care)?;
        let mut tasks = vec![ConstrainTask::Visit(value, care)];
        let mut results = Vec::new();
        let mut memo = BTreeMap::<(Bdd, Bdd), Bdd>::new();
        while let Some(task) = tasks.pop() {
            match task {
                ConstrainTask::Visit(value, care) => {
                    if let Some(result) = memo.get(&(value, care)) {
                        results.push(*result);
                        continue;
                    }
                    if care.is_false() {
                        results.push(self.handle(0));
                        continue;
                    }
                    if care.is_true() || value.is_false() || value.is_true() {
                        memo.insert((value, care), value);
                        results.push(value);
                        continue;
                    }
                    self.charge_operation()?;
                    let variable = self.top_variable(value, care)?;
                    let (value_low, value_high) = self.cofactors(value, variable)?;
                    let (care_low, care_high) = self.cofactors(care, variable)?;
                    if care_low.is_false() {
                        tasks.push(ConstrainTask::Alias(value, care));
                        tasks.push(ConstrainTask::Visit(value_high, care_high));
                    } else if care_high.is_false() {
                        tasks.push(ConstrainTask::Alias(value, care));
                        tasks.push(ConstrainTask::Visit(value_low, care_low));
                    } else {
                        tasks.push(ConstrainTask::Combine {
                            value,
                            care,
                            variable,
                        });
                        tasks.push(ConstrainTask::Visit(value_high, care_high));
                        tasks.push(ConstrainTask::Visit(value_low, care_low));
                    }
                }
                ConstrainTask::Alias(value, care) => {
                    let result = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    memo.insert((value, care), result);
                    results.push(result);
                }
                ConstrainTask::Combine {
                    value,
                    care,
                    variable,
                } => {
                    let high = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let low = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let result = self.node(variable, low, high)?;
                    memo.insert((value, care), result);
                    results.push(result);
                }
            }
        }
        if results.len() != 1 {
            return Err(BddError::MalformedEvaluation);
        }
        results.pop().ok_or(BddError::MalformedEvaluation)
    }

    fn implies(&mut self, premise: Bdd, consequence: Bdd) -> Result<bool, BddError> {
        self.validate(premise)?;
        self.validate(consequence)?;
        if let Some(result) = self.implication_cache.get(&(premise, consequence)) {
            return Ok(*result);
        }
        let mut pending = vec![(premise, consequence)];
        let mut visited = BTreeSet::new();
        let mut result = true;
        while let Some((premise, consequence)) = pending.pop() {
            if premise.is_false() || consequence.is_true() || premise == consequence {
                continue;
            }
            if premise.is_true() || consequence.is_false() {
                result = false;
                break;
            }
            if !visited.insert((premise, consequence)) {
                continue;
            }
            self.charge_operation()?;
            let variable = self.top_variable(premise, consequence)?;
            let (premise_low, premise_high) = self.cofactors(premise, variable)?;
            let (consequence_low, consequence_high) = self.cofactors(consequence, variable)?;
            pending.push((premise_low, consequence_low));
            pending.push((premise_high, consequence_high));
        }
        self.reserve_cache_entries(usize::from(
            !self.implication_cache.contains_key(&(premise, consequence)),
        ))?;
        self.implication_cache
            .insert((premise, consequence), result);
        Ok(result)
    }

    fn terminal(&self, operation: BinaryOp, left: Bdd, right: Bdd) -> Option<Bdd> {
        match operation {
            BinaryOp::And if left.is_false() || right.is_false() => Some(self.handle(0)),
            BinaryOp::And if left.is_true() => Some(right),
            BinaryOp::And if right.is_true() || left == right => Some(left),
            BinaryOp::Or if left.is_true() || right.is_true() => Some(self.handle(1)),
            BinaryOp::Or if left.is_false() => Some(right),
            BinaryOp::Or if right.is_false() || left == right => Some(left),
            _ => None,
        }
    }

    fn top_variable(&self, left: Bdd, right: Bdd) -> Result<usize, BddError> {
        Ok(self.variable_of(left)?.min(self.variable_of(right)?))
    }

    fn variable_of(&self, value: Bdd) -> Result<usize, BddError> {
        Ok(self.validate(value)?.variable)
    }

    fn cofactors(&self, value: Bdd, variable: usize) -> Result<(Bdd, Bdd), BddError> {
        let node = self.validate(value)?;
        Ok(if node.variable == variable {
            (node.low, node.high)
        } else {
            (value, value)
        })
    }

    fn reserve_cache_entries(&self, additional: usize) -> Result<(), BddError> {
        let entries = self
            .binary_cache
            .len()
            .saturating_add(self.not_cache.len())
            .saturating_add(self.implication_cache.len());
        if entries.saturating_add(additional) > self.limits.cache_entries {
            return Err(BddError::ResourceLimit {
                resource: BddResource::CacheEntries,
                limit: self.limits.cache_entries,
            });
        }
        Ok(())
    }

    fn charge_operation(&mut self) -> Result<(), BddError> {
        if self.operations_used >= self.limits.operations {
            return Err(BddError::ResourceLimit {
                resource: BddResource::Operations,
                limit: self.limits.operations,
            });
        }
        self.operations_used += 1;
        Ok(())
    }

    fn begin_operation(&mut self) {
        self.operations_used = 0;
    }
}

enum ApplyTask {
    Visit(Bdd, Bdd),
    Combine {
        key: (BinaryOp, Bdd, Bdd),
        variable: usize,
    },
}

enum NotTask {
    Visit(Bdd),
    Combine { value: Bdd, variable: usize },
}

enum RestrictTask {
    Visit(Bdd),
    Alias(Bdd),
    Combine { value: Bdd, variable: usize },
}

enum ConstrainTask {
    Visit(Bdd, Bdd),
    Alias(Bdd, Bdd),
    Combine {
        value: Bdd,
        care: Bdd,
        variable: usize,
    },
}

enum ExistsTask {
    Visit(Bdd),
    Combine {
        value: Bdd,
        variable: usize,
        quantified: bool,
    },
}

type Cube = BTreeMap<BoolVariable, bool>;

struct DnfBuilder {
    cube_limit: usize,
}

impl DnfBuilder {
    fn new(cube_limit: usize) -> Self {
        Self { cube_limit }
    }

    fn build(&self, expression: &BoolExpr) -> Option<Vec<Cube>> {
        self.visit(expression, false, 0)
    }

    fn visit(&self, expression: &BoolExpr, negated: bool, depth: usize) -> Option<Vec<Cube>> {
        if depth > 128 {
            return None;
        }
        match expression {
            BoolExpr::True => Some(if negated {
                Vec::new()
            } else {
                vec![Cube::new()]
            }),
            BoolExpr::False => Some(if negated {
                vec![Cube::new()]
            } else {
                Vec::new()
            }),
            BoolExpr::Symbol(variable) => Some(vec![Cube::from([(variable.clone(), !negated)])]),
            BoolExpr::Not(inner) => self.visit(inner, !negated, depth + 1),
            BoolExpr::And(terms) | BoolExpr::Or(terms) => {
                let conjunction = matches!(expression, BoolExpr::And(_)) != negated;
                if conjunction {
                    self.conjunction(terms, negated, depth + 1)
                } else {
                    self.disjunction(terms, negated, depth + 1)
                }
            }
        }
    }

    fn conjunction(&self, terms: &[BoolExpr], negated: bool, depth: usize) -> Option<Vec<Cube>> {
        let mut product = vec![Cube::new()];
        for term in terms {
            let factor = self.visit(term, negated, depth)?;
            let mut next = Vec::new();
            for left in &product {
                for right in &factor {
                    if let Some(cube) = Self::merge(left, right) {
                        next.push(cube);
                        if next.len() > self.cube_limit {
                            return None;
                        }
                    }
                }
            }
            product = next;
            if product.is_empty() {
                break;
            }
        }
        Some(product)
    }

    fn disjunction(&self, terms: &[BoolExpr], negated: bool, depth: usize) -> Option<Vec<Cube>> {
        let mut union = Vec::new();
        for term in terms {
            union.extend(self.visit(term, negated, depth)?);
            if union.len() > self.cube_limit {
                return None;
            }
        }
        Some(union)
    }

    fn merge(left: &Cube, right: &Cube) -> Option<Cube> {
        let mut merged = left.clone();
        for (variable, polarity) in right {
            match merged.get(variable) {
                Some(existing) if existing != polarity => return None,
                Some(_) => {}
                None => {
                    merged.insert(variable.clone(), *polarity);
                }
            }
        }
        Some(merged)
    }
}

fn ordered(left: Bdd, right: Bdd) -> (Bdd, Bdd) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

pub struct BddContext {
    context: u64,
    variables: BTreeMap<BoolVariable, usize>,
    variables_by_index: Vec<BoolVariable>,
    manager: RefCell<Manager>,
    expressions: RefCell<BTreeMap<BoolExpr, Bdd>>,
    limits: BddLimits,
}

#[derive(Debug, Clone, Copy)]
struct BddLimits {
    nodes: usize,
    cache_entries: usize,
    operations: usize,
}

impl BddLimits {
    fn for_variables(variables: usize) -> Self {
        let nodes = variables.max(1).saturating_mul(256).clamp(2_048, 65_536);
        Self {
            nodes,
            cache_entries: nodes.saturating_mul(4),
            operations: nodes.saturating_mul(8),
        }
    }
}

impl BddContext {
    pub fn new(names: &BTreeSet<BoolVariable>) -> Self {
        Self::ordered(names.iter().cloned())
    }

    pub fn ordered(names: impl IntoIterator<Item = BoolVariable>) -> Self {
        let context = NEXT_CONTEXT.fetch_add(1, Ordering::Relaxed);
        let mut variables = BTreeMap::new();
        let mut variables_by_index = Vec::new();
        for name in names {
            if variables.contains_key(&name) {
                continue;
            }
            let index = variables_by_index.len();
            variables.insert(name.clone(), index);
            variables_by_index.push(name);
        }
        let limits = BddLimits::for_variables(variables_by_index.len());
        Self {
            context,
            variables,
            variables_by_index,
            manager: RefCell::new(Manager::new(context, limits)),
            expressions: RefCell::new(BTreeMap::new()),
            limits,
        }
    }

    pub fn truth(&self) -> Bdd {
        Bdd {
            context: self.context,
            node: 1,
        }
    }

    pub fn falsity(&self) -> Bdd {
        Bdd {
            context: self.context,
            node: 0,
        }
    }

    pub fn and(&self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        let mut manager = self.manager.borrow_mut();
        manager.begin_operation();
        manager.and(left, right)
    }

    pub fn or(&self, left: Bdd, right: Bdd) -> Result<Bdd, BddError> {
        let mut manager = self.manager.borrow_mut();
        manager.begin_operation();
        manager.or(left, right)
    }

    pub fn not(&self, value: Bdd) -> Result<Bdd, BddError> {
        let mut manager = self.manager.borrow_mut();
        manager.begin_operation();
        manager.negate(value)
    }

    pub fn restrict(
        &self,
        value: Bdd,
        assignments: &BTreeMap<BoolVariable, bool>,
    ) -> Result<Bdd, BddError> {
        let assignments = assignments
            .iter()
            .map(|(variable, value)| {
                self.variables
                    .get(variable)
                    .copied()
                    .map(|index| (index, *value))
                    .ok_or_else(|| BddError::UnknownVariable(variable.clone()))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let mut manager = self.manager.borrow_mut();
        manager.begin_operation();
        manager.restrict(value, &assignments)
    }

    pub fn exists(&self, value: Bdd, variables: &BTreeSet<BoolVariable>) -> Result<Bdd, BddError> {
        let variables = variables
            .iter()
            .map(|variable| {
                self.variables
                    .get(variable)
                    .copied()
                    .ok_or_else(|| BddError::UnknownVariable(variable.clone()))
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let mut manager = self.manager.borrow_mut();
        manager.begin_operation();
        manager.exists(value, &variables)
    }

    pub fn constrain(&self, value: Bdd, care: Bdd) -> Result<Bdd, BddError> {
        let mut manager = self.manager.borrow_mut();
        manager.begin_operation();
        manager.constrain(value, care)
    }

    pub fn compile(&self, expression: &BoolExpr) -> Result<Bdd, BddError> {
        let mut tasks = vec![CompileTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CompileTask::Visit(expression) => {
                    if let Some(value) = self.expressions.borrow().get(expression) {
                        results.push(*value);
                        continue;
                    }
                    match expression {
                        BoolExpr::True => results.push(self.truth()),
                        BoolExpr::False => results.push(self.falsity()),
                        BoolExpr::Symbol(symbol) => {
                            let variable = self
                                .variables
                                .get(symbol)
                                .copied()
                                .ok_or_else(|| BddError::UnknownVariable(symbol.clone()))?;
                            let value = self.manager.borrow_mut().variable(variable)?;
                            self.record_expression(expression, value)?;
                            results.push(value);
                        }
                        BoolExpr::Not(inner) => {
                            tasks.push(CompileTask::Combine {
                                expression,
                                operation: CompileOp::Not,
                                operands: 1,
                            });
                            tasks.push(CompileTask::Visit(inner));
                        }
                        BoolExpr::And(terms) => {
                            tasks.push(CompileTask::Combine {
                                expression,
                                operation: CompileOp::And,
                                operands: terms.len(),
                            });
                            tasks.extend(terms.iter().rev().map(CompileTask::Visit));
                        }
                        BoolExpr::Or(terms) => {
                            tasks.push(CompileTask::Combine {
                                expression,
                                operation: CompileOp::Or,
                                operands: terms.len(),
                            });
                            tasks.extend(terms.iter().rev().map(CompileTask::Visit));
                        }
                    }
                }
                CompileTask::Combine {
                    expression,
                    operation,
                    operands,
                } => {
                    let start = results
                        .len()
                        .checked_sub(operands)
                        .ok_or(BddError::MalformedEvaluation)?;
                    let values = results.drain(start..).collect::<Vec<_>>();
                    let value = match operation {
                        CompileOp::Not => {
                            let [value] = values.as_slice() else {
                                return Err(BddError::MalformedEvaluation);
                            };
                            self.not(*value)?
                        }
                        CompileOp::And => values
                            .into_iter()
                            .try_fold(self.truth(), |left, right| self.and(left, right))?,
                        CompileOp::Or => values
                            .into_iter()
                            .try_fold(self.falsity(), |left, right| self.or(left, right))?,
                    };
                    self.record_expression(expression, value)?;
                    results.push(value);
                }
            }
        }
        if results.len() != 1 {
            return Err(BddError::MalformedEvaluation);
        }
        results.pop().ok_or(BddError::MalformedEvaluation)
    }

    pub fn are_equivalent(&self, left: &BoolExpr, right: &BoolExpr) -> Result<bool, BddError> {
        Ok(self.compile(left)? == self.compile(right)?)
    }

    pub fn implies(&self, premise: &BoolExpr, consequence: &BoolExpr) -> Result<bool, BddError> {
        let premise = self.compile(premise)?;
        let consequence = self.compile(consequence)?;
        self.implies_bdd(premise, consequence)
    }

    pub fn equivalent(&self, left: Bdd, right: Bdd) -> Result<bool, BddError> {
        self.manager.borrow().validate(left)?;
        self.manager.borrow().validate(right)?;
        Ok(left == right)
    }

    pub fn equivalent_under(&self, care: Bdd, left: Bdd, right: Bdd) -> Result<bool, BddError> {
        self.manager.borrow().validate(care)?;
        self.manager.borrow().validate(left)?;
        self.manager.borrow().validate(right)?;
        let difference = self.or(
            self.and(left, self.not(right)?)?,
            self.and(self.not(left)?, right)?,
        )?;
        Ok(self.and(care, difference)?.is_false())
    }

    pub fn reduce_under(
        &self,
        expression: &BoolExpr,
        care: Bdd,
        node_limit: usize,
    ) -> Result<Option<(BoolExpr, usize)>, BddError> {
        self.reduce_under_with_support(expression, care, &expression.symbols(), node_limit)
    }

    pub fn reduce_under_with_support(
        &self,
        expression: &BoolExpr,
        care: Bdd,
        support: &BTreeSet<BoolVariable>,
        node_limit: usize,
    ) -> Result<Option<(BoolExpr, usize)>, BddError> {
        self.manager.borrow().validate(care)?;
        if let Some(variable) = support
            .iter()
            .find(|variable| !self.variables.contains_key(*variable))
        {
            return Err(BddError::UnknownVariable(variable.clone()));
        }
        let hidden = self
            .variables
            .keys()
            .filter(|variable| !support.contains(*variable))
            .cloned()
            .collect::<BTreeSet<_>>();
        let care = if hidden.is_empty() {
            care
        } else {
            let projected = self.exists(care, &hidden)?;
            if let Some((projected_expression, _)) = self.expression(projected, 4096)? {
                let local = Self::new(support);
                let local_care = local.compile(&projected_expression)?;
                return local
                    .reduce_under_with_support(expression, local_care, support, node_limit);
            }
            projected
        };
        let value = self.compile(expression)?;
        let mut best = (expression.clone(), expression.node_count());
        let mut best_rank = (best.1, expression.symbols().len());

        let constrained = self.constrain(value, care)?;
        if let Some(candidate) = self.expression(constrained, node_limit)? {
            let rank = (candidate.1, candidate.0.symbols().len());
            if rank < best_rank && self.equivalent_under(care, value, constrained)? {
                best_rank = rank;
                best = candidate;
            }
        }
        if expression.node_count() >= 8 {
            if let Some(candidate) = self.implicant_cover(expression, care, value, node_limit)? {
                let rank = (candidate.node_count(), candidate.symbols().len());
                if rank <= best_rank {
                    best_rank = rank;
                    best = (candidate, rank.0);
                }
            }
        }
        let mut candidates = expression.subexpressions(256);
        candidates.extend([BoolExpr::False, BoolExpr::True]);
        let complements = candidates
            .iter()
            .cloned()
            .map(BoolExpr::not)
            .collect::<Vec<_>>();
        candidates.extend(complements);
        for candidate in candidates {
            let size = candidate.node_count();
            let rank = (size, candidate.symbols().len());
            if rank >= best_rank || size > node_limit {
                continue;
            }
            let candidate_value = self.compile(&candidate)?;
            if self.equivalent_under(care, value, candidate_value)? {
                best_rank = rank;
                best = (candidate, size);
            }
        }
        if expression.node_count() >= 8 || support.len() <= 16 {
            let candidate = match self.care_set_cover(care, value, support, node_limit) {
                Ok(candidate) => candidate,
                Err(error) if error.is_resource_limit() => None,
                Err(error) => return Err(error),
            };
            if let Some(candidate) = candidate {
                let rank = (candidate.node_count(), candidate.symbols().len());
                if rank <= best_rank {
                    best = (candidate, rank.0);
                }
            }
        }
        Ok((best.1 <= node_limit).then_some(best))
    }

    fn care_set_cover(
        &self,
        care: Bdd,
        value: Bdd,
        support: &BTreeSet<BoolVariable>,
        node_limit: usize,
    ) -> Result<Option<BoolExpr>, BddError> {
        const CUBE_LIMIT: usize = 256;
        const EXPANSION_LIMIT: usize = 2048;

        let on_set = self.and(care, value)?;
        if on_set.is_false() {
            return Ok(Some(BoolExpr::False));
        }
        let off_set = self.and(care, self.not(value)?)?;
        if off_set.is_false() {
            return Ok(Some(BoolExpr::True));
        }

        let expansion_limit = node_limit
            .saturating_mul(8)
            .max(node_limit)
            .min(EXPANSION_LIMIT);
        let Some((on_expression, _)) = self.expression(on_set, expansion_limit)? else {
            return Ok(None);
        };
        let Some(mut cubes) = DnfBuilder::new(CUBE_LIMIT).build(&on_expression) else {
            return Ok(None);
        };
        for variable in support {
            for polarity in [true, false] {
                let literal = BoolExpr::Symbol(variable.clone());
                let literal = if polarity {
                    literal
                } else {
                    BoolExpr::not(literal)
                };
                let literal_value = self.compile(&literal)?;
                if !self.and(on_set, literal_value)?.is_false()
                    && self.and(off_set, literal_value)?.is_false()
                {
                    cubes.push(Cube::from([(variable.clone(), polarity)]));
                }
            }
        }
        Self::absorb_cubes(&mut cubes);

        for cube in &mut cubes {
            let mut literals = cube.keys().cloned().collect::<Vec<_>>();
            literals.sort_by_key(|variable| (support.contains(variable), variable.clone()));
            for literal in literals {
                let Some(polarity) = cube.remove(&literal) else {
                    continue;
                };
                let candidate = self.compile(&Self::cube_expression(cube))?;
                if !self.and(candidate, off_set)?.is_false() {
                    cube.insert(literal, polarity);
                }
            }
        }
        cubes.retain(|cube| cube.keys().all(|variable| support.contains(variable)));
        Self::absorb_cubes(&mut cubes);
        self.absorb_cubes_under(&mut cubes, on_set)?;
        if cubes.is_empty() {
            return Ok(None);
        }

        let candidate = Self::factored_cover(&cubes, 0);
        if candidate.node_count() > node_limit {
            return Ok(None);
        }
        let candidate_value = self.compile(&candidate)?;
        Ok(self
            .equivalent_under(care, value, candidate_value)?
            .then_some(candidate))
    }

    fn absorb_cubes_under(&self, cubes: &mut Vec<Cube>, on_set: Bdd) -> Result<(), BddError> {
        cubes.sort_by(|left, right| {
            left.len()
                .cmp(&right.len())
                .then_with(|| left.iter().cmp(right.iter()))
        });
        let mut covered = self.falsity();
        let mut irredundant = Vec::new();
        for cube in std::mem::take(cubes) {
            let value = self.compile(&Self::cube_expression(&cube))?;
            let contribution = self.and(on_set, value)?;
            if contribution.is_false() || self.implies_bdd(contribution, covered)? {
                continue;
            }
            covered = self.or(covered, contribution)?;
            irredundant.push(cube);
        }
        *cubes = irredundant;
        Ok(())
    }

    fn implicant_cover(
        &self,
        expression: &BoolExpr,
        care: Bdd,
        value: Bdd,
        node_limit: usize,
    ) -> Result<Option<BoolExpr>, BddError> {
        const CUBE_LIMIT: usize = 64;
        let Some(mut cubes) = DnfBuilder::new(CUBE_LIMIT).build(expression) else {
            return Ok(None);
        };
        if cubes.is_empty() {
            return Ok(Some(BoolExpr::False));
        }
        Self::absorb_cubes(&mut cubes);
        for cube in &mut cubes {
            let literals = cube.keys().cloned().collect::<Vec<_>>();
            for literal in literals {
                let Some(polarity) = cube.remove(&literal) else {
                    continue;
                };
                let candidate = Self::cube_expression(cube);
                let candidate = self.compile(&candidate)?;
                let premise = self.and(care, candidate)?;
                if !self.implies_bdd(premise, value)? {
                    cube.insert(literal, polarity);
                }
            }
        }
        Self::absorb_cubes(&mut cubes);
        let candidate = Self::factored_cover(&cubes, 0);
        if candidate.node_count() > node_limit {
            return Ok(None);
        }
        let candidate_value = self.compile(&candidate)?;
        Ok(self
            .equivalent_under(care, value, candidate_value)?
            .then_some(candidate))
    }

    fn cube_expression(cube: &Cube) -> BoolExpr {
        let mut literals = cube.iter().collect::<Vec<_>>();
        literals.sort_by(
            |(left_variable, left_polarity), (right_variable, right_polarity)| {
                right_polarity
                    .cmp(left_polarity)
                    .then_with(|| left_variable.cmp(right_variable))
            },
        );
        BoolExpr::and(
            literals
                .into_iter()
                .map(|(variable, polarity)| {
                    let literal = BoolExpr::Symbol(variable.clone());
                    if *polarity {
                        literal
                    } else {
                        BoolExpr::not(literal)
                    }
                })
                .collect(),
        )
    }

    fn absorb_cubes(cubes: &mut Vec<Cube>) {
        cubes.sort_by(|left, right| {
            left.len()
                .cmp(&right.len())
                .then_with(|| left.iter().cmp(right.iter()))
        });
        let mut irredundant = Vec::<Cube>::new();
        for cube in std::mem::take(cubes) {
            if irredundant
                .iter()
                .any(|candidate| Self::cube_contains(&cube, candidate))
            {
                continue;
            }
            irredundant.push(cube);
        }
        *cubes = irredundant;
    }

    fn cube_contains(cube: &Cube, subset: &Cube) -> bool {
        subset
            .iter()
            .all(|(variable, polarity)| cube.get(variable) == Some(polarity))
    }

    fn factored_cover(cubes: &[Cube], depth: usize) -> BoolExpr {
        if cubes.is_empty() {
            return BoolExpr::False;
        }
        if cubes.iter().any(BTreeMap::is_empty) {
            return BoolExpr::True;
        }
        let flat = BoolExpr::or(cubes.iter().map(Self::cube_expression).collect());
        if cubes.len() < 2 || depth >= 32 {
            return flat;
        }

        let mut frequencies = BTreeMap::<(BoolVariable, bool), usize>::new();
        for cube in cubes {
            for (variable, polarity) in cube {
                *frequencies
                    .entry((variable.clone(), *polarity))
                    .or_default() += 1;
            }
        }
        let Some(((variable, polarity), count)) = frequencies
            .into_iter()
            .filter(|(_, count)| *count > 1)
            .max_by_key(|(_, count)| *count)
        else {
            return flat;
        };

        let mut containing = Vec::with_capacity(count);
        let mut remaining = Vec::with_capacity(cubes.len().saturating_sub(count));
        for cube in cubes {
            if cube.get(&variable) == Some(&polarity) {
                let mut reduced = cube.clone();
                reduced.remove(&variable);
                containing.push(reduced);
            } else {
                remaining.push(cube.clone());
            }
        }
        Self::absorb_cubes(&mut containing);
        Self::absorb_cubes(&mut remaining);
        let literal = BoolExpr::Symbol(variable);
        let literal = if polarity {
            literal
        } else {
            BoolExpr::not(literal)
        };
        let common = BoolExpr::and(vec![literal, Self::factored_cover(&containing, depth + 1)]);
        let factored = if remaining.is_empty() {
            common
        } else {
            BoolExpr::or(vec![Self::factored_cover(&remaining, depth + 1), common])
        };
        if factored.node_count() < flat.node_count() {
            factored
        } else {
            flat
        }
    }

    pub fn implies_bdd(&self, premise: Bdd, consequence: Bdd) -> Result<bool, BddError> {
        let mut manager = self.manager.borrow_mut();
        manager.begin_operation();
        manager.implies(premise, consequence)
    }

    pub fn expression(
        &self,
        value: Bdd,
        node_limit: usize,
    ) -> Result<Option<(BoolExpr, usize)>, BddError> {
        self.manager.borrow().validate(value)?;
        let mut pending = vec![ExpandTask::Visit(value)];
        let mut results = Vec::new();
        let mut memo = BTreeMap::<Bdd, (BoolExpr, usize)>::new();
        while let Some(task) = pending.pop() {
            match task {
                ExpandTask::Visit(value) => {
                    if let Some(result) = memo.get(&value) {
                        results.push(result.clone());
                        continue;
                    }
                    if value.is_false() {
                        if node_limit == 0 {
                            return Ok(None);
                        }
                        results.push((BoolExpr::False, 1));
                        continue;
                    }
                    if value.is_true() {
                        if node_limit == 0 {
                            return Ok(None);
                        }
                        results.push((BoolExpr::True, 1));
                        continue;
                    }
                    let node = self.manager.borrow().validate(value)?;
                    pending.push(ExpandTask::Build {
                        value,
                        variable: node.variable,
                    });
                    pending.push(ExpandTask::Visit(node.high));
                    pending.push(ExpandTask::Visit(node.low));
                }
                ExpandTask::Build { value, variable } => {
                    let (high, high_nodes) = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let (low, low_nodes) = results.pop().ok_or(BddError::MalformedEvaluation)?;
                    let symbol = BoolExpr::Symbol(
                        self.variables_by_index
                            .get(variable)
                            .cloned()
                            .ok_or(BddError::InvalidHandle(variable))?,
                    );
                    let (expression, nodes) = match (&low, &high) {
                        (BoolExpr::False, BoolExpr::True) => (symbol, 1),
                        (BoolExpr::True, BoolExpr::False) => (BoolExpr::not(symbol), 2),
                        (BoolExpr::False, _) => (
                            BoolExpr::and(vec![symbol, high]),
                            high_nodes.saturating_add(2),
                        ),
                        (_, BoolExpr::False) => (
                            BoolExpr::and(vec![BoolExpr::not(symbol), low]),
                            low_nodes.saturating_add(3),
                        ),
                        (BoolExpr::True, _) => (
                            BoolExpr::or(vec![BoolExpr::not(symbol), high]),
                            high_nodes.saturating_add(3),
                        ),
                        (_, BoolExpr::True) => {
                            (BoolExpr::or(vec![symbol, low]), low_nodes.saturating_add(2))
                        }
                        _ => (
                            BoolExpr::or(vec![
                                BoolExpr::and(vec![BoolExpr::not(symbol.clone()), low]),
                                BoolExpr::and(vec![symbol, high]),
                            ]),
                            low_nodes.saturating_add(high_nodes).saturating_add(6),
                        ),
                    };
                    if nodes > node_limit {
                        return Ok(None);
                    }
                    memo.insert(value, (expression.clone(), nodes));
                    results.push((expression, nodes));
                }
            }
        }
        if results.len() != 1 {
            return Err(BddError::MalformedEvaluation);
        }
        Ok(results.pop())
    }

    fn record_expression(&self, expression: &BoolExpr, value: Bdd) -> Result<(), BddError> {
        let mut expressions = self.expressions.borrow_mut();
        if !expressions.contains_key(expression) && expressions.len() >= self.limits.cache_entries {
            return Err(BddError::ResourceLimit {
                resource: BddResource::CacheEntries,
                limit: self.limits.cache_entries,
            });
        }
        expressions.insert(expression.clone(), value);
        Ok(())
    }
}

enum ExpandTask {
    Visit(Bdd),
    Build { value: Bdd, variable: usize },
}

enum CompileTask<'a> {
    Visit(&'a BoolExpr),
    Combine {
        expression: &'a BoolExpr,
        operation: CompileOp,
        operands: usize,
    },
}

#[derive(Clone, Copy)]
enum CompileOp {
    Not,
    And,
    Or,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(name: &str) -> BoolExpr {
        BoolExpr::symbol(name)
    }

    #[test]
    fn boolean_identities_share_canonical_handles() {
        let variables = ["a", "b"]
            .into_iter()
            .map(|name| BoolVariable::Named(name.to_string()))
            .collect();
        let context = BddContext::new(&variables);
        let a = sym("a");
        let b = sym("b");

        assert!(context.are_equivalent(&a, &a).unwrap());
        assert!(!context
            .are_equivalent(&a, &BoolExpr::not(a.clone()))
            .unwrap());
        assert!(context
            .are_equivalent(
                &BoolExpr::not(BoolExpr::and(vec![a.clone(), b.clone()])),
                &BoolExpr::or(vec![BoolExpr::not(a.clone()), BoolExpr::not(b.clone())]),
            )
            .unwrap());
        assert!(context
            .are_equivalent(
                &BoolExpr::or(vec![a.clone(), BoolExpr::and(vec![a.clone(), b.clone()])]),
                &a,
            )
            .unwrap());
    }

    #[test]
    fn existential_abstraction_forgets_quantified_variables() {
        let variables = ["a", "b"]
            .into_iter()
            .map(|name| BoolVariable::Named(name.to_string()))
            .collect();
        let context = BddContext::new(&variables);
        let a = sym("a");
        let b = sym("b");
        let conjunction = context.compile(&BoolExpr::and(vec![a.clone(), b])).unwrap();
        let quantified = context
            .exists(
                conjunction,
                &BTreeSet::from([BoolVariable::Named("b".to_string())]),
            )
            .unwrap();

        assert_eq!(quantified, context.compile(&a).unwrap());
    }

    #[test]
    fn care_set_reduction_uses_implied_subexpressions() {
        let variables = ["a", "b"]
            .into_iter()
            .map(|name| BoolVariable::Named(name.to_string()))
            .collect();
        let context = BddContext::new(&variables);
        let a = sym("a");
        let b = sym("b");
        let care = context
            .compile(&BoolExpr::or(vec![a.clone(), BoolExpr::not(b.clone())]))
            .unwrap();
        let original = BoolExpr::and(vec![a, b.clone()]);
        let (reduced, _) = context.reduce_under(&original, care, 32).unwrap().unwrap();

        assert_eq!(reduced, b);
    }

    #[test]
    fn implicant_cover_factors_mux_shaped_conditions() {
        let variables = ["c", "d", "f"]
            .into_iter()
            .map(|name| BoolVariable::Named(name.to_string()))
            .collect();
        let context = BddContext::new(&variables);
        let c = sym("c");
        let d = sym("d");
        let f = sym("f");
        let original = BoolExpr::or(vec![
            BoolExpr::and(vec![f.clone(), BoolExpr::or(vec![c.clone(), d.clone()])]),
            BoolExpr::and(vec![BoolExpr::not(f.clone()), d.clone()]),
        ]);
        let (reduced, _) = context
            .reduce_under(&original, context.truth(), 64)
            .unwrap()
            .unwrap();

        assert_eq!(reduced, BoolExpr::or(vec![d, BoolExpr::and(vec![c, f])]));
    }

    #[test]
    fn care_set_cover_can_use_an_equivalent_support_atom() {
        let variables = ["s0", "s1", "s2"]
            .into_iter()
            .map(|name| BoolVariable::Named(name.to_string()))
            .collect::<BTreeSet<_>>();
        let context = BddContext::new(&variables);
        let s0 = sym("s0");
        let s1 = sym("s1");
        let s2 = sym("s2");
        let care = context
            .compile(&BoolExpr::and(vec![
                BoolExpr::or(vec![s0.clone(), s1.clone(), s2.clone()]),
                BoolExpr::or(vec![BoolExpr::not(s0.clone()), BoolExpr::not(s1.clone())]),
                BoolExpr::or(vec![BoolExpr::not(s0.clone()), BoolExpr::not(s2.clone())]),
                BoolExpr::or(vec![BoolExpr::not(s1.clone()), BoolExpr::not(s2.clone())]),
            ]))
            .unwrap();
        let original = BoolExpr::and(vec![BoolExpr::not(s0), BoolExpr::not(s1)]);
        let (reduced, _) = context
            .reduce_under_with_support(&original, care, &variables, 32)
            .unwrap()
            .unwrap();

        assert_eq!(reduced, s2);
    }

    #[test]
    fn care_set_cover_recovers_a_finite_domain_tail() {
        let variables = ["l0", "l1", "l2", "l3", "l4", "l5", "p3", "q4", "q5"]
            .into_iter()
            .map(|name| BoolVariable::Named(name.to_string()))
            .collect::<BTreeSet<_>>();
        let context = BddContext::new(&variables);
        let labels = (0..=5)
            .map(|value| sym(&format!("l{value}")))
            .collect::<Vec<_>>();
        let mut theory = vec![BoolExpr::or(labels.clone())];
        for left in 0..labels.len() {
            for right in left + 1..labels.len() {
                theory.push(BoolExpr::or(vec![
                    BoolExpr::not(labels[left].clone()),
                    BoolExpr::not(labels[right].clone()),
                ]));
            }
        }
        let care = context.compile(&BoolExpr::and(theory)).unwrap();
        let original = BoolExpr::or(vec![
            BoolExpr::and(
                (0..=4)
                    .map(|value| BoolExpr::not(labels[value].clone()))
                    .collect(),
            ),
            BoolExpr::and(vec![
                sym("q5"),
                BoolExpr::or(vec![
                    BoolExpr::and(
                        (0..=3)
                            .map(|value| BoolExpr::not(labels[value].clone()))
                            .collect(),
                    ),
                    BoolExpr::and(vec![sym("q4"), sym("p3")]),
                ]),
            ]),
        ]);
        let (reduced, _) = context
            .reduce_under_with_support(&original, care, &variables, 128)
            .unwrap()
            .unwrap();

        assert_eq!(
            reduced,
            BoolExpr::or(vec![
                sym("l5"),
                BoolExpr::and(vec![sym("l4"), sym("q5")]),
                BoolExpr::and(vec![sym("p3"), sym("q4"), sym("q5")]),
            ])
        );
    }
}
