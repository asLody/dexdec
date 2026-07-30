//! Bounded proof domain for value availability.
//!
//! Control formulas are retained as a hash-consed Boolean DAG. ROBDD handles
//! are attached while the method-local proof budget permits exact implication.
//! Budget exhaustion makes subsequent proofs conservative without abandoning
//! value recovery or expanding formulas into trees.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::ir::bdd::{Bdd, BddContext, BddError};
use crate::ir::{BoolExpr, BoolVariable};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ControlDomain(u32);

#[derive(Debug, Clone)]
pub struct DomainError {
    kind: DomainFailure,
}

#[derive(Debug, Clone)]
enum DomainFailure {
    Invalid(ControlDomain),
    Capacity(usize),
    Boolean(BddError),
    MalformedEvaluation,
}

impl DomainError {
    fn invalid(domain: ControlDomain) -> Self {
        Self {
            kind: DomainFailure::Invalid(domain),
        }
    }

    fn capacity(capacity: usize) -> Self {
        Self {
            kind: DomainFailure::Capacity(capacity),
        }
    }

    fn malformed_evaluation() -> Self {
        Self {
            kind: DomainFailure::MalformedEvaluation,
        }
    }
}

impl fmt::Display for DomainError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            DomainFailure::Invalid(domain) => {
                write!(formatter, "invalid control domain {}", domain.0)
            }
            DomainFailure::Capacity(capacity) => {
                write!(formatter, "control-domain arena exceeds {capacity} nodes")
            }
            DomainFailure::Boolean(source) => write!(formatter, "Boolean proof failed: {source}"),
            DomainFailure::MalformedEvaluation => {
                formatter.write_str("malformed control-domain evaluation stack")
            }
        }
    }
}

impl std::error::Error for DomainError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.kind {
            DomainFailure::Boolean(source) => Some(source),
            _ => None,
        }
    }
}

impl From<BddError> for DomainError {
    fn from(source: BddError) -> Self {
        Self {
            kind: DomainFailure::Boolean(source),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum DomainNode {
    True,
    False,
    Symbol(BoolVariable),
    Not(ControlDomain),
    And(Vec<ControlDomain>),
    Or(Vec<ControlDomain>),
}

pub(super) struct DomainLogic {
    bdd: BddContext,
    nodes: Vec<DomainNode>,
    domains: BTreeMap<DomainNode, ControlDomain>,
    exact: BTreeMap<ControlDomain, Bdd>,
    saturated: Cell<bool>,
}

impl DomainLogic {
    const TRUE: ControlDomain = ControlDomain(0);
    const FALSE: ControlDomain = ControlDomain(1);

    pub(super) fn new(variables: &BTreeSet<BoolVariable>) -> Self {
        let bdd = BddContext::new(variables);
        Self {
            exact: BTreeMap::from([(Self::TRUE, bdd.truth()), (Self::FALSE, bdd.falsity())]),
            nodes: vec![DomainNode::True, DomainNode::False],
            domains: BTreeMap::from([
                (DomainNode::True, Self::TRUE),
                (DomainNode::False, Self::FALSE),
            ]),
            bdd,
            saturated: Cell::new(false),
        }
    }

    pub(super) fn truth(&self) -> ControlDomain {
        Self::TRUE
    }

    pub(super) fn falsity(&self) -> ControlDomain {
        Self::FALSE
    }

    pub(super) fn compile(&mut self, expression: &BoolExpr) -> Result<ControlDomain, DomainError> {
        let mut pending = vec![CompileTask::Visit(expression)];
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                CompileTask::Visit(BoolExpr::True) => results.push(Self::TRUE),
                CompileTask::Visit(BoolExpr::False) => results.push(Self::FALSE),
                CompileTask::Visit(BoolExpr::Symbol(symbol)) => {
                    results.push(self.symbol(symbol.clone())?);
                }
                CompileTask::Visit(BoolExpr::Not(inner)) => {
                    pending.push(CompileTask::Not);
                    pending.push(CompileTask::Visit(inner));
                }
                CompileTask::Visit(BoolExpr::And(terms)) => {
                    pending.push(CompileTask::And(terms.len()));
                    pending.extend(terms.iter().rev().map(CompileTask::Visit));
                }
                CompileTask::Visit(BoolExpr::Or(terms)) => {
                    pending.push(CompileTask::Or(terms.len()));
                    pending.extend(terms.iter().rev().map(CompileTask::Visit));
                }
                CompileTask::Not => {
                    let value = results
                        .pop()
                        .ok_or_else(DomainError::malformed_evaluation)?;
                    results.push(self.not(value)?);
                }
                CompileTask::And(count) => {
                    let value = self.combine(&mut results, count, true)?;
                    results.push(value);
                }
                CompileTask::Or(count) => {
                    let value = self.combine(&mut results, count, false)?;
                    results.push(value);
                }
            }
        }
        if results.len() != 1 {
            return Err(DomainError::malformed_evaluation());
        }
        results.pop().ok_or_else(DomainError::malformed_evaluation)
    }

    pub(super) fn not(&mut self, domain: ControlDomain) -> Result<ControlDomain, DomainError> {
        let node = self.node(domain)?.clone();
        match node {
            DomainNode::True => Ok(Self::FALSE),
            DomainNode::False => Ok(Self::TRUE),
            DomainNode::Not(inner) => Ok(inner),
            _ => {
                let exact = match (self.saturated.get(), self.exact.get(&domain).copied()) {
                    (false, Some(value)) => self.proof(self.bdd.not(value))?,
                    _ => None,
                };
                self.intern(DomainNode::Not(domain), exact)
            }
        }
    }

    fn combine(
        &mut self,
        results: &mut Vec<ControlDomain>,
        count: usize,
        conjunction: bool,
    ) -> Result<ControlDomain, DomainError> {
        let start = results
            .len()
            .checked_sub(count)
            .ok_or_else(DomainError::malformed_evaluation)?;
        let values = results.drain(start..).collect::<Vec<_>>();
        let mut value = if conjunction { Self::TRUE } else { Self::FALSE };
        for operand in values {
            value = if conjunction {
                self.and(value, operand)?
            } else {
                self.or(value, operand)?
            };
        }
        Ok(value)
    }

    pub(super) fn and(
        &mut self,
        left: ControlDomain,
        right: ControlDomain,
    ) -> Result<ControlDomain, DomainError> {
        self.junction(left, right, true)
    }

    pub(super) fn or(
        &mut self,
        left: ControlDomain,
        right: ControlDomain,
    ) -> Result<ControlDomain, DomainError> {
        self.junction(left, right, false)
    }

    pub(super) fn equivalent(
        &self,
        left: ControlDomain,
        right: ControlDomain,
    ) -> Result<bool, DomainError> {
        if left == right {
            return Ok(true);
        }
        match (
            self.exact.get(&left).copied(),
            self.exact.get(&right).copied(),
        ) {
            (Some(left), Some(right)) => match self.bdd.equivalent(left, right) {
                Ok(result) => Ok(result),
                Err(error) if error.is_resource_limit() => {
                    self.saturated.set(true);
                    Ok(false)
                }
                Err(error) => Err(error.into()),
            },
            _ => Ok(false),
        }
    }

    pub(super) fn implies(
        &self,
        premise: ControlDomain,
        consequence: ControlDomain,
    ) -> Result<bool, DomainError> {
        if premise == consequence || consequence == Self::TRUE || premise == Self::FALSE {
            return Ok(true);
        }
        if matches!(self.node(premise)?, DomainNode::And(terms) if terms.contains(&consequence))
            || matches!(self.node(consequence)?, DomainNode::Or(terms) if terms.contains(&premise))
        {
            return Ok(true);
        }
        if self.saturated.get() {
            return Ok(false);
        }
        let (Some(premise), Some(consequence)) = (
            self.exact.get(&premise).copied(),
            self.exact.get(&consequence).copied(),
        ) else {
            return Ok(false);
        };
        match self.bdd.implies_bdd(premise, consequence) {
            Ok(result) => Ok(result),
            Err(error) if error.is_resource_limit() => {
                self.saturated.set(true);
                Ok(false)
            }
            Err(error) => Err(error.into()),
        }
    }

    pub(super) fn covered_by(
        &self,
        premise: ControlDomain,
        consequences: impl IntoIterator<Item = ControlDomain>,
    ) -> Result<bool, DomainError> {
        let Some(premise) = self.exact.get(&premise).copied() else {
            return Ok(false);
        };
        let mut covered = self.bdd.falsity();
        for consequence in consequences {
            let Some(consequence) = self.exact.get(&consequence).copied() else {
                return Ok(false);
            };
            covered = match self.bdd.or(covered, consequence) {
                Ok(value) => value,
                Err(error) if error.is_resource_limit() => {
                    self.saturated.set(true);
                    return Ok(false);
                }
                Err(error) => return Err(error.into()),
            };
        }
        match self.bdd.implies_bdd(premise, covered) {
            Ok(result) => Ok(result),
            Err(error) if error.is_resource_limit() => {
                self.saturated.set(true);
                Ok(false)
            }
            Err(error) => Err(error.into()),
        }
    }

    pub(super) fn disjoint(
        &self,
        left: ControlDomain,
        right: ControlDomain,
    ) -> Result<bool, DomainError> {
        if left == Self::FALSE || right == Self::FALSE {
            return Ok(true);
        }
        if self.saturated.get() {
            return Ok(false);
        }
        let (Some(left), Some(right)) = (
            self.exact.get(&left).copied(),
            self.exact.get(&right).copied(),
        ) else {
            return Ok(false);
        };
        match self.bdd.and(left, right) {
            Ok(intersection) => Ok(intersection.is_false()),
            Err(error) if error.is_resource_limit() => {
                self.saturated.set(true);
                Ok(false)
            }
            Err(error) => Err(error.into()),
        }
    }

    pub(super) fn expression_under(
        &self,
        value: ControlDomain,
        care: ControlDomain,
        node_limit: usize,
    ) -> Result<Option<BoolExpr>, DomainError> {
        if self.saturated.get() {
            return Ok(None);
        }
        let (Some(value), Some(care)) = (
            self.exact.get(&value).copied(),
            self.exact.get(&care).copied(),
        ) else {
            return Ok(None);
        };
        let constrained = match self.bdd.constrain(value, care) {
            Ok(value) => value,
            Err(error) if error.is_resource_limit() => {
                self.saturated.set(true);
                return Ok(None);
            }
            Err(error) => return Err(error.into()),
        };
        match self.bdd.expression(constrained, node_limit) {
            Ok(expression) => Ok(expression.map(|(expression, _)| expression)),
            Err(error) if error.is_resource_limit() => {
                self.saturated.set(true);
                Ok(None)
            }
            Err(error) => Err(error.into()),
        }
    }

    fn symbol(&mut self, symbol: BoolVariable) -> Result<ControlDomain, DomainError> {
        let node = DomainNode::Symbol(symbol.clone());
        if let Some(domain) = self.domains.get(&node).copied() {
            return Ok(domain);
        }
        let exact = if self.saturated.get() {
            None
        } else {
            self.proof(self.bdd.compile(&BoolExpr::Symbol(symbol)))?
        };
        self.intern(node, exact)
    }

    fn junction(
        &mut self,
        left: ControlDomain,
        right: ControlDomain,
        conjunction: bool,
    ) -> Result<ControlDomain, DomainError> {
        let absorbing = if conjunction { Self::FALSE } else { Self::TRUE };
        let identity = if conjunction { Self::TRUE } else { Self::FALSE };
        if left == absorbing || right == absorbing {
            return Ok(absorbing);
        }
        if left == identity {
            return Ok(right);
        }
        if right == identity || left == right {
            return Ok(left);
        }

        let mut terms = Vec::new();
        self.extend_terms(left, conjunction, &mut terms)?;
        self.extend_terms(right, conjunction, &mut terms)?;
        terms.sort();
        terms.dedup();
        for term in &terms {
            if let DomainNode::Not(inner) = self.node(*term)? {
                if terms.binary_search(inner).is_ok() {
                    return Ok(absorbing);
                }
            }
        }
        if terms.len() == 1 {
            return terms.pop().ok_or_else(DomainError::malformed_evaluation);
        }

        let node = if conjunction {
            DomainNode::And(terms)
        } else {
            DomainNode::Or(terms)
        };
        if let Some(domain) = self.domains.get(&node).copied() {
            return Ok(domain);
        }
        let operands = match &node {
            DomainNode::And(terms) | DomainNode::Or(terms) => terms,
            _ => return Err(DomainError::malformed_evaluation()),
        };
        let exact = self.junction_proof(operands, conjunction)?;
        self.intern(node, exact)
    }

    fn extend_terms(
        &self,
        domain: ControlDomain,
        conjunction: bool,
        terms: &mut Vec<ControlDomain>,
    ) -> Result<(), DomainError> {
        match (conjunction, self.node(domain)?) {
            (true, DomainNode::And(nested)) | (false, DomainNode::Or(nested)) => {
                terms.extend(nested.iter().copied());
            }
            _ => terms.push(domain),
        }
        Ok(())
    }

    fn junction_proof(
        &self,
        terms: &[ControlDomain],
        conjunction: bool,
    ) -> Result<Option<Bdd>, DomainError> {
        if self.saturated.get() {
            return Ok(None);
        }
        let mut value = if conjunction {
            self.bdd.truth()
        } else {
            self.bdd.falsity()
        };
        for term in terms {
            let Some(operand) = self.exact.get(term).copied() else {
                return Ok(None);
            };
            let result = if conjunction {
                self.bdd.and(value, operand)
            } else {
                self.bdd.or(value, operand)
            };
            let Some(exact) = self.proof(result)? else {
                return Ok(None);
            };
            value = exact;
        }
        Ok(Some(value))
    }

    fn node(&self, domain: ControlDomain) -> Result<&DomainNode, DomainError> {
        self.nodes
            .get(domain.0 as usize)
            .ok_or_else(|| DomainError::invalid(domain))
    }

    fn intern(
        &mut self,
        node: DomainNode,
        exact: Option<Bdd>,
    ) -> Result<ControlDomain, DomainError> {
        if let Some(domain) = self.domains.get(&node).copied() {
            return Ok(domain);
        }
        let id =
            u32::try_from(self.nodes.len()).map_err(|_| DomainError::capacity(self.nodes.len()))?;
        let domain = ControlDomain(id);
        self.nodes.push(node.clone());
        self.domains.insert(node, domain);
        if let Some(exact) = exact {
            self.exact.insert(domain, exact);
        }
        Ok(domain)
    }

    fn proof(&self, result: Result<Bdd, BddError>) -> Result<Option<Bdd>, DomainError> {
        match result {
            Ok(value) => Ok(Some(value)),
            Err(error) if error.is_resource_limit() => {
                self.saturated.set(true);
                Ok(None)
            }
            Err(error) => Err(error.into()),
        }
    }
}

enum CompileTask<'a> {
    Visit(&'a BoolExpr),
    Not,
    And(usize),
    Or(usize),
}
