//! Ordered symbolic Boolean expressions used by reaching-condition analysis.
//!
//! Construction preserves evaluation order. Semantic equivalence and
//! implication are delegated to ROBDDs instead of an expanding rewrite table.

use std::collections::BTreeSet;
use std::fmt;

use crate::ir::{BlockId, InstructionId};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BoolVariable {
    Block(BlockId),
    Instruction(InstructionId),
    Source(u32),
    Atom(u32),
    Named(String),
}

impl fmt::Display for BoolVariable {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Block(block) => write!(formatter, "block:{}", block.0),
            Self::Instruction(instruction) => write!(formatter, "insn:{instruction}"),
            Self::Source(variable) => write!(formatter, "source:v{variable}"),
            Self::Atom(atom) => write!(formatter, "atom:{atom}"),
            Self::Named(name) => formatter.write_str(name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BoolExpr {
    True,
    False,
    Symbol(BoolVariable),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
}

impl BoolExpr {
    pub fn symbol(name: impl Into<String>) -> Self {
        Self::Symbol(BoolVariable::Named(name.into()))
    }

    pub fn block(block: BlockId) -> Self {
        Self::Symbol(BoolVariable::Block(block))
    }

    pub fn instruction(instruction: InstructionId) -> Self {
        Self::Symbol(BoolVariable::Instruction(instruction))
    }

    pub fn source(variable: u32) -> Self {
        Self::Symbol(BoolVariable::Source(variable))
    }

    pub fn not(expr: Self) -> Self {
        match expr {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Not(inner) => *inner,
            other => Self::Not(Box::new(other)),
        }
    }

    pub fn and(exprs: Vec<Self>) -> Self {
        Self::junction(exprs, true)
    }

    pub fn or(exprs: Vec<Self>) -> Self {
        Self::junction(exprs, false)
    }

    fn junction(exprs: Vec<Self>, conjunction: bool) -> Self {
        let mut terms = Vec::new();
        for expression in exprs {
            match (conjunction, expression) {
                (true, Self::False) | (false, Self::True) => {
                    return if conjunction { Self::False } else { Self::True };
                }
                (true, Self::True) | (false, Self::False) => {}
                (true, Self::And(nested)) | (false, Self::Or(nested)) => terms.extend(nested),
                (_, term) => terms.push(term),
            }
        }
        match terms.len() {
            0 if conjunction => Self::True,
            0 => Self::False,
            1 => terms.into_iter().next().unwrap_or(if conjunction {
                Self::True
            } else {
                Self::False
            }),
            _ if conjunction => Self::And(terms),
            _ => Self::Or(terms),
        }
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Self::True)
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Self::False)
    }

    pub fn is_symbol(&self) -> bool {
        matches!(self, Self::Symbol(_))
    }

    pub fn symbols(&self) -> BTreeSet<BoolVariable> {
        let mut symbols = BTreeSet::new();
        let mut pending = vec![self];
        while let Some(expression) = pending.pop() {
            match expression {
                Self::Symbol(symbol) => {
                    symbols.insert(symbol.clone());
                }
                Self::Not(inner) => pending.push(inner),
                Self::And(terms) | Self::Or(terms) => pending.extend(terms),
                Self::True | Self::False => {}
            }
        }
        symbols
    }

    pub fn subexpressions(&self, limit: usize) -> BTreeSet<Self> {
        let mut expressions = BTreeSet::new();
        let mut pending = vec![self];
        while let Some(expression) = pending.pop() {
            if expressions.len() >= limit || !expressions.insert(expression.clone()) {
                continue;
            }
            match expression {
                Self::Not(inner) => pending.push(inner),
                Self::And(terms) | Self::Or(terms) => pending.extend(terms),
                Self::True | Self::False | Self::Symbol(_) => {}
            }
        }
        expressions
    }

    pub fn node_count(&self) -> usize {
        let mut count = 0usize;
        let mut pending = vec![self];
        while let Some(expression) = pending.pop() {
            count = count.saturating_add(1);
            match expression {
                Self::Not(inner) => pending.push(inner),
                Self::And(terms) | Self::Or(terms) => pending.extend(terms),
                Self::True | Self::False | Self::Symbol(_) => {}
            }
        }
        count
    }

    pub fn equivalent(&self, other: &Self) -> Result<bool, super::bdd::BddError> {
        let mut symbols = self.symbols();
        symbols.extend(other.symbols());
        super::bdd::BddContext::new(&symbols).are_equivalent(self, other)
    }
}

impl fmt::Display for BoolExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut pending = vec![BoolFormatTask::Expression(self)];
        while let Some(task) = pending.pop() {
            match task {
                BoolFormatTask::Expression(Self::True) => formatter.write_str("true")?,
                BoolFormatTask::Expression(Self::False) => formatter.write_str("false")?,
                BoolFormatTask::Expression(Self::Symbol(symbol)) => write!(formatter, "{symbol}")?,
                BoolFormatTask::Expression(Self::Not(inner)) => {
                    pending.push(BoolFormatTask::Text(")"));
                    pending.push(BoolFormatTask::Expression(inner));
                    pending.push(BoolFormatTask::Text("!("));
                }
                BoolFormatTask::Expression(Self::And(terms)) => {
                    pending.push(BoolFormatTask::Text(")"));
                    for (index, term) in terms.iter().enumerate().rev() {
                        pending.push(BoolFormatTask::Expression(term));
                        if index != 0 {
                            pending.push(BoolFormatTask::Text(" && "));
                        }
                    }
                    pending.push(BoolFormatTask::Text("("));
                }
                BoolFormatTask::Expression(Self::Or(terms)) => {
                    pending.push(BoolFormatTask::Text(")"));
                    for (index, term) in terms.iter().enumerate().rev() {
                        pending.push(BoolFormatTask::Expression(term));
                        if index != 0 {
                            pending.push(BoolFormatTask::Text(" || "));
                        }
                    }
                    pending.push(BoolFormatTask::Text("("));
                }
                BoolFormatTask::Text(text) => formatter.write_str(text)?,
            }
        }
        Ok(())
    }
}

enum BoolFormatTask<'a> {
    Expression(&'a BoolExpr),
    Text(&'static str),
}
