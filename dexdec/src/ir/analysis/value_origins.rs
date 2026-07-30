//! Transitive origins of SSA copies and Phi values.

use std::collections::{BTreeMap, BTreeSet};

use super::{SsaValueGraph, SsaVar};

#[derive(Debug, Clone, Default)]
pub struct SsaOrigins(BTreeMap<SsaVar, BTreeSet<SsaVar>>);

impl SsaOrigins {
    pub fn analyze(values: &SsaValueGraph) -> Self {
        let mut sources = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        for copy in values.copies() {
            sources.entry(copy.result).or_default().insert(copy.source);
        }
        for phi in values.phis() {
            sources
                .entry(phi.result)
                .or_default()
                .extend(phi.inputs.iter().map(|input| input.value));
        }

        let mut origins = values
            .values()
            .map(|value| {
                let roots = (!sources.contains_key(&value.variable))
                    .then(|| BTreeSet::from([value.variable]))
                    .unwrap_or_default();
                (value.variable, roots)
            })
            .collect::<BTreeMap<_, _>>();
        loop {
            let additions = sources
                .iter()
                .map(|(result, inputs)| {
                    let roots = inputs
                        .iter()
                        .flat_map(|input| origins.get(input).into_iter().flatten())
                        .copied()
                        .collect::<BTreeSet<_>>();
                    (*result, roots)
                })
                .collect::<Vec<_>>();
            let mut changed = false;
            for (result, roots) in additions {
                let current = origins.entry(result).or_default();
                let previous = current.len();
                current.extend(roots);
                changed |= current.len() != previous;
            }
            if !changed {
                break;
            }
        }
        Self(origins)
    }

    pub fn origins(&self, value: SsaVar) -> Option<&BTreeSet<SsaVar>> {
        self.0.get(&value)
    }

    pub fn equivalent(&self, left: SsaVar, right: SsaVar) -> bool {
        match (self.origins(left), self.origins(right)) {
            (Some(left), Some(right)) => !left.is_empty() && left == right,
            _ => false,
        }
    }

    pub fn unique(&self, value: SsaVar) -> Option<SsaVar> {
        let roots = self.origins(value)?;
        (roots.len() == 1).then(|| roots.first().copied()).flatten()
    }
}
