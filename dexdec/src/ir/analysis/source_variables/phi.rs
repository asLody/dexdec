use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::ir::{
    analysis::{types::SourceTypeLattice, TypeHierarchy},
    ArgType, BlockId, InsnArg, InsnNode, InsnType, InstructionId, InstructionTree,
    InstructionVisitor, RegionExit, RegionGraph, RegionId, RegisterArg, SemanticBlock,
    SemanticExpression, SemanticFolder, SemanticNode, SemanticStatement, SemanticVisitor,
    StatementOrigin, Utf16String, CFG,
};

use super::{
    edge_arguments::{same_value, ContractedEdgeArguments},
    interference::{InstructionUses, SsaLiveness},
    loop_exit_copies::LoopExitCopyPlacement,
    CodeVariables, ControlContractions, NormalCopySite, SourceTypeEnvironment, SourceVariableError,
    SsaTypeEnvironment, SsaValueGraph, SsaVar, TypeConstraintError,
};

#[derive(Clone)]
struct EdgeCopy {
    destination: RegisterArg,
    source: InsnArg,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CopySource {
    Variable(u32),
    Literal(i64, ArgType),
    String(Utf16String),
}

impl CopySource {
    fn from_arg(source: &InsnArg, variables: &CodeVariables) -> Result<Self, SourceVariableError> {
        match source {
            InsnArg::Reg(register) => {
                let value = SsaVar::from_reg(register)
                    .ok_or(SourceVariableError::MissingRegisterIdentity)?;
                register
                    .code_var
                    .or_else(|| variables.variable_of(value))
                    .map(Self::Variable)
                    .ok_or(SourceVariableError::MissingCodeVariable(value))
            }
            InsnArg::Lit(literal) => Ok(Self::Literal(literal.value, literal.ty.clone())),
            InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::ConstStr => Ok(
                Self::String(instruction.payload.string_value.clone().unwrap_or_default()),
            ),
            InsnArg::Wrapped(_) => Err(SourceVariableError::MissingRegisterIdentity),
        }
    }
}

type CopyFacts = BTreeSet<(u32, CopySource)>;

/// Forward must-analysis for source-variable values already established on
/// normal control-flow paths. Exceptional Phi copies are unnecessary when the
/// same value is available immediately before the throwing instruction.
struct AvailableCopyAnalysis {
    before_throw: BTreeMap<BlockId, CopyFacts>,
    before_normal: BTreeMap<BlockId, CopyFacts>,
    before_edge: BTreeMap<crate::ir::RegionEdge, CopyFacts>,
}

impl AvailableCopyAnalysis {
    fn analyze(
        cfg: &CFG,
        variables: &CodeVariables,
        normal_copies: &BTreeMap<NormalCopySite, Vec<EdgeCopy>>,
        exceptional_copies: &BTreeMap<BlockId, CopyFacts>,
        statement_definitions: &BTreeSet<SsaVar>,
    ) -> Result<Self, SourceVariableError> {
        let universe = Self::universe(
            cfg,
            variables,
            normal_copies,
            exceptional_copies,
            statement_definitions,
        )?;
        let mut inputs = cfg
            .block_ids()
            .into_iter()
            .map(|block| (block, universe.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut outputs = inputs.clone();
        inputs.insert(cfg.entry, CopyFacts::new());

        loop {
            let mut changed = false;
            for block in cfg.block_ids() {
                let input = if block == cfg.entry {
                    CopyFacts::new()
                } else {
                    let mut states = Vec::new();
                    for (predecessor, kind) in cfg
                        .incoming_edges(block)
                        .into_iter()
                        .filter(|(_, kind)| !kind.is_exception())
                    {
                        let Some(mut state) = outputs.get(&predecessor).cloned() else {
                            continue;
                        };
                        let edge = crate::ir::RegionEdge {
                            source: predecessor,
                            target: block,
                            kind,
                        };
                        for copy in normal_copies
                            .get(&NormalCopySite::Edge(edge))
                            .into_iter()
                            .flatten()
                        {
                            Self::transfer_copy(&mut state, copy, variables)?;
                        }
                        states.push(state);
                    }
                    Self::meet(states.iter())
                };
                let mut output = input.clone();
                let body = cfg
                    .block(block)
                    .ok_or(SourceVariableError::MissingBlock(block))?;
                let (last, prefix) = body
                    .insns
                    .split_last()
                    .map_or((None, &[][..]), |(last, prefix)| (Some(last), prefix));
                for instruction in prefix {
                    Self::transfer_instruction(
                        &mut output,
                        instruction,
                        variables,
                        statement_definitions,
                    )?;
                }
                for (destination, source) in exceptional_copies.get(&block).into_iter().flatten() {
                    Self::define(&mut output, *destination, Some(source.clone()));
                }
                if let Some(last) = last {
                    Self::transfer_instruction(
                        &mut output,
                        last,
                        variables,
                        statement_definitions,
                    )?;
                }
                for copy in normal_copies
                    .get(&NormalCopySite::Block(block))
                    .into_iter()
                    .flatten()
                {
                    Self::transfer_copy(&mut output, copy, variables)?;
                }
                changed |= inputs.get(&block) != Some(&input);
                changed |= outputs.get(&block) != Some(&output);
                inputs.insert(block, input);
                outputs.insert(block, output);
            }
            if !changed {
                break;
            }
        }

        let mut before_throw = BTreeMap::new();
        let mut before_normal = BTreeMap::new();
        let mut before_edge = BTreeMap::new();
        for block in cfg.block_ids() {
            let body = cfg
                .block(block)
                .ok_or(SourceVariableError::MissingBlock(block))?;
            let mut facts = inputs.get(&block).cloned().unwrap_or_default();
            let (last, prefix) = body
                .insns
                .split_last()
                .map_or((None, &[][..]), |(last, prefix)| (Some(last), prefix));
            for instruction in prefix {
                Self::transfer_instruction(
                    &mut facts,
                    instruction,
                    variables,
                    statement_definitions,
                )?;
            }
            if last.is_some_and(InsnNode::can_throw) {
                before_throw.insert(block, facts.clone());
            }
            for (destination, source) in exceptional_copies.get(&block).into_iter().flatten() {
                Self::define(&mut facts, *destination, Some(source.clone()));
            }
            if let Some(last) = last {
                Self::transfer_instruction(&mut facts, last, variables, statement_definitions)?;
            }
            before_normal.insert(block, facts.clone());
            for copy in normal_copies
                .get(&NormalCopySite::Block(block))
                .into_iter()
                .flatten()
            {
                Self::transfer_copy(&mut facts, copy, variables)?;
            }
            for (target, kind) in cfg.successors_with_kind(block) {
                if kind.is_exception() {
                    continue;
                }
                before_edge.insert(
                    crate::ir::RegionEdge {
                        source: block,
                        target: *target,
                        kind: *kind,
                    },
                    facts.clone(),
                );
            }
        }
        Ok(Self {
            before_throw,
            before_normal,
            before_edge,
        })
    }

    fn universe(
        cfg: &CFG,
        variables: &CodeVariables,
        normal_copies: &BTreeMap<NormalCopySite, Vec<EdgeCopy>>,
        exceptional_copies: &BTreeMap<BlockId, CopyFacts>,
        statement_definitions: &BTreeSet<SsaVar>,
    ) -> Result<CopyFacts, SourceVariableError> {
        let mut facts = CopyFacts::new();
        for copy in normal_copies.values().flatten() {
            if let Some(fact) = Self::copy_fact(copy, variables)? {
                facts.insert(fact);
            }
        }
        facts.extend(
            exceptional_copies
                .values()
                .flat_map(|block| block.iter().cloned()),
        );
        for body in cfg.blocks.values() {
            for instruction in &body.insns {
                if !Self::is_statement_definition(instruction, statement_definitions) {
                    continue;
                }
                if let Some(fact) = Self::instruction_fact(instruction, variables)? {
                    facts.insert(fact);
                }
            }
        }
        Ok(facts)
    }

    fn meet<'a>(mut states: impl Iterator<Item = &'a CopyFacts>) -> CopyFacts {
        let Some(mut facts) = states.next().cloned() else {
            return CopyFacts::new();
        };
        for state in states {
            facts.retain(|fact| state.contains(fact));
        }
        facts
    }

    fn transfer_instruction(
        facts: &mut CopyFacts,
        instruction: &InsnNode,
        variables: &CodeVariables,
        statement_definitions: &BTreeSet<SsaVar>,
    ) -> Result<(), SourceVariableError> {
        if instruction.insn_type == InsnType::Phi
            || !Self::is_statement_definition(instruction, statement_definitions)
        {
            return Ok(());
        }
        let Some(result) = instruction.result.as_ref() else {
            return Ok(());
        };
        let destination = Self::variable_of(result, variables)?;
        let source = Self::instruction_source(instruction, variables)?;
        Self::define(facts, destination, source);
        Ok(())
    }

    fn is_statement_definition(
        instruction: &InsnNode,
        statement_definitions: &BTreeSet<SsaVar>,
    ) -> bool {
        instruction
            .result
            .as_ref()
            .and_then(SsaVar::from_reg)
            .is_some_and(|value| statement_definitions.contains(&value))
    }

    fn transfer_copy(
        facts: &mut CopyFacts,
        copy: &EdgeCopy,
        variables: &CodeVariables,
    ) -> Result<(), SourceVariableError> {
        let destination = Self::variable_of(&copy.destination, variables)?;
        let source = CopySource::from_arg(&copy.source, variables)?;
        Self::define(facts, destination, Some(source));
        Ok(())
    }

    fn instruction_fact(
        instruction: &InsnNode,
        variables: &CodeVariables,
    ) -> Result<Option<(u32, CopySource)>, SourceVariableError> {
        let Some(result) = instruction.result.as_ref() else {
            return Ok(None);
        };
        let destination = Self::variable_of(result, variables)?;
        Ok(Self::instruction_source(instruction, variables)?
            .filter(|source| *source != CopySource::Variable(destination))
            .map(|source| (destination, source)))
    }

    fn copy_fact(
        copy: &EdgeCopy,
        variables: &CodeVariables,
    ) -> Result<Option<(u32, CopySource)>, SourceVariableError> {
        let destination = Self::variable_of(&copy.destination, variables)?;
        let source = CopySource::from_arg(&copy.source, variables)?;
        Ok((source != CopySource::Variable(destination)).then_some((destination, source)))
    }

    fn instruction_source(
        instruction: &InsnNode,
        variables: &CodeVariables,
    ) -> Result<Option<CopySource>, SourceVariableError> {
        match instruction.insn_type {
            InsnType::Const | InsnType::Move => instruction
                .args
                .first()
                .map(|source| CopySource::from_arg(source, variables))
                .transpose(),
            InsnType::ConstStr => Ok(Some(CopySource::String(
                instruction.payload.string_value.clone().unwrap_or_default(),
            ))),
            _ => Ok(None),
        }
    }

    fn variable_of(
        register: &RegisterArg,
        variables: &CodeVariables,
    ) -> Result<u32, SourceVariableError> {
        let value =
            SsaVar::from_reg(register).ok_or(SourceVariableError::MissingRegisterIdentity)?;
        register
            .code_var
            .or_else(|| variables.variable_of(value))
            .ok_or(SourceVariableError::MissingCodeVariable(value))
    }

    fn define(facts: &mut CopyFacts, destination: u32, source: Option<CopySource>) {
        if source == Some(CopySource::Variable(destination)) {
            return;
        }
        facts.retain(|(variable, value)| {
            *variable != destination && *value != CopySource::Variable(destination)
        });
        if let Some(source) = source {
            facts.insert((destination, source));
        }
    }

    fn contains(&self, block: BlockId, destination: u32, source: &CopySource) -> bool {
        self.before_throw
            .get(&block)
            .is_some_and(|facts| facts.contains(&(destination, source.clone())))
    }

    fn contains_before_normal(
        &self,
        block: BlockId,
        destination: u32,
        source: &CopySource,
    ) -> bool {
        self.before_normal
            .get(&block)
            .is_some_and(|facts| facts.contains(&(destination, source.clone())))
    }

    fn contains_before_site(
        &self,
        site: NormalCopySite,
        destination: u32,
        source: &CopySource,
    ) -> bool {
        match site {
            NormalCopySite::Block(block) => self.contains_before_normal(block, destination, source),
            NormalCopySite::Edge(edge) => self
                .before_edge
                .get(&edge)
                .is_some_and(|facts| facts.contains(&(destination, source.clone()))),
        }
    }
}

pub(super) struct PhiCopies;

struct SsaCopyResolver<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    materialized: &'a BTreeSet<SsaVar>,
}

impl<'a> SsaCopyResolver<'a> {
    fn new(cfg: &'a CFG, values: &'a SsaValueGraph, materialized: &'a BTreeSet<SsaVar>) -> Self {
        Self {
            cfg,
            values,
            materialized,
        }
    }

    fn resolve(&self, source: InsnArg) -> InsnArg {
        let InsnArg::Reg(mut register) = source else {
            return source;
        };
        let mut visited = BTreeSet::new();
        while let Some(value) = SsaVar::from_reg(&register) {
            if self.materialized.contains(&value) || !visited.insert(value) {
                break;
            }
            let Some(position) = self.values.value(value).and_then(|value| value.definition) else {
                break;
            };
            let Some(instruction) = self
                .cfg
                .block(position.block)
                .and_then(|block| block.insns.get(position.index))
            else {
                break;
            };
            let Some(source) = instruction
                .args
                .first()
                .filter(|_| instruction.insn_type == InsnType::Move)
                .and_then(InsnArg::as_register)
            else {
                break;
            };
            register = source.clone();
        }
        InsnArg::Reg(register)
    }

    fn resolve_for_edge(
        &self,
        source: InsnArg,
        predecessor: BlockId,
        edge_kind: crate::ir::EdgeKind,
        constants: &BTreeMap<SsaVar, InsnArg>,
    ) -> Option<InsnArg> {
        let mut source = self.resolve(source);
        let mut visited = BTreeSet::new();
        loop {
            let Some(register) = source.as_register() else {
                break;
            };
            let Some(value) = SsaVar::from_reg(register) else {
                break;
            };
            if self.materialized.contains(&value) || !visited.insert(value) {
                break;
            }
            let Some(position) = self.values.value(value).and_then(|value| value.definition) else {
                break;
            };
            let Some(instruction) = self
                .cfg
                .block(position.block)
                .and_then(|block| block.insns.get(position.index))
            else {
                break;
            };
            if instruction.insn_type != InsnType::Phi {
                break;
            }
            let Some(index) = instruction
                .payload
                .phi_edges
                .iter()
                .position(|edge| *edge == (predecessor, edge_kind))
            else {
                break;
            };
            let Some(argument) = instruction.args.get(index) else {
                break;
            };
            source = self.resolve(argument.clone());
        }
        let value = source.as_register().and_then(SsaVar::from_reg)?;
        (self.materialized.contains(&value) || constants.contains_key(&value)).then_some(source)
    }
}

pub(super) struct RequiredPhiValues {
    values: BTreeSet<SsaVar>,
}

impl RequiredPhiValues {
    pub(super) fn collect(
        cfg: &CFG,
        graph: &SsaValueGraph,
        root: &SemanticNode,
        constants: &BTreeMap<SsaVar, InsnArg>,
        recovered: &BTreeSet<SsaVar>,
        contractions: &ControlContractions,
    ) -> Result<BTreeSet<SsaVar>, SourceVariableError> {
        let mut collector = Self {
            values: BTreeSet::new(),
        };
        collector.visit_node(root);
        let roots = collector.values;
        let materialized = StatementDefinitions::collect(root);
        let mut pending = roots.iter().copied().collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        let mut required = BTreeSet::new();
        let edge_arguments = ContractedEdgeArguments::new(cfg, graph, constants, contractions);
        while let Some(value) = pending.pop() {
            if !visited.insert(value)
                || (recovered.contains(&value) && materialized.contains(&value))
                || PhiCopies::canonical_constant(constants, value).is_some()
            {
                continue;
            }
            let Some(position) = graph.value(value).and_then(|value| value.definition) else {
                continue;
            };
            let instruction = cfg
                .block(position.block)
                .and_then(|block| block.insns.get(position.index))
                .ok_or(SourceVariableError::MissingBlock(position.block))?;
            required.insert(value);
            match instruction.insn_type {
                InsnType::Phi => {
                    for argument in edge_arguments.resolve_all(position.block, instruction)? {
                        let Some(value) = argument.value.explicit() else {
                            continue;
                        };
                        let mut dependencies = ArgumentDependencies::default();
                        InstructionTree::visit_arg(value, &mut dependencies);
                        pending.extend(dependencies.values);
                    }
                }
                InsnType::Move => {
                    if let Some(source) = instruction
                        .args
                        .first()
                        .and_then(InsnArg::as_register)
                        .and_then(SsaVar::from_reg)
                    {
                        pending.push(source);
                    }
                }
                _ => {}
            }
        }
        Ok(required)
    }
}

#[derive(Default)]
struct ArgumentDependencies {
    values: BTreeSet<SsaVar>,
}

impl InstructionVisitor for ArgumentDependencies {
    fn visit_register(&mut self, register: &RegisterArg) {
        self.values.extend(SsaVar::from_reg(register));
    }
}

impl SemanticVisitor for RequiredPhiValues {
    fn visit_register(&mut self, register: &RegisterArg) {
        self.values.extend(SsaVar::from_reg(register));
    }
}

pub(super) struct RetainedSsaValues {
    values: BTreeSet<SsaVar>,
}

pub(super) struct StatementDefinitions {
    values: BTreeSet<SsaVar>,
}

impl StatementDefinitions {
    pub(super) fn collect(root: &SemanticNode) -> BTreeSet<SsaVar> {
        let mut collector = Self {
            values: BTreeSet::new(),
        };
        collector.visit_node(root);
        collector.values
    }
}

impl SemanticVisitor for StatementDefinitions {
    fn visit_statement(&mut self, statement: &SemanticStatement) {
        self.values
            .extend(statement.result().and_then(SsaVar::from_reg));
    }
}

impl RetainedSsaValues {
    pub(super) fn collect(root: &SemanticNode) -> BTreeSet<SsaVar> {
        let mut collector = Self {
            values: BTreeSet::new(),
        };
        collector.visit_node(root);
        collector.values
    }
}

impl SemanticVisitor for RetainedSsaValues {
    fn enter_operation(&mut self, instruction: &crate::ir::SemanticOperation) {
        self.values
            .extend(instruction.result.as_ref().and_then(SsaVar::from_reg));
    }

    fn visit_register(&mut self, register: &RegisterArg) {
        self.values.extend(SsaVar::from_reg(register));
    }
}

pub(super) struct CollectedPhiCopies {
    normal: BTreeMap<NormalCopySite, Vec<EdgeCopy>>,
    exceptional: BTreeMap<ExceptionalEdge, Vec<EdgeCopy>>,
    variable_types: BTreeMap<u32, ArgType>,
}

pub(super) struct PhiCopySet {
    normal: BTreeMap<NormalCopySite, Vec<EdgeCopy>>,
    exceptional: BTreeMap<StatementOrigin, Vec<EdgeCopy>>,
    exceptional_spills: Vec<ExceptionalSpill>,
    variable_types: BTreeMap<u32, ArgType>,
}

struct NormalCopies {
    by_site: BTreeMap<NormalCopySite, Vec<SemanticStatement>>,
    canonical_site: BTreeMap<NormalCopySite, NormalCopySite>,
    // Equivalent sites satisfy one structural coverage obligation, but each
    // concrete CFG site that survives semantically must still execute copies.
    placed_sites: BTreeSet<NormalCopySite>,
    covered_classes: BTreeSet<NormalCopySite>,
}

impl NormalCopies {
    fn new(
        by_site: BTreeMap<NormalCopySite, Vec<SemanticStatement>>,
        canonical_site: BTreeMap<NormalCopySite, NormalCopySite>,
    ) -> Self {
        Self {
            by_site,
            canonical_site,
            placed_sites: BTreeSet::new(),
            covered_classes: BTreeSet::new(),
        }
    }

    fn canonical(&self, site: NormalCopySite) -> NormalCopySite {
        self.canonical_site.get(&site).copied().unwrap_or(site)
    }

    fn place_once(&mut self, site: NormalCopySite) -> Option<Vec<SemanticStatement>> {
        if !self.placed_sites.insert(site) {
            return None;
        }
        let canonical = self.canonical(site);
        self.covered_classes.insert(canonical);
        let statements = self
            .by_site
            .get(&site)
            .or_else(|| self.by_site.get(&canonical))?;
        Some(statements.clone())
    }

    fn place_once_on_path(
        &mut self,
        sites: impl IntoIterator<Item = NormalCopySite>,
    ) -> Option<Vec<SemanticStatement>> {
        sites
            .into_iter()
            .find(|site| self.by_site.contains_key(site))
            .and_then(|site| self.place_once(site))
    }

    fn place_at_occurrence(&mut self, site: NormalCopySite) -> Option<Vec<SemanticStatement>> {
        let canonical = self.canonical(site);
        self.placed_sites.insert(site);
        self.covered_classes.insert(canonical);
        self.by_site
            .get(&site)
            .or_else(|| self.by_site.get(&canonical))
            .cloned()
    }

    fn place_block_occurrence(
        &mut self,
        site: NormalCopySite,
        repeats_semantically: bool,
    ) -> Option<Vec<SemanticStatement>> {
        if repeats_semantically && self.is_idempotent(site) {
            self.place_at_occurrence(site)
        } else {
            self.place_once(site)
        }
    }

    fn is_idempotent(&self, site: NormalCopySite) -> bool {
        let site = self.canonical(site);
        let Some(statements) = self.by_site.get(&site) else {
            return false;
        };
        let destinations = statements
            .iter()
            .filter_map(SemanticStatement::result)
            .filter_map(|result| result.code_var)
            .collect::<BTreeSet<_>>();
        !destinations.is_empty()
            && statements.iter().all(|statement| {
                let Some(instruction) = statement.instruction_ref() else {
                    return false;
                };
                instruction.insn_type == InsnType::Move
                    && instruction.payload.edge_copy
                    && instruction
                        .operands()
                        .first()
                        .and_then(SemanticExpression::as_register)
                        .and_then(|source| source.code_var)
                        .is_none_or(|source| !destinations.contains(&source))
            })
    }

    fn first_unplaced(&self) -> Option<NormalCopySite> {
        self.by_site
            .keys()
            .map(|site| self.canonical(*site))
            .find(|site| !self.covered_classes.contains(site))
    }

    fn get(&self, site: NormalCopySite) -> Option<&Vec<SemanticStatement>> {
        let site = self.canonical(site);
        self.by_site.get(&site)
    }
}

struct EquivalentCopySites;

impl EquivalentCopySites {
    fn analyze(
        cfg: &CFG,
        regions: &RegionGraph,
        copies: &BTreeMap<NormalCopySite, Vec<EdgeCopy>>,
    ) -> BTreeMap<NormalCopySite, NormalCopySite> {
        let mut classes = Vec::<Vec<NormalCopySite>>::new();
        for site in copies.keys().copied() {
            if let Some(class) = classes.iter_mut().find(|class| {
                Self::same_semantic_exit(cfg, regions, site, class[0])
                    && Self::same_copy_vector(&copies[&site], &copies[&class[0]])
            }) {
                class.push(site);
            } else {
                classes.push(vec![site]);
            }
        }
        classes
            .into_iter()
            .flat_map(|class| {
                let canonical = class[0];
                class.into_iter().map(move |site| (site, canonical))
            })
            .collect()
    }

    fn same_semantic_exit(
        cfg: &CFG,
        regions: &RegionGraph,
        left: NormalCopySite,
        right: NormalCopySite,
    ) -> bool {
        let Some(left) = Self::leave(cfg, regions, left) else {
            return false;
        };
        let Some(right) = Self::leave(cfg, regions, right) else {
            return false;
        };
        left.leave.source == right.leave.source
            && left.leave.target == right.leave.target
            && left.leave.control_target == right.leave.control_target
            && left.cleanup_regions == right.cleanup_regions
            && Self::same_exit(&left.leave.exit, &right.leave.exit)
    }

    fn leave<'a>(
        cfg: &CFG,
        regions: &'a RegionGraph,
        site: NormalCopySite,
    ) -> Option<&'a crate::ir::ResolvedRegionExit> {
        let edge = match site {
            NormalCopySite::Edge(edge) => edge,
            NormalCopySite::Block(source) => {
                let edges = cfg
                    .successors_with_kind(source)
                    .iter()
                    .filter(|(_, kind)| !kind.is_exception())
                    .copied()
                    .collect::<Vec<_>>();
                let [(target, kind)] = edges.as_slice() else {
                    return None;
                };
                crate::ir::RegionEdge {
                    source,
                    target: *target,
                    kind: *kind,
                }
            }
        };
        regions.leave_for_edge(edge)
    }

    fn same_exit(left: &RegionExit, right: &RegionExit) -> bool {
        match (left, right) {
            (RegionExit::FallThrough(left), RegionExit::FallThrough(right)) => left == right,
            (RegionExit::Return(None), RegionExit::Return(None))
            | (RegionExit::Break, RegionExit::Break)
            | (RegionExit::Continue, RegionExit::Continue) => true,
            (RegionExit::Return(Some(left)), RegionExit::Return(Some(right)))
            | (RegionExit::Throw(left), RegionExit::Throw(right)) => same_value(left, right),
            _ => false,
        }
    }

    fn same_copy_vector(left: &[EdgeCopy], right: &[EdgeCopy]) -> bool {
        left.len() == right.len()
            && left.iter().all(|left| {
                right.iter().any(|right| {
                    left.destination.code_var == right.destination.code_var
                        && same_value(&left.source, &right.source)
                })
            })
    }
}

struct ExceptionalSpill {
    origin: StatementOrigin,
    handler: ExceptionHandlerPort,
    copy: EdgeCopy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ExceptionalEdge {
    predecessor: BlockId,
    handler: ExceptionHandlerTarget,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ExceptionHandlerTarget {
    ingress: BlockId,
    port: Option<ExceptionHandlerPort>,
}

impl ExceptionHandlerTarget {
    fn resolve(
        ingress: BlockId,
        contractions: &ControlContractions,
        regions: &RegionGraph,
    ) -> Self {
        Self {
            ingress,
            port: ExceptionHandlerPort::resolve(ingress, contractions, regions),
        }
    }

    fn require(self) -> Result<ExceptionHandlerPort, SourceVariableError> {
        self.port
            .ok_or(SourceVariableError::MissingHandlerEntry(self.ingress))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ExceptionHandlerPort {
    region: RegionId,
    entry: BlockId,
}

impl ExceptionHandlerPort {
    fn resolve(
        ingress: BlockId,
        contractions: &ControlContractions,
        regions: &RegionGraph,
    ) -> Option<Self> {
        Self::at_or_detached(ingress, regions)
            .or_else(|| {
                regions
                    .handler_adapters()
                    .get(&ingress)
                    .and_then(|entry| Self::at_or_detached(*entry, regions))
            })
            .or_else(|| {
                contractions
                    .terminal(ingress)
                    .filter(|terminal| *terminal != ingress)
                    .and_then(|terminal| Self::at_or_detached(terminal, regions))
            })
    }

    fn at_or_detached(block: BlockId, regions: &RegionGraph) -> Option<Self> {
        Self::at(block, regions).or_else(|| {
            Self::detached_continuation(
                block,
                regions.tree(),
                regions
                    .tree()
                    .regions()
                    .filter(|region| regions.is_exception_handler(region.id))
                    .map(|region| region.id),
            )
        })
    }

    /// Resolve an empty handler whose physical entry is also an ordinary CFG
    /// continuation. Such handlers cannot own the shared block lexically, so
    /// region recovery records it as the handler continuation instead.
    fn detached_continuation(
        block: BlockId,
        tree: &crate::ir::RegionTree,
        handlers: impl IntoIterator<Item = RegionId>,
    ) -> Option<Self> {
        let mut matches = handlers.into_iter().filter(|handler| {
            tree.region(*handler).is_some_and(|region| {
                region.entry.is_none() && region.kind.continuation() == Some(block)
            })
        });
        let region = matches.next()?;
        matches.next().is_none().then_some(Self {
            region,
            entry: block,
        })
    }

    fn at(block: BlockId, regions: &RegionGraph) -> Option<Self> {
        let region = regions.enclosing_exception_handler(block)?;
        let handler = regions.tree().region(region)?;
        let entry = handler.entry.or_else(|| handler.kind.continuation())?;
        Some(Self { region, entry })
    }
}

enum ExceptionalAssignment {
    Shared {
        handler: ExceptionHandlerTarget,
        source: CopySource,
        copy: EdgeCopy,
    },
    Spilled,
}

impl ExceptionalAssignment {
    fn spill(&mut self) -> Option<(ExceptionHandlerTarget, EdgeCopy)> {
        match std::mem::replace(self, Self::Spilled) {
            Self::Shared { handler, copy, .. } => Some((handler, copy)),
            Self::Spilled => None,
        }
    }
}

/// Places parallel copies when a split critical edge is absorbed by a
/// structured control node.
///
/// Copies may move to the branch source only when their destination variables
/// are dead on every other normal successor and are not read by the branch
/// predicate. This is the standard out-of-SSA predecessor-placement proof.
struct NormalCopyPlacement<'a> {
    cfg: &'a CFG,
    variables: &'a CodeVariables,
    liveness: &'a SsaLiveness,
    semantic_blocks: BTreeSet<BlockId>,
}

impl<'a> NormalCopyPlacement<'a> {
    fn new(
        cfg: &'a CFG,
        variables: &'a CodeVariables,
        liveness: &'a SsaLiveness,
        semantic: &SemanticNode,
    ) -> Self {
        Self {
            cfg,
            variables,
            liveness,
            semantic_blocks: SemanticBlocks::collect(semantic),
        }
    }

    fn apply(
        &self,
        copies: &mut BTreeMap<NormalCopySite, Vec<EdgeCopy>>,
    ) -> Result<(), SourceVariableError> {
        let adapters = copies
            .keys()
            .filter_map(|site| match site {
                NormalCopySite::Block(block) => Some(*block),
                NormalCopySite::Edge(_) => None,
            })
            .collect::<Vec<_>>();
        for adapter in adapters {
            if self.semantic_blocks.contains(&adapter) {
                continue;
            }
            let Some(edge) = SplitEdgeBlock::analyze(self.cfg, adapter) else {
                continue;
            };
            if !self.semantic_blocks.contains(&edge.source) {
                continue;
            }
            let site = NormalCopySite::Block(adapter);
            let Some(edge_copies) = copies.get(&site) else {
                continue;
            };
            if !self.can_lift(&edge, edge_copies)? {
                continue;
            }
            let edge_copies = copies.remove(&site).unwrap_or_default();
            copies
                .entry(NormalCopySite::Block(edge.source))
                .or_default()
                .extend(edge_copies);
        }
        Ok(())
    }

    fn can_lift(
        &self,
        edge: &SplitEdgeBlock,
        copies: &[EdgeCopy],
    ) -> Result<bool, SourceVariableError> {
        let destinations = copies
            .iter()
            .map(|copy| self.code_variable(&copy.destination))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let branch_uses = self
            .cfg
            .block(edge.source)
            .and_then(|block| block.insns.last())
            .map(InstructionUses::collect)
            .unwrap_or_default();
        if branch_uses
            .into_iter()
            .filter_map(|value| self.variables.variable_of(value))
            .any(|variable| destinations.contains(&variable))
        {
            return Ok(false);
        }
        for &(target, kind) in self.cfg.successors_with_kind(edge.source) {
            if kind.is_exception() || target == edge.adapter {
                continue;
            }
            if self
                .liveness
                .edge_live(edge.source, target, kind)?
                .iter()
                .filter_map(|value| self.variables.variable_of(*value))
                .any(|variable| destinations.contains(&variable))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn code_variable(&self, register: &RegisterArg) -> Result<u32, SourceVariableError> {
        let value =
            SsaVar::from_reg(register).ok_or(SourceVariableError::MissingRegisterIdentity)?;
        register
            .code_var
            .or_else(|| self.variables.variable_of(value))
            .ok_or(SourceVariableError::MissingCodeVariable(value))
    }
}

struct SplitEdgeBlock {
    source: BlockId,
    adapter: BlockId,
}

impl SplitEdgeBlock {
    fn analyze(cfg: &CFG, adapter: BlockId) -> Option<Self> {
        let block = cfg.block(adapter)?;
        if !block.synthetic
            || !block
                .insns
                .iter()
                .all(|instruction| matches!(instruction.insn_type, InsnType::Nop | InsnType::Goto))
            || cfg
                .successors_with_kind(adapter)
                .iter()
                .any(|(_, kind)| kind.is_exception())
        {
            return None;
        }
        let mut successors = cfg.normal_successors(adapter);
        let destination = successors.next()?;
        if successors.next().is_some() {
            return None;
        }
        let incoming = cfg.incoming_edges(adapter);
        if incoming.iter().any(|(_, kind)| kind.is_exception()) {
            return None;
        }
        let sources = incoming
            .iter()
            .map(|(source, _)| *source)
            .collect::<BTreeSet<_>>();
        let mut sources = sources.into_iter();
        let source = sources.next()?;
        if sources.next().is_some() {
            return None;
        }
        if cfg.normal_successors(source).collect::<BTreeSet<_>>().len() <= 1
            || cfg.incoming_edges(destination).len() <= 1
        {
            return None;
        }
        Some(Self { source, adapter })
    }
}

/// Repositions copies from a physical exception ingress that structural
/// recovery absorbs into a handler port.
///
/// This is critical-edge splitting in reverse: a copy may be evaluated at
/// each throwing predecessor when the ingress has no normal predecessor and
/// the physical block has no surviving semantic identity. Path-invariant
/// sources can be cloned directly. Register sources must resolve to an
/// available value for every exceptional edge, selecting the ingress Phi input
/// when necessary. Later liveness analysis spills the value when evaluating it
/// on the predecessor would clobber a normal path.
struct ExceptionalIngressCopyPlacement<'a> {
    cfg: &'a CFG,
    semantic_blocks: BTreeSet<BlockId>,
    contractions: &'a ControlContractions,
    regions: &'a RegionGraph,
    values: &'a SsaValueGraph,
    materialized: &'a BTreeSet<SsaVar>,
    required_phis: &'a BTreeSet<SsaVar>,
    constants: &'a BTreeMap<SsaVar, InsnArg>,
}

impl<'a> ExceptionalIngressCopyPlacement<'a> {
    fn new(
        cfg: &'a CFG,
        semantic: &SemanticNode,
        contractions: &'a ControlContractions,
        regions: &'a RegionGraph,
        values: &'a SsaValueGraph,
        materialized: &'a BTreeSet<SsaVar>,
        required_phis: &'a BTreeSet<SsaVar>,
        constants: &'a BTreeMap<SsaVar, InsnArg>,
    ) -> Self {
        Self {
            cfg,
            semantic_blocks: SemanticBlocks::collect(semantic),
            contractions,
            regions,
            values,
            materialized,
            required_phis,
            constants,
        }
    }

    fn apply(&self, copies: &mut CollectedPhiCopies) {
        let available = Self::available_values(self.materialized, self.required_phis);
        let resolver = SsaCopyResolver::new(self.cfg, self.values, &available);
        let ingresses = copies
            .normal
            .keys()
            .filter_map(|site| match site {
                NormalCopySite::Block(block) if !self.semantic_blocks.contains(block) => {
                    Some(*block)
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        for ingress in ingresses {
            let incoming = self.cfg.incoming_edges(ingress);
            if incoming.is_empty() || incoming.iter().any(|(_, kind)| !kind.is_exception()) {
                continue;
            }
            let site = NormalCopySite::Block(ingress);
            let Some(block_copies) = copies.normal.remove(&site) else {
                continue;
            };
            let handler = ExceptionHandlerTarget::resolve(ingress, self.contractions, self.regions);
            let mut retained = Vec::new();
            for copy in block_copies {
                let sources = if Self::is_path_invariant(&copy.source) {
                    Some(vec![copy.source.clone(); incoming.len()])
                } else {
                    incoming
                        .iter()
                        .map(|(predecessor, kind)| {
                            resolver.resolve_for_edge(
                                copy.source.clone(),
                                *predecessor,
                                *kind,
                                self.constants,
                            )
                        })
                        .collect::<Option<Vec<_>>>()
                };
                let Some(sources) = sources else {
                    retained.push(copy);
                    continue;
                };
                for ((predecessor, _), source) in incoming.iter().zip(sources) {
                    copies
                        .exceptional
                        .entry(ExceptionalEdge {
                            predecessor: *predecessor,
                            handler,
                        })
                        .or_default()
                        .push(EdgeCopy {
                            destination: copy.destination.clone(),
                            source,
                        });
                }
            }
            if !retained.is_empty() {
                copies.normal.insert(site, retained);
            }
        }
    }

    fn available_values(
        materialized: &BTreeSet<SsaVar>,
        required_phis: &BTreeSet<SsaVar>,
    ) -> BTreeSet<SsaVar> {
        materialized.union(required_phis).copied().collect()
    }

    fn is_path_invariant(source: &InsnArg) -> bool {
        matches!(source, InsnArg::Lit(_))
            || matches!(
                source,
                InsnArg::Wrapped(instruction)
                    if matches!(instruction.insn_type, InsnType::Const | InsnType::ConstStr)
            )
    }
}

pub(super) struct ExceptionalCopyPlacement<'a> {
    cfg: &'a CFG,
    variables: &'a CodeVariables,
    liveness: &'a SsaLiveness,
    statement_definitions: &'a BTreeSet<SsaVar>,
    required_phis: &'a BTreeSet<SsaVar>,
    semantic: &'a SemanticNode,
    contractions: &'a ControlContractions,
    regions: &'a RegionGraph,
    values: &'a SsaValueGraph,
    constants: &'a BTreeMap<SsaVar, InsnArg>,
}

impl<'a> ExceptionalCopyPlacement<'a> {
    pub(super) fn new(
        cfg: &'a CFG,
        variables: &'a CodeVariables,
        liveness: &'a SsaLiveness,
        statement_definitions: &'a BTreeSet<SsaVar>,
        required_phis: &'a BTreeSet<SsaVar>,
        semantic: &'a SemanticNode,
        contractions: &'a ControlContractions,
        regions: &'a RegionGraph,
        values: &'a SsaValueGraph,
        constants: &'a BTreeMap<SsaVar, InsnArg>,
    ) -> Self {
        Self {
            cfg,
            variables,
            liveness,
            statement_definitions,
            required_phis,
            semantic,
            contractions,
            regions,
            values,
            constants,
        }
    }

    pub(super) fn verify(
        &self,
        mut copies: CollectedPhiCopies,
    ) -> Result<PhiCopySet, SourceVariableError> {
        NormalCopyPlacement::new(self.cfg, self.variables, self.liveness, self.semantic)
            .apply(&mut copies.normal)?;
        ExceptionalIngressCopyPlacement::new(
            self.cfg,
            self.semantic,
            self.contractions,
            self.regions,
            self.values,
            self.statement_definitions,
            self.required_phis,
            self.constants,
        )
        .apply(&mut copies);
        let exceptional_effects = self.exceptional_effects(&copies.exceptional)?;
        let available = AvailableCopyAnalysis::analyze(
            self.cfg,
            self.variables,
            &copies.normal,
            &exceptional_effects,
            self.statement_definitions,
        )?;
        for (site, block_copies) in &mut copies.normal {
            let mut retained = Vec::with_capacity(block_copies.len());
            for copy in std::mem::take(block_copies) {
                let destination = self.code_variable(&copy.destination)?;
                let source = self.source(&copy.source)?;
                if !available.contains_before_site(*site, destination, &source) {
                    retained.push(copy);
                }
            }
            *block_copies = retained;
        }
        let mut assignments =
            BTreeMap::<StatementOrigin, BTreeMap<u32, ExceptionalAssignment>>::new();
        let mut throw_sites = BTreeMap::<BlockId, StatementOrigin>::new();
        let mut exceptional_spills = Vec::new();
        for (edge, edge_copies) in copies.exceptional {
            let throw_site = match throw_sites.get(&edge.predecessor) {
                Some(origin) => origin.clone(),
                None => {
                    let origin = self.throw_site(edge.predecessor)?;
                    throw_sites.insert(edge.predecessor, origin.clone());
                    origin
                }
            };
            let normal_live = self.normal_live_variables(edge.predecessor)?;
            let block_assignments = assignments.entry(throw_site.clone()).or_default();
            for copy in edge_copies {
                let destination = self.code_variable(&copy.destination)?;
                let source = self.source(&copy.source)?;
                if available.contains(edge.predecessor, destination, &source) {
                    continue;
                }
                if normal_live.contains(&destination) {
                    exceptional_spills.push(ExceptionalSpill {
                        origin: throw_site.clone(),
                        handler: edge.handler.require()?,
                        copy,
                    });
                    continue;
                }
                match block_assignments.entry(destination) {
                    std::collections::btree_map::Entry::Vacant(entry) => {
                        entry.insert(ExceptionalAssignment::Shared {
                            handler: edge.handler,
                            source,
                            copy,
                        });
                    }
                    std::collections::btree_map::Entry::Occupied(mut entry) => match entry.get() {
                        ExceptionalAssignment::Shared {
                            source: prior_source,
                            ..
                        } if *prior_source == source => {}
                        ExceptionalAssignment::Shared { .. } => {
                            if let Some((handler, prior_copy)) = entry.get_mut().spill() {
                                exceptional_spills.push(ExceptionalSpill {
                                    origin: throw_site.clone(),
                                    handler: handler.require()?,
                                    copy: prior_copy,
                                });
                            }
                            exceptional_spills.push(ExceptionalSpill {
                                origin: throw_site.clone(),
                                handler: edge.handler.require()?,
                                copy,
                            });
                        }
                        ExceptionalAssignment::Spilled => {
                            exceptional_spills.push(ExceptionalSpill {
                                origin: throw_site.clone(),
                                handler: edge.handler.require()?,
                                copy,
                            });
                        }
                    },
                }
            }
        }
        Ok(PhiCopySet {
            normal: copies.normal,
            exceptional: assignments
                .into_iter()
                .map(|(origin, assignments)| {
                    (
                        origin,
                        assignments
                            .into_values()
                            .filter_map(|assignment| match assignment {
                                ExceptionalAssignment::Shared { copy, .. } => Some(copy),
                                ExceptionalAssignment::Spilled => None,
                            })
                            .collect(),
                    )
                })
                .collect(),
            exceptional_spills,
            variable_types: copies.variable_types,
        })
    }

    fn exceptional_effects(
        &self,
        copies: &BTreeMap<ExceptionalEdge, Vec<EdgeCopy>>,
    ) -> Result<BTreeMap<BlockId, CopyFacts>, SourceVariableError> {
        let mut candidates = BTreeMap::<BlockId, BTreeMap<u32, Option<CopySource>>>::new();
        for (edge, edge_copies) in copies {
            let block = candidates.entry(edge.predecessor).or_default();
            for copy in edge_copies {
                let destination = self.code_variable(&copy.destination)?;
                let source = self.source(&copy.source)?;
                match block.entry(destination) {
                    std::collections::btree_map::Entry::Vacant(entry) => {
                        entry.insert(Some(source));
                    }
                    std::collections::btree_map::Entry::Occupied(mut entry) => {
                        if entry.get().as_ref() != Some(&source) {
                            entry.insert(None);
                        }
                    }
                }
            }
        }
        Ok(candidates
            .into_iter()
            .map(|(block, values)| {
                (
                    block,
                    values
                        .into_iter()
                        .filter_map(|(destination, source)| {
                            source.map(|source| (destination, source))
                        })
                        .collect(),
                )
            })
            .collect())
    }

    fn throw_site(&self, block: BlockId) -> Result<StatementOrigin, SourceVariableError> {
        let body = self
            .cfg
            .block(block)
            .ok_or(SourceVariableError::MissingBlock(block))?;
        let throwing = body
            .insns
            .iter()
            .enumerate()
            .filter(|(_, instruction)| !instruction.payload.edge_copy && instruction.can_throw())
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if throwing.as_slice() != [body.insns.len().saturating_sub(1)] {
            return Err(SourceVariableError::MissingThrowSite(block));
        }
        let instruction = body
            .insns
            .last()
            .ok_or(SourceVariableError::MissingThrowSite(block))?;
        Ok(StatementOrigin {
            block,
            instruction: instruction.id,
        })
    }

    fn normal_live_variables(
        &self,
        predecessor: BlockId,
    ) -> Result<BTreeSet<u32>, SourceVariableError> {
        let mut variables = BTreeSet::new();
        for value in self
            .liveness
            .normal_continuation_live(self.cfg, predecessor)?
        {
            variables.insert(
                self.variables
                    .variable_of(value)
                    .ok_or(SourceVariableError::MissingCodeVariable(value))?,
            );
        }
        Ok(variables)
    }

    fn code_variable(&self, register: &RegisterArg) -> Result<u32, SourceVariableError> {
        let variable =
            SsaVar::from_reg(register).ok_or(SourceVariableError::MissingRegisterIdentity)?;
        register
            .code_var
            .or_else(|| self.variables.variable_of(variable))
            .ok_or(SourceVariableError::MissingCodeVariable(variable))
    }

    fn source(&self, source: &InsnArg) -> Result<CopySource, SourceVariableError> {
        CopySource::from_arg(source, self.variables)
    }
}

impl PhiCopies {
    pub(super) fn collect(
        cfg: &CFG,
        required: &BTreeSet<SsaVar>,
        statement_definitions: &BTreeSet<SsaVar>,
        values: &SsaValueGraph,
        constants: &BTreeMap<SsaVar, InsnArg>,
        resolved_phi_types: &BTreeMap<SsaVar, ArgType>,
        contractions: &ControlContractions,
        regions: &RegionGraph,
        hierarchy: &dyn TypeHierarchy,
    ) -> Result<CollectedPhiCopies, SourceVariableError> {
        let mut normal = BTreeMap::<NormalCopySite, Vec<EdgeCopy>>::new();
        let mut exceptional = BTreeMap::<ExceptionalEdge, Vec<EdgeCopy>>::new();
        let mut variable_types = BTreeMap::<u32, (ArgType, SsaVar, BlockId)>::new();
        let type_lattice = SourceTypeLattice::new(hierarchy);
        let contracted_arguments =
            ContractedEdgeArguments::new(cfg, values, constants, contractions);
        let copy_resolver = SsaCopyResolver::new(cfg, values, statement_definitions);
        for (&successor, block) in &cfg.blocks {
            for phi in block
                .insns
                .iter()
                .filter(|instruction| instruction.insn_type == InsnType::Phi)
            {
                let result = phi
                    .result
                    .as_ref()
                    .ok_or(SourceVariableError::MissingPhiResult(successor))?;
                let result_value =
                    SsaVar::from_reg(result).ok_or(SourceVariableError::MissingRegisterIdentity)?;
                if !required.contains(&result_value) {
                    continue;
                }
                let destination_variable = result.code_var.ok_or_else(|| {
                    SsaVar::from_reg(result)
                        .map(SourceVariableError::MissingCodeVariable)
                        .unwrap_or(SourceVariableError::MissingRegisterIdentity)
                })?;
                let destination_type = resolved_phi_types.get(&result_value).cloned().ok_or(
                    TypeConstraintError::UnresolvedValue {
                        register: result.reg_num,
                        version: result.ssa_version,
                    },
                )?;
                match variable_types.entry(destination_variable) {
                    std::collections::btree_map::Entry::Vacant(entry) => {
                        entry.insert((destination_type.clone(), result_value, successor));
                    }
                    std::collections::btree_map::Entry::Occupied(mut entry) => {
                        let (current_type, current_value, current_block) = entry.get();
                        let joined = type_lattice
                            .join(current_type, &destination_type)
                            .ok_or_else(|| SourceVariableError::ConflictingPhiVariable {
                                variable: destination_variable,
                                left_value: *current_value,
                                left_block: *current_block,
                                left_type: current_type.clone(),
                                right_value: result_value,
                                right_block: successor,
                                right_type: destination_type.clone(),
                            })?;
                        entry.insert((joined, result_value, successor));
                    }
                }
                for argument in contracted_arguments.resolve_all(successor, phi)? {
                    let Some(value) = argument.value.into_explicit() else {
                        continue;
                    };
                    let mut value = copy_resolver.resolve(value);
                    if argument.edge_kind == crate::ir::EdgeKind::Exception
                        && value
                            .as_register()
                            .is_some_and(|source| source.code_var == Some(destination_variable))
                    {
                        if let Some(resolved) = copy_resolver.resolve_for_edge(
                            value.clone(),
                            argument.predecessor,
                            argument.edge_kind,
                            constants,
                        ) {
                            value = resolved;
                        }
                    }
                    let Some(source) = Self::copy_source_arg(
                        value,
                        destination_variable,
                        &destination_type,
                        constants,
                    ) else {
                        continue;
                    };
                    let predecessors = (argument.edge_kind == crate::ir::EdgeKind::Exception)
                        .then(|| regions.exceptional_rethrow_sources(argument.predecessor))
                        .flatten()
                        .cloned()
                        .unwrap_or_else(|| BTreeSet::from([argument.predecessor]));
                    for predecessor in predecessors {
                        let destination = result.clone();
                        let source = source.clone();
                        if argument.edge_kind == crate::ir::EdgeKind::Exception
                            && !Self::is_unconditional_throw_edge(cfg, predecessor, argument.entry)
                        {
                            exceptional
                                .entry(ExceptionalEdge {
                                    predecessor,
                                    handler: ExceptionHandlerTarget::resolve(
                                        argument.entry,
                                        contractions,
                                        regions,
                                    ),
                                })
                                .or_default()
                                .push(EdgeCopy {
                                    destination,
                                    source,
                                });
                        } else {
                            let copy_site = if argument.edge_kind == crate::ir::EdgeKind::Exception
                            {
                                NormalCopySite::Block(predecessor)
                            } else {
                                let Some(copy_site) = contractions.normal_copy_site(
                                    cfg,
                                    predecessor,
                                    argument.entry,
                                    successor,
                                ) else {
                                    let targets =
                                        cfg.normal_successors(predecessor).collect::<BTreeSet<_>>();
                                    return Err(SourceVariableError::UnsplitNormalEdge {
                                        predecessor,
                                        successor: argument.entry,
                                        targets: targets.into_iter().collect(),
                                    });
                                };
                                copy_site
                            };
                            normal.entry(copy_site).or_default().push(EdgeCopy {
                                destination,
                                source,
                            });
                        }
                    }
                }
            }
        }
        Ok(CollectedPhiCopies {
            normal,
            exceptional,
            variable_types: variable_types
                .into_iter()
                .map(|(variable, (ty, _, _))| (variable, ty))
                .collect(),
        })
    }

    fn is_unconditional_throw_edge(cfg: &CFG, source: BlockId, target: BlockId) -> bool {
        let edges = cfg.successors_with_kind(source);
        if edges != [(target, crate::ir::EdgeKind::Exception)] {
            return false;
        }
        cfg.block(source)
            .and_then(|block| {
                block
                    .insns
                    .iter()
                    .rev()
                    .find(|instruction| !instruction.payload.edge_copy)
            })
            .is_some_and(|instruction| instruction.insn_type == InsnType::Throw)
    }

    fn copy_source(
        source: RegisterArg,
        source_value: SsaVar,
        destination_variable: u32,
        destination_type: &ArgType,
        constants: &BTreeMap<SsaVar, InsnArg>,
    ) -> Option<InsnArg> {
        if source.code_var == Some(destination_variable) {
            return None;
        }
        Some(
            Self::canonical_constant(constants, source_value)
                .and_then(|value| Self::typed_constant(value, destination_type))
                .unwrap_or(InsnArg::Reg(source)),
        )
    }

    fn copy_source_arg(
        source: InsnArg,
        destination_variable: u32,
        destination_type: &ArgType,
        constants: &BTreeMap<SsaVar, InsnArg>,
    ) -> Option<InsnArg> {
        match source {
            InsnArg::Reg(register) => {
                let source_value = SsaVar::from_reg(&register)?;
                Self::copy_source(
                    register,
                    source_value,
                    destination_variable,
                    destination_type,
                    constants,
                )
            }
            constant => Self::typed_constant(&constant, destination_type),
        }
    }

    fn canonical_constant(
        values: &BTreeMap<SsaVar, InsnArg>,
        mut value: SsaVar,
    ) -> Option<&InsnArg> {
        let mut visited = BTreeSet::new();
        while visited.insert(value) {
            let canonical = values.get(&value)?;
            match canonical {
                InsnArg::Reg(register) => {
                    value = SsaVar::from_reg(register)?;
                }
                InsnArg::Lit(_) => return Some(canonical),
                InsnArg::Wrapped(instruction)
                    if matches!(instruction.insn_type, InsnType::Const | InsnType::ConstStr) =>
                {
                    return Some(canonical);
                }
                InsnArg::Wrapped(_) => return None,
            }
        }
        None
    }

    fn typed_constant(value: &InsnArg, ty: &ArgType) -> Option<InsnArg> {
        match value {
            InsnArg::Lit(literal) => Some(InsnArg::lit(literal.value, ty.clone())),
            InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::Const => {
                let value = instruction.args.first()?.as_literal()?.value;
                Some(InsnArg::lit(value, ty.clone()))
            }
            InsnArg::Wrapped(instruction) if instruction.insn_type == InsnType::ConstStr => {
                let mut instruction = (**instruction).clone();
                if let Some(result) = &mut instruction.result {
                    result.ty = ty.clone();
                }
                Some(InsnArg::wrap(instruction))
            }
            InsnArg::Reg(_) | InsnArg::Wrapped(_) => None,
        }
    }

    fn sequentialize(
        mut copies: Vec<EdgeCopy>,
        next_variable: &mut u32,
        types: &mut SourceTypeEnvironment,
    ) -> Result<Vec<SemanticStatement>, SourceVariableError> {
        copies.retain(|copy| {
            copy.destination.code_var
                != copy
                    .source
                    .as_register()
                    .and_then(|register| register.code_var)
        });
        let mut statements = Vec::new();
        while !copies.is_empty() {
            let sources = copies
                .iter()
                .filter_map(|copy| {
                    copy.source
                        .as_register()
                        .and_then(|register| register.code_var)
                })
                .collect::<BTreeSet<_>>();
            if let Some(index) = copies.iter().position(|copy| {
                copy.destination
                    .code_var
                    .is_some_and(|destination| !sources.contains(&destination))
            }) {
                let copy = copies.remove(index);
                statements.push(Self::statement(copy.destination, copy.source)?);
                continue;
            }

            let source = copies
                .first()
                .and_then(|copy| copy.source.as_register())
                .cloned()
                .ok_or(SourceVariableError::EmptyParallelCopyCycle)?;
            let source_variable = source.code_var.ok_or_else(|| {
                SsaVar::from_reg(&source)
                    .map(SourceVariableError::MissingCodeVariable)
                    .unwrap_or(SourceVariableError::MissingRegisterIdentity)
            })?;
            let temporary_variable = *next_variable;
            *next_variable += 1;
            let temporary_type = types.register_type(&source)?.clone();
            let mut temporary = RegisterArg::new(source.reg_num, temporary_type.clone());
            temporary.code_var = Some(temporary_variable);
            types.bind_variable(temporary_variable, temporary_type)?;
            statements.push(Self::statement(temporary.clone(), InsnArg::Reg(source))?);
            for copy in &mut copies {
                if copy
                    .source
                    .as_register()
                    .and_then(|register| register.code_var)
                    == Some(source_variable)
                {
                    copy.source = InsnArg::Reg(temporary.clone());
                }
            }
        }
        Ok(statements)
    }

    fn statement(
        destination: RegisterArg,
        source: InsnArg,
    ) -> Result<SemanticStatement, SourceVariableError> {
        let mut instruction = InsnNode::mov(destination, source);
        instruction.payload.edge_copy = true;
        Ok(SemanticStatement::instruction(instruction)?)
    }
}

pub(super) struct PhiTypeAnalysis;

impl PhiTypeAnalysis {
    pub(super) fn solve(
        cfg: &CFG,
        required: &BTreeSet<SsaVar>,
        values: &SsaValueGraph,
        types: &SsaTypeEnvironment,
        constants: &BTreeMap<SsaVar, InsnArg>,
        hierarchy: &dyn TypeHierarchy,
    ) -> Result<BTreeMap<SsaVar, ArgType>, TypeConstraintError> {
        let mut phis = BTreeMap::<SsaVar, (&InsnNode, RegisterArg)>::new();
        let mut consumers = BTreeMap::<SsaVar, BTreeSet<SsaVar>>::new();
        for block in cfg.blocks.values() {
            for phi in block
                .insns
                .iter()
                .filter(|instruction| instruction.insn_type == InsnType::Phi)
            {
                let Some(result) = phi.result.as_ref() else {
                    continue;
                };
                let Some(result_value) = SsaVar::from_reg(result) else {
                    continue;
                };
                if !required.contains(&result_value) {
                    continue;
                }
                phis.insert(result_value, (phi, result.clone()));
                for input in &phi.args {
                    if let Some(input) = input.as_register().and_then(SsaVar::from_reg) {
                        consumers.entry(input).or_default().insert(result_value);
                    }
                }
            }
        }

        let mut resolved = BTreeMap::<SsaVar, ArgType>::new();
        let mut pending = phis.keys().copied().collect::<VecDeque<_>>();
        let mut queued = phis.keys().copied().collect::<BTreeSet<_>>();
        while let Some(value) = pending.pop_front() {
            queued.remove(&value);
            let Some((phi, result)) = phis.get(&value) else {
                continue;
            };
            let ty = PhiTypeResolver::new(cfg, values, types, constants, hierarchy, &resolved)
                .resolve(phi, result)?;
            if resolved.get(&value) == Some(&ty) {
                continue;
            }
            resolved.insert(value, ty);
            for consumer in consumers.get(&value).into_iter().flatten() {
                if queued.insert(*consumer) {
                    pending.push_back(*consumer);
                }
            }
        }
        Ok(resolved)
    }
}

struct PhiTypeResolver<'a> {
    cfg: &'a CFG,
    values: &'a SsaValueGraph,
    types: &'a SsaTypeEnvironment,
    constants: &'a BTreeMap<SsaVar, InsnArg>,
    lattice: SourceTypeLattice<'a>,
    resolved: &'a BTreeMap<SsaVar, ArgType>,
}

impl<'a> PhiTypeResolver<'a> {
    fn new(
        cfg: &'a CFG,
        values: &'a SsaValueGraph,
        types: &'a SsaTypeEnvironment,
        constants: &'a BTreeMap<SsaVar, InsnArg>,
        hierarchy: &'a dyn TypeHierarchy,
        resolved: &'a BTreeMap<SsaVar, ArgType>,
    ) -> Self {
        Self {
            cfg,
            values,
            types,
            constants,
            lattice: SourceTypeLattice::new(hierarchy),
            resolved,
        }
    }

    fn resolve(
        &self,
        phi: &InsnNode,
        result: &RegisterArg,
    ) -> Result<ArgType, TypeConstraintError> {
        let (known, unresolved) = match self.types.register_type(result) {
            Ok(ty) => (Some(ty.clone()), None),
            Err(error) => (None, Some(error)),
        };
        let inputs = phi
            .args
            .iter()
            .map(|input| self.input_fact(input))
            .collect::<Option<Vec<_>>>();
        let Some(inputs) = inputs else {
            return known.ok_or_else(|| unresolved.expect("missing type error"));
        };
        if let Some(known) = known.as_ref().filter(|known| known.is_primitive()) {
            let requires_widening = inputs.iter().any(|input| {
                input.literal.is_some_and(|value| {
                    Self::literal_widening_type(input, value).is_some()
                        && !Self::literal_fits(value, known)
                })
            });
            if !requires_widening {
                return Ok(known.clone());
            }
        }
        let resolved = self.resolve_inputs(&inputs);
        resolved
            .or(known)
            .ok_or_else(|| unresolved.expect("missing type error"))
    }

    fn resolve_inputs(&self, inputs: &[PhiInputType]) -> Option<ArgType> {
        let mut candidate = None;
        for inferred in inputs
            .iter()
            .filter(|input| input.literal.is_none())
            .filter_map(|input| input.inferred.as_ref())
        {
            candidate = Some(match candidate {
                Some(ref current) => self.lattice.join(current, inferred)?,
                None => inferred.clone(),
            });
        }
        if candidate.is_none() {
            candidate = inputs
                .iter()
                .filter(|input| input.literal.is_none())
                .filter_map(|input| input.physical.clone())
                .next()
                .or_else(|| {
                    inputs
                        .iter()
                        .filter_map(|input| input.physical.clone())
                        .next()
                });
        }
        for input in inputs {
            if let Some(value) = input.literal {
                if candidate
                    .as_ref()
                    .is_some_and(|ty| Self::literal_fits(value, ty))
                {
                    continue;
                }
                if let Some(widened) = Self::literal_widening_type(input, value) {
                    candidate = Some(match candidate {
                        Some(ref current) => self.lattice.join(current, &widened)?,
                        None => widened,
                    });
                    continue;
                }
            } else if input.inferred.is_some() {
                continue;
            }
            if let Some(physical) = input.physical.as_ref() {
                candidate = Some(match candidate {
                    Some(ref current) => self.lattice.join(current, physical)?,
                    None => physical.clone(),
                });
            }
        }
        candidate
    }

    fn literal_widening_type(input: &PhiInputType, value: i64) -> Option<ArgType> {
        let physical = input.inferred.as_ref().or(input.physical.as_ref())?;
        match physical.as_primitive()? {
            crate::ir::PrimitiveType::Boolean
            | crate::ir::PrimitiveType::Byte
            | crate::ir::PrimitiveType::Short
            | crate::ir::PrimitiveType::Char
            | crate::ir::PrimitiveType::Int => Some(if i32::try_from(value).is_ok() {
                ArgType::INT
            } else {
                ArgType::LONG
            }),
            crate::ir::PrimitiveType::Long => Some(ArgType::LONG),
            crate::ir::PrimitiveType::Float
            | crate::ir::PrimitiveType::Double
            | crate::ir::PrimitiveType::Void
            | crate::ir::PrimitiveType::Object
            | crate::ir::PrimitiveType::Array => None,
        }
    }

    fn input_fact(&self, input: &InsnArg) -> Option<PhiInputType> {
        let value = input.as_register().and_then(SsaVar::from_reg)?;
        Some(PhiInputType {
            inferred: self
                .resolved
                .get(&value)
                .cloned()
                .or_else(|| self.types.argument_type(input).ok().cloned()),
            physical: self.physical_type(value),
            literal: self.constant_value(value),
        })
    }

    fn physical_type(&self, mut value: SsaVar) -> Option<ArgType> {
        let mut visited = BTreeSet::new();
        while visited.insert(value) {
            if let Some(ty) = self.resolved.get(&value) {
                return Some(ty.clone());
            }
            if let Some(constant) = self.constants.get(&value) {
                if let Some(ty) = constant.declared_type().filter(|ty| ty.is_known()) {
                    return Some(ty.clone());
                }
            }
            let position = self.values.value(value)?.definition?;
            let instruction = self.cfg.block(position.block)?.insns.get(position.index)?;
            if let Some(ty) = instruction
                .result
                .as_ref()
                .map(|result| &result.ty)
                .filter(|ty| ty.is_known())
            {
                return Some(ty.clone());
            }
            if instruction.insn_type != InsnType::Move {
                return instruction
                    .args
                    .first()
                    .and_then(InsnArg::declared_type)
                    .filter(|ty| ty.is_known())
                    .cloned();
            }
            let source = instruction.args.first()?;
            if let Some(ty) = source.declared_type().filter(|ty| ty.is_known()) {
                return Some(ty.clone());
            }
            value = source.as_register().and_then(SsaVar::from_reg)?;
        }
        None
    }

    fn constant_value(&self, mut value: SsaVar) -> Option<i64> {
        let mut visited = BTreeSet::new();
        while visited.insert(value) {
            if let Some(constant) = self.constants.get(&value) {
                return constant.literal_value();
            }
            let position = self.values.value(value)?.definition?;
            let instruction = self.cfg.block(position.block)?.insns.get(position.index)?;
            match instruction.insn_type {
                InsnType::Const => return instruction.args.first()?.literal_value(),
                InsnType::Move => {
                    value = instruction
                        .args
                        .first()
                        .and_then(InsnArg::as_register)
                        .and_then(SsaVar::from_reg)?;
                }
                _ => return None,
            }
        }
        None
    }

    fn literal_fits(value: i64, ty: &ArgType) -> bool {
        match ty.as_primitive() {
            Some(crate::ir::PrimitiveType::Boolean) => matches!(value, 0 | 1),
            Some(crate::ir::PrimitiveType::Byte) => i8::try_from(value).is_ok(),
            Some(crate::ir::PrimitiveType::Short) => i16::try_from(value).is_ok(),
            Some(crate::ir::PrimitiveType::Char) => u16::try_from(value).is_ok(),
            Some(crate::ir::PrimitiveType::Int) => i32::try_from(value).is_ok(),
            Some(crate::ir::PrimitiveType::Long) => true,
            Some(crate::ir::PrimitiveType::Float) => i32::try_from(value).is_ok(),
            Some(crate::ir::PrimitiveType::Double) => true,
            Some(crate::ir::PrimitiveType::Void) => false,
            Some(crate::ir::PrimitiveType::Object | crate::ir::PrimitiveType::Array) => value == 0,
            None => matches!(ty, ArgType::Object(_) | ArgType::Array(_)) && value == 0,
        }
    }
}

#[derive(Debug)]
struct PhiInputType {
    inferred: Option<ArgType>,
    physical: Option<ArgType>,
    literal: Option<i64>,
}

pub(super) struct PhiLowering {
    normal: NormalCopies,
    exceptional: BTreeMap<InstructionId, (BlockId, Vec<SemanticStatement>)>,
    terminal_exceptional: BTreeMap<BlockId, InstructionId>,
    handler_entries: BTreeMap<BlockId, Vec<SemanticStatement>>,
    handler_regions: BTreeMap<RegionId, BlockId>,
    handler_blocks: BTreeSet<BlockId>,
    semantic_blocks: BTreeSet<BlockId>,
    repeated_semantic_blocks: BTreeSet<BlockId>,
    statement_blocks: BTreeSet<BlockId>,
    materialized_instructions: BTreeSet<InstructionId>,
    placed_exceptional: BTreeSet<InstructionId>,
    seen: BTreeSet<BlockId>,
    next_variable: u32,
}

impl PhiLowering {
    pub(super) fn new(
        cfg: &CFG,
        copies: PhiCopySet,
        mut next_variable: u32,
        types: &mut SourceTypeEnvironment,
        hierarchy: &dyn TypeHierarchy,
        regions: &RegionGraph,
    ) -> Result<Self, SourceVariableError> {
        let PhiCopySet {
            normal: normal_copies,
            exceptional: mut exceptional_copies,
            exceptional_spills,
            variable_types,
        } = copies;
        let canonical_sites = EquivalentCopySites::analyze(cfg, regions, &normal_copies);
        for (&variable, ty) in &variable_types {
            types.merge_variable(variable, ty.clone(), hierarchy)?;
        }
        let mut normal = BTreeMap::new();
        for (block, copies) in normal_copies {
            let statements = PhiCopies::sequentialize(copies, &mut next_variable, types)?;
            if !statements.is_empty() {
                normal.insert(block, statements);
            }
        }

        let mut spill_variables =
            BTreeMap::<(ExceptionHandlerPort, u32), (RegisterArg, RegisterArg)>::new();
        for spill in exceptional_spills {
            if regions.is_elided(&spill.origin) {
                continue;
            }
            let destination_variable = spill.copy.destination.code_var.ok_or_else(|| {
                SsaVar::from_reg(&spill.copy.destination)
                    .map(SourceVariableError::MissingCodeVariable)
                    .unwrap_or(SourceVariableError::MissingRegisterIdentity)
            })?;
            let key = (spill.handler, destination_variable);
            let temporary = if let Some((_, temporary)) = spill_variables.get(&key) {
                temporary.clone()
            } else {
                let temporary_type = variable_types
                    .get(&destination_variable)
                    .cloned()
                    .unwrap_or_else(|| spill.copy.destination.ty.clone());
                let temporary_variable = next_variable;
                next_variable += 1;
                let mut temporary =
                    RegisterArg::new(spill.copy.destination.reg_num, temporary_type.clone());
                temporary.code_var = Some(temporary_variable);
                types.bind_variable(temporary_variable, temporary_type)?;
                spill_variables.insert(key, (spill.copy.destination.clone(), temporary.clone()));
                temporary
            };
            exceptional_copies
                .entry(spill.origin)
                .or_default()
                .push(EdgeCopy {
                    destination: temporary,
                    source: spill.copy.source,
                });
        }

        let mut exceptional = BTreeMap::new();
        for (origin, copies) in exceptional_copies {
            if regions.is_elided(&origin) {
                continue;
            }
            let mut statements = PhiCopies::sequentialize(copies, &mut next_variable, types)?;
            for statement in &mut statements {
                statement.origin = Some(origin.clone());
            }
            if !statements.is_empty() {
                exceptional.insert(origin.instruction, (origin.block, statements));
            }
        }
        let terminal_exceptional = cfg
            .blocks
            .values()
            .filter_map(|block| {
                let terminal = block.terminator()?;
                exceptional
                    .contains_key(&terminal.id)
                    .then_some((block.id, terminal.id))
            })
            .collect();
        let mut handler_entry_copies = BTreeMap::<BlockId, Vec<EdgeCopy>>::new();
        for ((handler, _), (destination, temporary)) in spill_variables {
            handler_entry_copies
                .entry(handler.entry)
                .or_default()
                .push(EdgeCopy {
                    destination,
                    source: InsnArg::Reg(temporary),
                });
        }
        let mut handler_entries = BTreeMap::new();
        for (handler, copies) in handler_entry_copies {
            let statements = PhiCopies::sequentialize(copies, &mut next_variable, types)?;
            if !statements.is_empty() {
                handler_entries.insert(handler, statements);
            }
        }
        let handler_regions = regions
            .tree()
            .regions()
            .filter(|region| regions.is_exception_handler(region.id))
            .filter_map(|region| {
                region
                    .entry
                    .or_else(|| region.kind.continuation())
                    .map(|entry| (region.id, entry))
            })
            .collect::<BTreeMap<_, _>>();
        let handler_blocks = handler_regions.values().copied().collect();
        Ok(Self {
            normal: NormalCopies::new(normal, canonical_sites),
            exceptional,
            terminal_exceptional,
            handler_entries,
            handler_regions,
            handler_blocks,
            semantic_blocks: BTreeSet::new(),
            repeated_semantic_blocks: BTreeSet::new(),
            statement_blocks: BTreeSet::new(),
            materialized_instructions: BTreeSet::new(),
            placed_exceptional: BTreeSet::new(),
            seen: BTreeSet::new(),
            next_variable,
        })
    }

    pub(super) fn next_variable(&self) -> u32 {
        self.next_variable
    }

    pub(super) fn apply(mut self, root: &mut SemanticNode) -> Result<(), SourceVariableError> {
        self.semantic_blocks = SemanticBlocks::collect(root);
        self.repeated_semantic_blocks = SemanticBlockOccurrences::repeated(root);
        self.statement_blocks = StatementBlocks::collect(root);
        self.materialized_instructions =
            EvaluationInstructions::of_node(root).into_iter().collect();
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = self.fold_node(body)?;
        if let Some(site) = self.normal.first_unplaced() {
            return Err(match site {
                NormalCopySite::Block(block) => SourceVariableError::MissingSemanticBlock(block),
                NormalCopySite::Edge(edge) => SourceVariableError::MissingSemanticEdge(edge),
            });
        }
        if let Some((instruction, (block, _))) = self
            .exceptional
            .iter()
            .find(|(instruction, _)| !self.placed_exceptional.contains(instruction))
        {
            return Err(SourceVariableError::MissingExceptionalCopySite {
                block: *block,
                instruction: *instruction,
            });
        }
        if let Some(block) = self
            .handler_entries
            .keys()
            .find(|block| !self.seen.contains(block))
            .copied()
        {
            return Err(SourceVariableError::MissingHandlerEntry(block));
        }
        LoopExitCopyPlacement::apply(root)?;
        Ok(())
    }
}

impl SemanticFolder for PhiLowering {
    type Error = SourceVariableError;

    fn finish_node(&mut self, node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        match node {
            SemanticNode::BasicBlock(block) => self.lower_block(block),
            SemanticNode::Leave(leave) => self.lower_leave(leave),
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => {
                let prefix =
                    self.exceptional_prefix(EvaluationInstructions::of_predicate(&condition));
                Ok(SemanticNode::sequence([
                    prefix,
                    SemanticNode::If {
                        condition,
                        then_node,
                        else_node,
                    },
                ]))
            }
            SemanticNode::Loop {
                control,
                header,
                kind,
                mut test,
                body,
            } => {
                let prefix =
                    self.exceptional_prefix(EvaluationInstructions::of_predicate(&test.condition));
                test.setup = Box::new(SemanticNode::sequence([*test.setup, prefix]));
                Ok(SemanticNode::Loop {
                    control,
                    header,
                    kind,
                    test,
                    body,
                })
            }
            SemanticNode::Switch {
                region,
                selector,
                cases,
            } => {
                let prefix =
                    self.exceptional_prefix(EvaluationInstructions::of_expression(&selector));
                Ok(SemanticNode::sequence([
                    prefix,
                    SemanticNode::Switch {
                        region,
                        selector,
                        cases,
                    },
                ]))
            }
            SemanticNode::Synchronized {
                region,
                lock,
                method,
                body,
            } => {
                let prefix = self.exceptional_prefix(EvaluationInstructions::of_expression(&lock));
                Ok(SemanticNode::sequence([
                    prefix,
                    SemanticNode::Synchronized {
                        region,
                        lock,
                        method,
                        body,
                    },
                ]))
            }
            SemanticNode::ForEach {
                control,
                variable,
                iterable,
                body,
            } => {
                let prefix =
                    self.exceptional_prefix(EvaluationInstructions::of_expression(&iterable));
                Ok(SemanticNode::sequence([
                    prefix,
                    SemanticNode::ForEach {
                        control,
                        variable,
                        iterable,
                        body,
                    },
                ]))
            }
            SemanticNode::Try {
                region,
                body,
                catches,
                finally,
            } => self.lower_try(region, *body, catches, finally),
            node => Ok(node),
        }
    }
}

impl PhiLowering {
    fn exceptional_prefix(
        &mut self,
        instructions: impl IntoIterator<Item = InstructionId>,
    ) -> SemanticNode {
        let mut resolved = BTreeSet::new();
        let mut blocks = Vec::new();
        for instruction in instructions {
            if !resolved.insert(instruction) {
                continue;
            }
            let Some((origin, copies)) = self.exceptional.get(&instruction) else {
                continue;
            };
            let origin = *origin;
            let copies = copies.clone();
            self.placed_exceptional.insert(instruction);
            if !copies.is_empty() {
                blocks.push(SemanticNode::BasicBlock(SemanticBlock {
                    id: origin,
                    statements: copies,
                }));
            }
        }
        SemanticNode::sequence(blocks)
    }

    fn lower_block(
        &mut self,
        mut block: SemanticBlock,
    ) -> Result<SemanticNode, SourceVariableError> {
        self.seen.insert(block.id);
        let owns_normal_copies =
            !block.statements.is_empty() || !self.statement_blocks.contains(&block.id);
        let mut statements = if self.handler_blocks.contains(&block.id) {
            Vec::new()
        } else {
            self.handler_entries.remove(&block.id).unwrap_or_default()
        };
        let mut resolved = BTreeSet::new();
        for statement in block.statements {
            for instruction in EvaluationInstructions::of_statement(&statement) {
                if let Some((_, copies)) = self.exceptional.get(&instruction) {
                    if resolved.insert(instruction) {
                        self.placed_exceptional.insert(instruction);
                        statements.extend(copies.iter().cloned());
                    }
                }
            }
            statements.push(statement);
        }
        block.statements = statements;
        if owns_normal_copies {
            let site = NormalCopySite::Block(block.id);
            let repeats_semantically =
                !block.statements.is_empty() || self.repeated_semantic_blocks.contains(&block.id);
            let copies = self
                .normal
                .place_block_occurrence(site, repeats_semantically);
            if let Some(statements) = copies {
                block.statements.extend(statements);
            }
        }
        Ok(SemanticNode::BasicBlock(block))
    }

    fn lower_leave(
        &mut self,
        mut leave: crate::ir::SemanticLeave,
    ) -> Result<SemanticNode, SourceVariableError> {
        let condition_prefix = leave
            .condition
            .as_ref()
            .map(EvaluationInstructions::of_predicate)
            .map(|instructions| self.exceptional_prefix(instructions))
            .unwrap_or(SemanticNode::Empty);
        let value_prefix = leave
            .value()
            .map(EvaluationInstructions::of_expression)
            .map(|instructions| self.exceptional_prefix(instructions))
            .unwrap_or(SemanticNode::Empty);
        let terminal_prefix = leave
            .origin
            .and_then(|origin| {
                terminal_exceptional_fallback(
                    &self.terminal_exceptional,
                    &self.materialized_instructions,
                    origin,
                )
            })
            .map(|instruction| self.exceptional_prefix([instruction]))
            .unwrap_or(SemanticNode::Empty);
        let normal_prefix = leave
            .origin
            .and_then(|origin| {
                self.seen.insert(origin);
                let mut sites = Vec::with_capacity(3);
                if let Some(edge) = leave.edge {
                    sites.push(NormalCopySite::Edge(edge));
                    // A surviving target block owns its block-local copies.
                    // Lifting those copies onto this leave would execute them
                    // once before the transfer and again when the target is
                    // lowered. Only absorb target copies when structural
                    // recovery removed the target's semantic identity.
                    if !self.semantic_blocks.contains(&edge.target) {
                        sites.push(NormalCopySite::Block(edge.target));
                    }
                }
                sites.push(NormalCopySite::Block(origin));
                self.normal.place_once_on_path(sites).map(|statements| {
                    SemanticNode::BasicBlock(SemanticBlock {
                        id: origin,
                        statements,
                    })
                })
            })
            .unwrap_or(SemanticNode::Empty);
        let Some(condition) = leave.condition.take() else {
            return Ok(SemanticNode::sequence([
                condition_prefix,
                value_prefix,
                terminal_prefix,
                normal_prefix,
                SemanticNode::Leave(leave),
            ]));
        };

        let taken = SemanticNode::sequence([
            value_prefix,
            terminal_prefix,
            normal_prefix,
            SemanticNode::Leave(leave),
        ]);
        Ok(SemanticNode::sequence([
            condition_prefix,
            SemanticNode::If {
                condition: crate::ir::SemanticOperand::new(condition),
                then_node: Box::new(taken),
                else_node: None,
            },
        ]))
    }

    fn lower_try(
        &mut self,
        region: RegionId,
        body: SemanticNode,
        mut catches: Vec<crate::ir::SemanticCatch>,
        finally: Option<crate::ir::SemanticFinally>,
    ) -> Result<SemanticNode, SourceVariableError> {
        for catch in &mut catches {
            let Some(entry) = self.handler_regions.get(&catch.region).copied() else {
                continue;
            };
            let Some(statements) = self.handler_entries.remove(&entry) else {
                continue;
            };
            self.seen.insert(entry);
            catch.body = SemanticNode::sequence([
                SemanticNode::BasicBlock(SemanticBlock {
                    id: entry,
                    statements,
                }),
                std::mem::replace(&mut catch.body, SemanticNode::Empty),
            ]);
        }
        Ok(SemanticNode::Try {
            region,
            body: Box::new(body),
            catches,
            finally,
        })
    }
}

fn terminal_exceptional_fallback(
    terminal_exceptional: &BTreeMap<BlockId, InstructionId>,
    materialized_instructions: &BTreeSet<InstructionId>,
    origin: BlockId,
) -> Option<InstructionId> {
    terminal_exceptional
        .get(&origin)
        .copied()
        .filter(|instruction| !materialized_instructions.contains(instruction))
}

#[derive(Default)]
struct SemanticBlocks {
    blocks: BTreeSet<BlockId>,
}

impl SemanticBlocks {
    fn collect(root: &SemanticNode) -> BTreeSet<BlockId> {
        let mut collector = Self::default();
        collector.visit_node(root);
        collector.blocks
    }
}

impl SemanticVisitor for SemanticBlocks {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::BasicBlock(block) = node {
            self.blocks.insert(block.id);
        }
    }
}

#[derive(Default)]
struct SemanticBlockOccurrences {
    counts: BTreeMap<BlockId, usize>,
}

impl SemanticBlockOccurrences {
    fn repeated(root: &SemanticNode) -> BTreeSet<BlockId> {
        let mut collector = Self::default();
        collector.visit_node(root);
        collector
            .counts
            .into_iter()
            .filter_map(|(block, count)| (count > 1).then_some(block))
            .collect()
    }
}

impl SemanticVisitor for SemanticBlockOccurrences {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::BasicBlock(block) = node {
            *self.counts.entry(block.id).or_default() += 1;
        }
    }
}

#[derive(Default)]
struct StatementBlocks {
    blocks: BTreeSet<BlockId>,
}

impl StatementBlocks {
    fn collect(root: &SemanticNode) -> BTreeSet<BlockId> {
        let mut collector = Self::default();
        collector.visit_node(root);
        collector.blocks
    }
}

impl SemanticVisitor for StatementBlocks {
    fn enter_node(&mut self, node: &SemanticNode) {
        if let SemanticNode::BasicBlock(block) = node {
            if !block.statements.is_empty() {
                self.blocks.insert(block.id);
            }
        }
    }
}

#[derive(Default)]
struct EvaluationInstructions {
    instructions: Vec<InstructionId>,
}

impl EvaluationInstructions {
    fn of_node(node: &SemanticNode) -> Vec<InstructionId> {
        let mut collector = Self::default();
        collector.visit_node(node);
        collector.instructions
    }

    fn of_statement(statement: &crate::ir::SemanticStatement) -> Vec<InstructionId> {
        if let Some(operation) = statement.instruction_ref() {
            return Self::of_operation(operation);
        }
        statement
            .value()
            .map(Self::of_expression)
            .unwrap_or_default()
    }

    fn of_operation(operation: &crate::ir::SemanticOperation) -> Vec<InstructionId> {
        let mut collector = Self::default();
        collector.visit_operation(operation);
        collector.instructions
    }

    fn of_expression(expression: &crate::ir::SemanticExpression) -> Vec<InstructionId> {
        let mut collector = Self::default();
        collector.visit_expression(expression);
        collector.instructions
    }

    fn of_predicate(predicate: &crate::ir::SemanticPredicate) -> Vec<InstructionId> {
        let mut collector = Self::default();
        collector.visit_predicate(predicate);
        collector.instructions
    }
}

impl SemanticVisitor for EvaluationInstructions {
    fn enter_operation(&mut self, operation: &crate::ir::SemanticOperation) {
        self.instructions.push(operation.id);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::analysis::ClassHierarchyIndex;
    use crate::ir::{
        Block, CatchRegion, EdgeKind, InsnNode, InsnType, LiteralArg, RegionEdge, RegionKind,
        RegionTree, SemanticExpression,
    };

    fn source_variable(register: u32, version: u32, variable: u32) -> RegisterArg {
        let mut value = RegisterArg::new_ssa(register, version, ArgType::INT);
        value.code_var = Some(variable);
        value
    }

    #[test]
    fn detached_handler_continuation_is_an_exception_port() {
        let continuation = BlockId::new(7);
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let protected = tree
            .add_child(root, RegionKind::Try, Some(BlockId::new(6)))
            .expect("try region");
        let handler = tree
            .add_child(
                protected,
                RegionKind::Catch(CatchRegion {
                    exception_types: vec![ArgType::throwable()],
                    exception_value: None,
                    continuation: Some(continuation),
                }),
                None,
            )
            .expect("detached handler");

        assert_eq!(
            ExceptionHandlerPort::detached_continuation(continuation, &tree, [handler]),
            Some(ExceptionHandlerPort {
                region: handler,
                entry: continuation,
            })
        );
    }

    #[test]
    fn ambiguous_detached_handler_continuation_is_not_selected() {
        let continuation = BlockId::new(7);
        let mut tree = RegionTree::new(Some(BlockId::new(0)));
        let root = tree.root();
        let protected = tree
            .add_child(root, RegionKind::Try, Some(BlockId::new(6)))
            .expect("try region");
        let handler = |tree: &mut RegionTree| {
            tree.add_child(
                protected,
                RegionKind::Catch(CatchRegion {
                    exception_types: vec![ArgType::throwable()],
                    exception_value: None,
                    continuation: Some(continuation),
                }),
                None,
            )
            .expect("detached handler")
        };
        let left = handler(&mut tree);
        let right = handler(&mut tree);

        assert_eq!(
            ExceptionHandlerPort::detached_continuation(continuation, &tree, [left, right]),
            None
        );
    }

    #[test]
    fn physical_type_reuses_resolved_phi_through_a_move() {
        let predecessor = BlockId::new(0);
        let block_id = BlockId::new(1);
        let phi_input = RegisterArg::new_ssa(7, 0, ArgType::narrow());
        let phi_value = RegisterArg::new_ssa(7, 10, ArgType::narrow());
        let moved = RegisterArg::new_ssa(23, 0, ArgType::narrow());
        let moved_value = SsaVar::from_reg(&moved).expect("moved SSA value");
        let mut predecessor_block = Block::new(predecessor);
        predecessor_block.push(InsnNode::const_value(phi_input.clone(), 0));
        let mut block = Block::new(block_id);
        block.push(InsnNode::phi(
            phi_value.clone(),
            vec![(predecessor.raw(), InsnArg::Reg(phi_input))],
        ));
        block.push(InsnNode::move_insn(moved, InsnArg::Reg(phi_value.clone())));
        let mut cfg = CFG::new("resolved_phi_move");
        cfg.entry = predecessor;
        cfg.add_block(predecessor_block);
        cfg.add_block(block);
        cfg.add_edge(predecessor, block_id, EdgeKind::Normal);
        let values = SsaValueGraph::build(&cfg).expect("SSA graph");
        let types = SsaTypeEnvironment::default();
        let constants = BTreeMap::new();
        let hierarchy = ClassHierarchyIndex::default();
        let resolved = BTreeMap::from([(
            SsaVar::from_reg(&phi_value).expect("phi SSA value"),
            ArgType::BOOLEAN,
        )]);
        let resolver =
            PhiTypeResolver::new(&cfg, &values, &types, &constants, &hierarchy, &resolved);

        assert_eq!(resolver.physical_type(moved_value), Some(ArgType::BOOLEAN));
    }

    #[test]
    fn copy_resolver_selects_nested_phi_value_for_exception_edge() {
        let entry = BlockId::new(3);
        let left_block = BlockId::new(0);
        let right_block = BlockId::new(1);
        let handler = BlockId::new(2);
        let left = source_variable(1, 0, 1);
        let right = source_variable(2, 0, 2);
        let phi_result = source_variable(0, 1, 7);
        let moved = source_variable(3, 0, 7);

        let mut cfg = CFG::new("nested_exception_phi");
        cfg.entry = entry;
        cfg.add_block(Block::new(entry));
        let mut left_body = Block::new(left_block);
        left_body.push(InsnNode::const_value(left.clone(), 1));
        cfg.add_block(left_body);
        let mut right_body = Block::new(right_block);
        right_body.push(InsnNode::const_value(right.clone(), 2));
        cfg.add_block(right_body);
        let mut handler_body = Block::new(handler);
        let mut phi = InsnNode::phi(
            phi_result.clone(),
            vec![
                (left_block.raw(), InsnArg::Reg(left)),
                (right_block.raw(), InsnArg::Reg(right.clone())),
            ],
        );
        for edge in &mut phi.payload.phi_edges {
            edge.1 = EdgeKind::Exception;
        }
        handler_body.push(phi);
        handler_body.push(InsnNode::move_insn(moved.clone(), InsnArg::Reg(phi_result)));
        cfg.add_block(handler_body);
        cfg.add_edge(entry, left_block, EdgeKind::True);
        cfg.add_edge(entry, right_block, EdgeKind::False);
        cfg.add_edge(left_block, handler, EdgeKind::Exception);
        cfg.add_edge(right_block, handler, EdgeKind::Exception);

        let values = SsaValueGraph::build(&cfg).expect("SSA graph");
        let materialized = BTreeSet::from([SsaVar::from_reg(&right).expect("SSA value")]);
        let resolver = SsaCopyResolver::new(&cfg, &values, &materialized);
        let resolved = resolver
            .resolve_for_edge(
                InsnArg::Reg(moved),
                right_block,
                EdgeKind::Exception,
                &BTreeMap::new(),
            )
            .expect("materialized edge value");

        assert!(same_value(&resolved, &InsnArg::Reg(right)));
    }

    #[test]
    fn copy_resolver_rejects_non_materialized_nested_phi_value() {
        let predecessor = BlockId::new(0);
        let handler = BlockId::new(1);
        let source = source_variable(1, 0, 1);
        let phi_result = source_variable(0, 1, 7);
        let moved = source_variable(2, 0, 7);

        let mut cfg = CFG::new("non_materialized_exception_phi");
        cfg.entry = predecessor;
        let mut predecessor_body = Block::new(predecessor);
        predecessor_body.push(InsnNode::const_value(source.clone(), 1));
        cfg.add_block(predecessor_body);
        let mut handler_body = Block::new(handler);
        let mut phi = InsnNode::phi(
            phi_result.clone(),
            vec![(predecessor.raw(), InsnArg::Reg(source))],
        );
        phi.payload.phi_edges[0].1 = EdgeKind::Exception;
        handler_body.push(phi);
        handler_body.push(InsnNode::move_insn(moved.clone(), InsnArg::Reg(phi_result)));
        cfg.add_block(handler_body);
        cfg.add_edge(predecessor, handler, EdgeKind::Exception);

        let values = SsaValueGraph::build(&cfg).expect("SSA graph");
        let materialized = BTreeSet::new();
        let resolver = SsaCopyResolver::new(&cfg, &values, &materialized);

        assert!(resolver
            .resolve_for_edge(
                InsnArg::Reg(moved),
                predecessor,
                EdgeKind::Exception,
                &BTreeMap::new(),
            )
            .is_none());
    }

    #[test]
    fn exceptional_ingress_accepts_a_required_dominating_phi() {
        let entry = BlockId::new(0);
        let phi_block = BlockId::new(1);
        let predecessor = BlockId::new(2);
        let handler = BlockId::new(3);
        let input = source_variable(0, 0, 1);
        let phi_result = source_variable(0, 1, 7);
        let phi_value = SsaVar::from_reg(&phi_result).expect("phi SSA value");

        let mut cfg = CFG::new("required_dominating_exception_phi");
        cfg.entry = entry;
        let mut entry_body = Block::new(entry);
        entry_body.push(InsnNode::const_value(input.clone(), 1));
        cfg.add_block(entry_body);
        let mut phi_body = Block::new(phi_block);
        phi_body.push(InsnNode::phi(
            phi_result.clone(),
            vec![(entry.raw(), InsnArg::Reg(input))],
        ));
        cfg.add_block(phi_body);
        cfg.add_block(Block::new(predecessor));
        cfg.add_block(Block::new(handler));
        cfg.add_edge(entry, phi_block, EdgeKind::Normal);
        cfg.add_edge(phi_block, predecessor, EdgeKind::Normal);
        cfg.add_edge(predecessor, handler, EdgeKind::Exception);

        let values = SsaValueGraph::build(&cfg).expect("SSA graph");
        let available = ExceptionalIngressCopyPlacement::available_values(
            &BTreeSet::new(),
            &BTreeSet::from([phi_value]),
        );
        let resolver = SsaCopyResolver::new(&cfg, &values, &available);
        let resolved = resolver
            .resolve_for_edge(
                InsnArg::Reg(phi_result.clone()),
                predecessor,
                EdgeKind::Exception,
                &BTreeMap::new(),
            )
            .expect("required Phi is materialized by Phi lowering");

        assert!(same_value(&resolved, &InsnArg::Reg(phi_result)));
    }

    fn normal_copies() -> NormalCopies {
        let mut destination = RegisterArg::new(0, ArgType::INT);
        destination.code_var = Some(7);
        let mut copy = InsnNode::mov(destination, InsnArg::Lit(LiteralArg::int(1)));
        copy.payload.edge_copy = true;
        let statement = SemanticStatement::instruction(copy).expect("edge copy statement");
        NormalCopies::new(
            BTreeMap::from([(NormalCopySite::Block(BlockId::new(7)), vec![statement])]),
            BTreeMap::new(),
        )
    }

    #[test]
    fn normal_copies_follow_each_statement_block_occurrence() {
        let site = NormalCopySite::Block(BlockId::new(7));
        let mut copies = normal_copies();

        assert_eq!(copies.place_at_occurrence(site).unwrap().len(), 1);
        assert_eq!(copies.place_at_occurrence(site).unwrap().len(), 1);
        assert!(copies.first_unplaced().is_none());
    }

    #[test]
    fn adapter_copy_sites_are_placed_once() {
        let site = NormalCopySite::Block(BlockId::new(7));
        let mut copies = normal_copies();

        assert_eq!(copies.place_block_occurrence(site, false).unwrap().len(), 1);
        assert!(copies.place_block_occurrence(site, false).is_none());
    }

    #[test]
    fn equivalent_concrete_copy_sites_are_each_placed() {
        let first = NormalCopySite::Block(BlockId::new(7));
        let second = NormalCopySite::Block(BlockId::new(8));
        let mut copies = normal_copies();
        let statements = copies.by_site[&first].clone();
        copies.by_site.insert(second, statements);
        copies.canonical_site = BTreeMap::from([(first, first), (second, first)]);

        assert_eq!(
            copies.place_block_occurrence(second, false).unwrap().len(),
            1
        );
        assert!(copies.first_unplaced().is_none());
        assert_eq!(
            copies.place_block_occurrence(first, false).unwrap().len(),
            1
        );
        assert!(copies.place_block_occurrence(first, false).is_none());
    }

    #[test]
    fn repeated_semantic_block_copies_follow_each_occurrence() {
        let site = NormalCopySite::Block(BlockId::new(7));
        let mut copies = normal_copies();

        assert_eq!(copies.place_block_occurrence(site, true).unwrap().len(), 1);
        assert_eq!(copies.place_block_occurrence(site, true).unwrap().len(), 1);
        assert!(copies.first_unplaced().is_none());
    }

    #[test]
    fn repeated_semantic_blocks_are_detected() {
        let block = || {
            SemanticNode::BasicBlock(SemanticBlock {
                id: BlockId::new(7),
                statements: Vec::new(),
            })
        };
        let root = SemanticNode::sequence(vec![block(), block()]);

        assert_eq!(
            SemanticBlockOccurrences::repeated(&root),
            BTreeSet::from([BlockId::new(7)])
        );
    }

    #[test]
    fn dependent_block_copies_are_not_repeated() {
        let site = NormalCopySite::Block(BlockId::new(7));
        let left = source_variable(0, 0, 1);
        let right = source_variable(1, 0, 2);
        let mut left_copy = InsnNode::mov(left.clone(), InsnArg::Reg(right.clone()));
        left_copy.payload.edge_copy = true;
        let mut right_copy = InsnNode::mov(right, InsnArg::Reg(left));
        right_copy.payload.edge_copy = true;
        let statements = vec![
            SemanticStatement::instruction(left_copy).expect("left edge copy"),
            SemanticStatement::instruction(right_copy).expect("right edge copy"),
        ];
        let mut copies = NormalCopies::new(BTreeMap::from([(site, statements)]), BTreeMap::new());

        assert_eq!(copies.place_block_occurrence(site, true).unwrap().len(), 2);
        assert!(copies.place_block_occurrence(site, true).is_none());
    }

    #[test]
    fn transfer_path_consumes_target_adapter_copies() {
        let mut copies = normal_copies();
        let edge = RegionEdge {
            source: BlockId::new(3),
            target: BlockId::new(7),
            kind: EdgeKind::True,
        };

        assert_eq!(
            copies
                .place_once_on_path([
                    NormalCopySite::Edge(edge),
                    NormalCopySite::Block(edge.target),
                ])
                .unwrap()
                .len(),
            1
        );
        assert!(copies.first_unplaced().is_none());
    }

    #[test]
    fn materialized_throwing_instruction_suppresses_terminal_copy_fallback() {
        let block = BlockId::new(18);
        let instruction = InstructionId::new(20);
        let mut constructor = InsnNode::new(InsnType::Constructor, 0);
        constructor.id = instruction;
        constructor.set_result(RegisterArg::new(13, ArgType::object("example/Value")));
        let root = SemanticNode::BasicBlock(SemanticBlock {
            id: block,
            statements: vec![SemanticStatement::instruction(constructor).unwrap()],
        });
        let materialized = EvaluationInstructions::of_node(&root)
            .into_iter()
            .collect::<BTreeSet<_>>();
        let terminals = BTreeMap::from([(block, instruction)]);

        assert_eq!(
            terminal_exceptional_fallback(&terminals, &materialized, block),
            None
        );
        assert_eq!(
            terminal_exceptional_fallback(&terminals, &BTreeSet::new(), block),
            Some(instruction)
        );
    }
}
