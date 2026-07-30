use std::collections::{BTreeMap, BTreeSet};

use super::{BlockId, ExceptionAnalysis, RegionGraph, RegionId, RegionKind, SemanticNode, CFG};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticStage {
    Structured,
    ValuesRecovered,
    SourceAllocated,
    SourceVariables,
    SourceSyntax,
    Normalized,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GatedPhiRejection {
    UnusedResult,
    ExistingDefinition,
    UnmappedInputGate,
    UnaddressableUse,
    UnrecoverableUseDomain,
    AmbiguousUseDomain,
    IncompleteUseDomain,
    InsufficientInputs,
    CyclicInput,
    LoopCarried,
    AmbiguousInputDefinition,
    MissingSelectionRegion,
    MissingInputGate,
    UnsupportedInputValue,
    IncompleteCoverage,
    TrivialValueSet,
    OverlappingGates,
    PredicateNotRecoverable,
    CompositionCost,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GatedPhiDiagnostic {
    pub block: BlockId,
    pub register: u32,
    pub version: u32,
    pub reason: GatedPhiRejection,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ValueRecoveryDiagnostics {
    pub gated_candidates: usize,
    pub gated_recovered: usize,
    pub gated_specialized: usize,
    pub decision_nodes: usize,
    pub exact_partition_searches: usize,
    pub bounded_partition_searches: usize,
    pub rejected: Vec<GatedPhiDiagnostic>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceTypeDiagnostics {
    pub object_types: Vec<(String, String)>,
    pub definition_variables: Vec<(u32, String)>,
    pub definition_values: Vec<(u32, u32, String)>,
    pub variables: Vec<(u32, String)>,
    pub values: Vec<(u32, u32, String)>,
    pub requirements: Vec<(u32, String)>,
    pub value_requirements: Vec<(u32, u32, String)>,
    pub equations: Vec<SourceTypeEquationDiagnostic>,
    pub requirement_candidates: Vec<(u32, Vec<String>)>,
    pub invocations: Vec<InvocationTypeDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceTypeEquationDiagnostic {
    pub variable: u32,
    pub register: u32,
    pub version: Option<u32>,
    pub erased_type: String,
    pub edge_copy: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvocationTypeDiagnostic {
    pub reference: String,
    pub resolved: bool,
    pub inputs: Vec<Option<String>>,
    pub output: Option<String>,
    pub owner_parameters: Vec<String>,
    pub owner_bounds_satisfied: Option<bool>,
}

pub enum AnalysisEvent<'a> {
    ClassStage {
        class: &'a str,
        stage: &'static str,
    },
    MethodStage {
        class: &'a str,
        method: &'a str,
        descriptor: &'a str,
        stage: &'static str,
    },
    MethodFailure {
        class: &'a str,
        method: &'a str,
        descriptor: &'a str,
        stage: &'static str,
        reason: &'a str,
    },
    MethodPipeline {
        cfg: &'a CFG,
        stage: &'static str,
    },
    CfgTransform {
        phase: &'static str,
        name: &'static str,
        result: super::PassResult,
        cfg: &'a CFG,
    },
    ControlFlow(&'a CFG),
    Exceptions {
        cfg: &'a CFG,
        analysis: &'a ExceptionAnalysis,
    },
    Regions {
        cfg: &'a CFG,
        graph: &'a RegionGraph,
    },
    RegionCfg {
        region: RegionId,
        kind: &'a RegionKind,
        source_cfg: &'a CFG,
        region_cfg: &'a CFG,
        mapping: &'a BTreeMap<BlockId, BlockId>,
        open_flows: &'a BTreeMap<BlockId, BTreeSet<BlockId>>,
    },
    RegionChild {
        owner: RegionId,
        child: RegionId,
        entry: BlockId,
        stage: &'static str,
        root: &'a SemanticNode,
    },
    Semantics {
        cfg: &'a CFG,
        stage: SemanticStage,
        root: &'a SemanticNode,
    },
    ValueRecovery {
        cfg: &'a CFG,
        diagnostics: &'a ValueRecoveryDiagnostics,
    },
    SourceTypes(&'a SourceTypeDiagnostics),
    IncompleteMethod {
        cfg: &'a CFG,
        stage: SemanticStage,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnalysisEventKind {
    ClassStage,
    MethodStage,
    MethodFailure,
    MethodPipeline,
    CfgTransform,
    ControlFlow,
    Exceptions,
    Regions,
    RegionCfg,
    RegionChild,
    Semantics,
    ValueRecovery,
    SourceTypes,
    IncompleteMethod,
}

impl AnalysisEvent<'_> {
    pub fn kind(&self) -> AnalysisEventKind {
        match self {
            Self::ClassStage { .. } => AnalysisEventKind::ClassStage,
            Self::MethodStage { .. } => AnalysisEventKind::MethodStage,
            Self::MethodFailure { .. } => AnalysisEventKind::MethodFailure,
            Self::MethodPipeline { .. } => AnalysisEventKind::MethodPipeline,
            Self::CfgTransform { .. } => AnalysisEventKind::CfgTransform,
            Self::ControlFlow(_) => AnalysisEventKind::ControlFlow,
            Self::Exceptions { .. } => AnalysisEventKind::Exceptions,
            Self::Regions { .. } => AnalysisEventKind::Regions,
            Self::RegionCfg { .. } => AnalysisEventKind::RegionCfg,
            Self::RegionChild { .. } => AnalysisEventKind::RegionChild,
            Self::Semantics { .. } => AnalysisEventKind::Semantics,
            Self::ValueRecovery { .. } => AnalysisEventKind::ValueRecovery,
            Self::SourceTypes(_) => AnalysisEventKind::SourceTypes,
            Self::IncompleteMethod { .. } => AnalysisEventKind::IncompleteMethod,
        }
    }
}

pub trait AnalysisObserver: Send + Sync {
    fn is_enabled(&self, _kind: AnalysisEventKind) -> bool {
        true
    }

    fn is_cancelled(&self) -> bool {
        false
    }

    fn checkpoint(&self) -> Result<(), AnalysisCancelled> {
        if self.is_cancelled() {
            Err(AnalysisCancelled)
        } else {
            Ok(())
        }
    }

    fn observe(&self, event: AnalysisEvent<'_>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnalysisCancelled;

impl std::fmt::Display for AnalysisCancelled {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("analysis was cancelled")
    }
}

impl std::error::Error for AnalysisCancelled {}

#[derive(Debug, Default)]
pub struct NullAnalysisObserver;

impl AnalysisObserver for NullAnalysisObserver {
    fn is_enabled(&self, _kind: AnalysisEventKind) -> bool {
        false
    }

    fn observe(&self, _event: AnalysisEvent<'_>) {}
}
