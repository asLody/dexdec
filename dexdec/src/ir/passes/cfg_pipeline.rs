//! Canonical CFG normalization and SSA construction.

use crate::ir::analysis::{SsaInvariantError, SsaValueGraph, TypeHierarchy};
use crate::ir::passes::{
    BindResults, CanonicalizationError, CanonicalizeCFG, CfgInvariantError,
    ConstructorRecoveryError, MonitorSplitError, Pass, PassResult, PhiSimplificationError,
    PhiSimplify, PruneUnreachable, RecoverConstructors, ResultBindingError, SSATransform,
    SplitCriticalEdges, SplitMonitorEntries, SsaTransformError, ValidateCFG,
};
use crate::ir::{AnalysisCancelled, CFG};

pub struct CfgPipeline<'a> {
    hierarchy: &'a dyn TypeHierarchy,
}

#[derive(Debug, Clone)]
pub struct CfgAnalysis {
    pub values: SsaValueGraph,
    pub change: PassResult,
}

#[derive(Debug)]
pub enum CfgPipelineError {
    Cancelled(AnalysisCancelled),
    Canonicalization(CanonicalizationError),
    ResultBinding(ResultBindingError),
    MonitorSplit(MonitorSplitError),
    SsaConstruction(SsaTransformError),
    PhiSimplification(PhiSimplificationError),
    ConstructorRecovery(ConstructorRecoveryError),
    Validation(CfgInvariantError),
    SsaInvariant(SsaInvariantError),
}

impl std::fmt::Display for CfgPipelineError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cancelled(error) => error.fmt(formatter),
            Self::Canonicalization(error) => write!(formatter, "CFG canonicalization: {error}"),
            Self::ResultBinding(error) => write!(formatter, "DEX result binding: {error}"),
            Self::MonitorSplit(error) => write!(formatter, "monitor boundary split: {error}"),
            Self::SsaConstruction(error) => write!(formatter, "SSA construction: {error}"),
            Self::PhiSimplification(error) => write!(formatter, "Phi simplification: {error}"),
            Self::ConstructorRecovery(error) => write!(formatter, "constructor recovery: {error}"),
            Self::Validation(error) => write!(formatter, "CFG invariant: {error}"),
            Self::SsaInvariant(error) => write!(formatter, "SSA invariant: {error}"),
        }
    }
}

impl std::error::Error for CfgPipelineError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Cancelled(source) => Some(source),
            Self::Canonicalization(source) => Some(source),
            Self::ResultBinding(source) => Some(source),
            Self::MonitorSplit(source) => Some(source),
            Self::SsaConstruction(source) => Some(source),
            Self::PhiSimplification(source) => Some(source),
            Self::ConstructorRecovery(source) => Some(source),
            Self::Validation(source) => Some(source),
            Self::SsaInvariant(source) => Some(source),
        }
    }
}

impl From<std::convert::Infallible> for CfgPipelineError {
    fn from(error: std::convert::Infallible) -> Self {
        match error {}
    }
}

impl From<AnalysisCancelled> for CfgPipelineError {
    fn from(error: AnalysisCancelled) -> Self {
        Self::Cancelled(error)
    }
}

macro_rules! cfg_error_conversion {
    ($source:ty, $variant:ident) => {
        impl From<$source> for CfgPipelineError {
            fn from(error: $source) -> Self {
                Self::$variant(error)
            }
        }
    };
}

cfg_error_conversion!(CanonicalizationError, Canonicalization);
cfg_error_conversion!(ResultBindingError, ResultBinding);
cfg_error_conversion!(MonitorSplitError, MonitorSplit);
cfg_error_conversion!(SsaTransformError, SsaConstruction);
cfg_error_conversion!(PhiSimplificationError, PhiSimplification);
cfg_error_conversion!(ConstructorRecoveryError, ConstructorRecovery);
cfg_error_conversion!(CfgInvariantError, Validation);
cfg_error_conversion!(SsaInvariantError, SsaInvariant);

impl<'a> CfgPipeline<'a> {
    pub fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self { hierarchy }
    }

    pub fn run(&self, cfg: &mut CFG) -> Result<PassResult, CfgPipelineError> {
        self.analyze(cfg).map(|analysis| analysis.change)
    }

    pub fn run_observed(
        &self,
        cfg: &mut CFG,
        observer: &dyn crate::ir::AnalysisObserver,
    ) -> Result<PassResult, CfgPipelineError> {
        self.analyze_observed(cfg, observer)
            .map(|analysis| analysis.change)
    }

    pub fn analyze(&self, cfg: &mut CFG) -> Result<CfgAnalysis, CfgPipelineError> {
        self.analyze_observed(cfg, &crate::ir::NullAnalysisObserver)
    }

    pub fn analyze_observed(
        &self,
        cfg: &mut CFG,
        observer: &dyn crate::ir::AnalysisObserver,
    ) -> Result<CfgAnalysis, CfgPipelineError> {
        if cfg.is_analysis_prepared() {
            return Ok(CfgAnalysis {
                values: Self::values(cfg)?,
                change: PassResult::Unchanged,
            });
        }

        cfg.capture_exception_coverage();

        let mut context = StageContext::new(cfg, observer);
        context.validate("input")?;
        let mut changed = NormalizationStage::default().run(&mut context)?;
        changed |= SsaStage::new(self.hierarchy).run(&mut context)?;

        context.validate("ssa")?;
        context.cfg.identify_instructions();
        context.cfg.mark_analysis_prepared();
        let values = Self::values(context.cfg)?;
        Ok(CfgAnalysis {
            values,
            change: changed.into(),
        })
    }

    fn values(cfg: &CFG) -> Result<SsaValueGraph, CfgPipelineError> {
        SsaValueGraph::build(cfg).map_err(CfgPipelineError::SsaInvariant)
    }
}

trait CfgStage {
    const NAME: &'static str;

    fn run(&mut self, context: &mut StageContext<'_>) -> Result<bool, CfgPipelineError>;
}

#[derive(Default)]
struct NormalizationStage {
    prune: PruneUnreachable,
    canonicalize: CanonicalizeCFG,
    bind_results: BindResults,
    split_monitors: SplitMonitorEntries,
    split_edges: SplitCriticalEdges,
}

impl CfgStage for NormalizationStage {
    const NAME: &'static str = "cfg";

    fn run(&mut self, context: &mut StageContext<'_>) -> Result<bool, CfgPipelineError> {
        let mut changed = false;
        loop {
            let mut round = context.pass(Self::NAME, &mut self.prune)?;
            round |= context.pass(Self::NAME, &mut self.canonicalize)?;
            changed |= round;
            if !round {
                break;
            }
        }
        changed |= context.pass(Self::NAME, &mut self.bind_results)?;
        changed |= context.pass(Self::NAME, &mut self.split_monitors)?;
        changed |= context.pass(Self::NAME, &mut self.split_edges)?;
        context.validate(Self::NAME)?;
        Ok(changed)
    }
}

struct SsaStage<'a> {
    construct: SSATransform,
    simplify: PhiSimplify,
    constructors: RecoverConstructors<'a>,
    prune: PruneUnreachable,
}

impl<'a> SsaStage<'a> {
    fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self {
            construct: SSATransform,
            simplify: PhiSimplify,
            constructors: RecoverConstructors::new(hierarchy),
            prune: PruneUnreachable,
        }
    }
}

impl CfgStage for SsaStage<'_> {
    const NAME: &'static str = "ssa";

    fn run(&mut self, context: &mut StageContext<'_>) -> Result<bool, CfgPipelineError> {
        let mut changed = context.pass(Self::NAME, &mut self.construct)?;
        changed |= context.pass(Self::NAME, &mut self.simplify)?;
        let constructors_changed = context.pass(Self::NAME, &mut self.constructors)?;
        changed |= constructors_changed;
        if constructors_changed {
            changed |= context.pass(Self::NAME, &mut self.prune)?;
            changed |= context.pass(Self::NAME, &mut self.simplify)?;
        }
        context.validate(Self::NAME)?;
        Ok(changed)
    }
}

struct StageContext<'a> {
    cfg: &'a mut CFG,
    observer: &'a dyn crate::ir::AnalysisObserver,
}

impl<'a> StageContext<'a> {
    fn new(cfg: &'a mut CFG, observer: &'a dyn crate::ir::AnalysisObserver) -> Self {
        Self { cfg, observer }
    }

    fn pass<P>(&mut self, stage: &'static str, pass: &mut P) -> Result<bool, CfgPipelineError>
    where
        P: Pass,
        CfgPipelineError: From<P::Error>,
    {
        self.observer.checkpoint()?;
        let result = pass.run(self.cfg).map_err(CfgPipelineError::from)?;
        self.observe(stage, pass.name(), result);
        self.observer.checkpoint()?;
        Ok(result == PassResult::Changed)
    }

    fn validate(&mut self, stage: &'static str) -> Result<(), CfgPipelineError> {
        self.observer.checkpoint()?;
        let mut validator = ValidateCFG;
        let result = validator.run(self.cfg)?;
        self.observe(stage, validator.name(), result);
        self.observer.checkpoint()?;
        Ok(())
    }

    fn observe(&self, phase: &'static str, name: &'static str, result: PassResult) {
        self.observer
            .observe(crate::ir::AnalysisEvent::CfgTransform {
                phase,
                name,
                result,
                cfg: self.cfg,
            });
    }
}
