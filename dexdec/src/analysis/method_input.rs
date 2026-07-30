use crate::frontend::MethodNode;
use crate::ir::{AnalysisEvent, AnalysisObserver, CFG};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MethodRecoveryStage {
    Decode,
    Metadata,
    Semantics,
    SourceLowering,
}

impl MethodRecoveryStage {
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Decode => "DEX decoding",
            Self::Metadata => "method metadata",
            Self::Semantics => "semantic recovery",
            Self::SourceLowering => "source lowering",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MethodRecoveryFailure {
    stage: MethodRecoveryStage,
    cause: String,
}

impl MethodRecoveryFailure {
    pub(crate) fn new(stage: MethodRecoveryStage, cause: impl std::fmt::Display) -> Self {
        Self {
            stage,
            cause: cause.to_string(),
        }
    }

    pub(crate) fn summary(&self) -> String {
        format!(
            "Method could not be decompiled during {}: {}",
            self.stage.label(),
            self.cause
        )
    }

    pub(crate) fn observe(
        &self,
        observer: &dyn AnalysisObserver,
        class: &str,
        method: &str,
        descriptor: &str,
    ) {
        observer.observe(AnalysisEvent::MethodFailure {
            class,
            method,
            descriptor,
            stage: self.stage.label(),
            reason: &self.cause,
        });
    }
}

#[derive(Debug)]
pub(crate) enum ClassMethodState {
    Decoded(CFG),
    Failed(MethodRecoveryFailure),
}

#[derive(Debug)]
pub(crate) struct ClassMethodInput {
    method: MethodNode,
    state: ClassMethodState,
}

impl ClassMethodInput {
    pub(crate) fn decoded(method: MethodNode, cfg: CFG) -> Self {
        Self {
            method,
            state: ClassMethodState::Decoded(cfg),
        }
    }

    pub(crate) fn failed(method: MethodNode, failure: MethodRecoveryFailure) -> Self {
        Self {
            method,
            state: ClassMethodState::Failed(failure),
        }
    }

    pub(crate) fn method(&self) -> &MethodNode {
        &self.method
    }

    pub(crate) fn method_mut(&mut self) -> &mut MethodNode {
        &mut self.method
    }

    pub(crate) fn cfg(&self) -> Option<&CFG> {
        match &self.state {
            ClassMethodState::Decoded(cfg) => Some(cfg),
            ClassMethodState::Failed(_) => None,
        }
    }

    pub(crate) fn cfg_mut(&mut self) -> Option<&mut CFG> {
        match &mut self.state {
            ClassMethodState::Decoded(cfg) => Some(cfg),
            ClassMethodState::Failed(_) => None,
        }
    }

    pub(crate) fn decoded_mut(&mut self) -> Option<(&mut MethodNode, &mut CFG)> {
        match &mut self.state {
            ClassMethodState::Decoded(cfg) => Some((&mut self.method, cfg)),
            ClassMethodState::Failed(_) => None,
        }
    }

    pub(crate) fn failure(&self) -> Option<&MethodRecoveryFailure> {
        match &self.state {
            ClassMethodState::Decoded(_) => None,
            ClassMethodState::Failed(failure) => Some(failure),
        }
    }
}
