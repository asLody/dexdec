use super::MethodReference;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnalysisLocation {
    Class(String),
    Method(MethodReference),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnalysisDiagnostic {
    InvalidGenericSignature {
        location: AnalysisLocation,
        signature: String,
        offset: usize,
    },
    InconsistentGenericSignature {
        location: AnalysisLocation,
        signature: String,
        reason: String,
    },
}
