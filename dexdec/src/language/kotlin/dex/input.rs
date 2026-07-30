use crate::ir::{InsnType, SemanticNode, SemanticVisitor};

use super::KotlinLoweringError;

pub(super) struct KotlinInputVerifier {
    invalid: Option<KotlinLoweringError>,
}

impl KotlinInputVerifier {
    pub(super) fn verify(root: &SemanticNode) -> Result<(), KotlinLoweringError> {
        let mut verifier = Self { invalid: None };
        verifier.visit_node(root);
        verifier.invalid.map_or(Ok(()), Err)
    }

    fn reject(&mut self, error: KotlinLoweringError) {
        if self.invalid.is_none() {
            self.invalid = Some(error);
        }
    }
}

impl SemanticVisitor for KotlinInputVerifier {
    fn enter_operation(&mut self, instruction: &crate::ir::SemanticOperation) {
        let error = match instruction.insn_type {
            InsnType::Phi => KotlinLoweringError::UnrecoveredPhi(instruction.offset),
            InsnType::MoveResult => KotlinLoweringError::UnrecoveredMoveResult(instruction.offset),
            InsnType::MoveException => {
                KotlinLoweringError::UnrecoveredExceptionValue(instruction.offset)
            }
            InsnType::MonitorEnter | InsnType::MonitorExit => {
                KotlinLoweringError::UnrecoveredMonitor(instruction.offset)
            }
            InsnType::NewInstance => {
                KotlinLoweringError::UnrecoveredObjectInitialization(instruction.offset)
            }
            InsnType::Nop => KotlinLoweringError::UnsupportedStatement(InsnType::Nop),
            _ => return,
        };
        self.reject(error);
    }
}
