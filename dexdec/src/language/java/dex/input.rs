use crate::ir::{InsnType, SemanticNode, SemanticVisitor};

use super::JavaLoweringError;

pub(super) struct JavaInputVerifier {
    invalid: Option<JavaLoweringError>,
}

impl JavaInputVerifier {
    pub(super) fn verify(root: &SemanticNode) -> Result<(), JavaLoweringError> {
        let mut verifier = Self { invalid: None };
        verifier.visit_node(root);
        verifier.invalid.map_or(Ok(()), Err)
    }

    fn reject(&mut self, error: JavaLoweringError) {
        if self.invalid.is_none() {
            self.invalid = Some(error);
        }
    }
}

impl SemanticVisitor for JavaInputVerifier {
    fn enter_operation(&mut self, instruction: &crate::ir::SemanticOperation) {
        let error = match instruction.insn_type {
            InsnType::Phi => JavaLoweringError::UnrecoveredPhi(instruction.offset),
            InsnType::MoveResult => JavaLoweringError::UnrecoveredMoveResult(instruction.offset),
            InsnType::MoveException => {
                JavaLoweringError::UnrecoveredExceptionValue(instruction.offset)
            }
            InsnType::MonitorEnter | InsnType::MonitorExit => {
                JavaLoweringError::UnrecoveredMonitor(instruction.offset)
            }
            InsnType::NewInstance => {
                JavaLoweringError::UnrecoveredObjectInitialization(instruction.offset)
            }
            InsnType::Nop => JavaLoweringError::UnsupportedStatement(InsnType::Nop),
            _ => return,
        };
        self.reject(error);
    }
}
