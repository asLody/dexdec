//! Finite Java syntax recovery proven over Semantic IR.

mod conditions;
mod expression;
mod loops;
pub(super) mod primitives;
mod protection;

use crate::analysis::SemanticTransform;
use crate::ir::{analysis::TypeHierarchy, SemanticMethod, SourceSemantics, SourceSyntaxSemantics};

pub struct SourceSyntaxRecovery<'a> {
    expressions: expression::ExpressionSyntax,
    loops: loops::JavaLoopSyntax<'a>,
    conditions: conditions::PathConditionSyntax,
    protection: protection::ProtectionSyntax<'a>,
}

pub struct JavaValueSyntax<'a> {
    expressions: expression::ExpressionSyntax,
    loops: loops::JavaLoopSyntax<'a>,
}

impl<'a> JavaValueSyntax<'a> {
    pub fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self {
            expressions: expression::ExpressionSyntax::default(),
            loops: loops::JavaLoopSyntax::new(hierarchy),
        }
    }

    pub fn apply(
        &mut self,
        method: &mut SemanticMethod<SourceSyntaxSemantics>,
    ) -> Result<bool, crate::ir::SemanticFoldError> {
        let types = method.state().types().clone();
        let recovery = self.expressions.apply(method.body_mut(), &types)?;
        let loops = self.loops.apply(method.body_mut())?;
        Ok(recovery.changed || loops)
    }
}

impl<'a> SourceSyntaxRecovery<'a> {
    pub fn new(hierarchy: &'a dyn TypeHierarchy) -> Self {
        Self {
            expressions: expression::ExpressionSyntax::default(),
            loops: loops::JavaLoopSyntax::new(hierarchy),
            conditions: conditions::PathConditionSyntax,
            protection: protection::ProtectionSyntax::new(hierarchy),
        }
    }
}

impl SemanticTransform<SourceSemantics> for SourceSyntaxRecovery<'_> {
    type Output = SourceSyntaxSemantics;
    type Error = crate::ir::SemanticFoldError;

    fn transform(
        &mut self,
        mut method: SemanticMethod<SourceSemantics>,
    ) -> Result<SemanticMethod<Self::Output>, Self::Error> {
        let types = method.state().types().clone();
        let expressions = self.expressions.apply(method.body_mut(), &types)?;
        method
            .state_mut()
            .types_mut()
            .refine_booleans(expressions.boolean_variables);
        self.loops.apply(method.body_mut())?;
        let types = method.state().types().clone();
        self.conditions.apply(method.body_mut(), &types)?;
        self.protection.apply(method.body_mut())?;
        Ok(method.into_source_syntax())
    }
}
