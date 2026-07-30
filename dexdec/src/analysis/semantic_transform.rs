use crate::ir::{SemanticContext, SemanticMethod};

pub trait SemanticTransform<Input>
where
    Input: SemanticContext,
{
    type Output: SemanticContext;
    type Error: std::error::Error;

    fn transform(
        &mut self,
        method: SemanticMethod<Input>,
    ) -> Result<SemanticMethod<Self::Output>, Self::Error>;
}
