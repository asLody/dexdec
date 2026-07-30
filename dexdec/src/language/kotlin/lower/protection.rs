use crate::ir::SemanticCatch;

use super::{KotlinDialect, KotlinStructuralError};
use crate::language::kotlin::ast::{KotlinCatch, KotlinStmt};

pub(super) struct ProtectionLowering<'a, R> {
    dialect: &'a mut R,
}

impl<'a, R> ProtectionLowering<'a, R>
where
    R: KotlinDialect,
    R::Error: From<KotlinStructuralError>,
{
    pub(super) fn new(dialect: &'a mut R) -> Self {
        Self { dialect }
    }

    pub(super) fn lower(
        &mut self,
        body: KotlinStmt,
        catches: &[SemanticCatch],
        catch_bodies: Vec<KotlinStmt>,
        finally: Option<KotlinStmt>,
    ) -> Result<KotlinStmt, R::Error> {
        if catch_bodies.len() != catches.len() {
            return Err(KotlinStructuralError::ChildArity {
                expected: catches.len(),
                actual: catch_bodies.len(),
            }
            .into());
        }

        let lowered = catches
            .iter()
            .zip(catch_bodies)
            .map(|(catch, body)| self.lower_catch(catch, body))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(KotlinStmt::Try {
            body: Box::new(body),
            catches: lowered,
            finally: finally.map(Box::new),
        })
    }

    fn lower_catch(
        &mut self,
        catch: &SemanticCatch,
        body: KotlinStmt,
    ) -> Result<KotlinCatch, R::Error> {
        let types = catch
            .exception_types
            .iter()
            .map(|ty| self.dialect.type_name(ty))
            .collect::<Result<Vec<_>, _>>()?;
        if types.is_empty() {
            return Err(KotlinStructuralError::EmptyCatchTypes.into());
        }
        Ok(self
            .dialect
            .catch_binding(catch.exception_value.as_ref())?
            .lower(types, body))
    }
}
