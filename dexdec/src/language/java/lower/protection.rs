use crate::ir::SemanticCatch;

use super::{JavaDialect, JavaStructuralError};
use crate::language::java::ast::{JavaCatch, JavaStmt};

pub(super) struct ProtectionLowering<'a, R> {
    dialect: &'a mut R,
}

impl<'a, R> ProtectionLowering<'a, R>
where
    R: JavaDialect,
    R::Error: From<JavaStructuralError>,
{
    pub(super) fn new(dialect: &'a mut R) -> Self {
        Self { dialect }
    }

    pub(super) fn lower(
        &mut self,
        body: JavaStmt,
        catches: &[SemanticCatch],
        catch_bodies: Vec<JavaStmt>,
        finally: Option<JavaStmt>,
    ) -> Result<JavaStmt, R::Error> {
        if catch_bodies.len() != catches.len() {
            return Err(JavaStructuralError::ChildArity {
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
        Ok(JavaStmt::Try {
            body: Box::new(body),
            catches: lowered,
            finally: finally.map(Box::new),
        })
    }

    fn lower_catch(
        &mut self,
        catch: &SemanticCatch,
        body: JavaStmt,
    ) -> Result<JavaCatch, R::Error> {
        let types = catch
            .exception_types
            .iter()
            .map(|ty| self.dialect.type_name(ty))
            .collect::<Result<Vec<_>, _>>()?;
        if types.is_empty() {
            return Err(JavaStructuralError::EmptyCatchTypes.into());
        }
        Ok(self
            .dialect
            .catch_binding(catch.exception_value.as_ref())?
            .lower(types, body))
    }
}
