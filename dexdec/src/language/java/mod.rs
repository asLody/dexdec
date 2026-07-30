mod aggregate;
mod assignment;
mod ast;
mod declaration_placement;
mod declarations;
mod dex;
mod emit;
pub(crate) mod literals;
mod lower;
mod members;
mod normalize;
mod rewrite;
mod source_types;
mod syntax;
mod unit;

pub use aggregate::AggregateInitializer;
pub use assignment::DefiniteAssignment;
pub use ast::{
    JavaAssignOp, JavaBinaryOp, JavaCatch, JavaClassName, JavaClassType, JavaClassTypeSegment,
    JavaConstructorTarget, JavaExpr, JavaField, JavaIdentifier, JavaLiteral, JavaMethodBody,
    JavaNameScope, JavaPrimitiveType, JavaStmt, JavaSwitchCase, JavaType, JavaTypeArgument,
    JavaTypeParameter, JavaUnaryOp, JavaUpdateOp,
};
pub use declaration_placement::LexicalDeclarationPlacement;
pub use dex::{DexJavaDialect, JavaLoweringError, JavaSourceErasure, OuterInstanceBinding};
pub use emit::{JavaPrintError, JavaPrinter};
pub use lower::{JavaDialect, JavaLowerer, JavaStructuralError};
pub use members::{JavaConstructorLayout, JavaFieldSymbol, JavaMemberNames, JavaMethodSymbol};
pub use normalize::{
    JavaAstNormalizer, JavaAstTransform, JavaInitializerExitLowering, JavaMethodCompletion,
};
pub use rewrite::JavaAstRewriter;
pub(crate) use source_types::GenericTypeProjection;
pub use syntax::{JavaValueSyntax, SourceSyntaxRecovery};
pub use unit::{
    JavaAnnotation, JavaAnnotationElement, JavaAnnotationValue, JavaAnonymousClassBody,
    JavaCompilationUnit, JavaEnumConstant, JavaFieldDeclaration, JavaMethodDeclaration,
    JavaMethodDeclarationKind, JavaMethodParameter, JavaModifier, JavaTypeDeclaration,
    JavaTypeDeclarationKind,
};
