mod aggregate;
mod assignment;
mod ast;
mod declaration_placement;
mod declarations;
mod dex;
mod emit;
mod imports;
mod jvm_builtins;
mod jvm_calls;
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
    KotlinAssignOp, KotlinBinaryOp, KotlinCallArguments, KotlinCatch, KotlinClassName,
    KotlinClassType, KotlinClassTypeSegment, KotlinConstructorTarget, KotlinExpr, KotlinField,
    KotlinIdentifier, KotlinJvmIntrinsic, KotlinLiteral, KotlinLocalBinding, KotlinMethodBody,
    KotlinNameScope, KotlinPrimitiveType, KotlinStmt, KotlinSwitchCase, KotlinType,
    KotlinTypeArgument, KotlinTypeParameter, KotlinUnaryOp, KotlinUpdateOp,
};
pub use declaration_placement::LexicalDeclarationPlacement;
pub use dex::{
    DexKotlinDialect, KotlinDefaultCallContract, KotlinDefaultMask, KotlinLoweringError,
    KotlinMethodNullability, KotlinSourceErasure, OuterInstanceBinding,
};
pub use emit::{KotlinPrintError, KotlinPrinter};
pub use imports::KotlinImportAnalysis;
pub(crate) use jvm_builtins::KotlinJvmBuiltins;
pub use lower::{KotlinDialect, KotlinLowerer, KotlinStructuralError};
pub use members::{
    KotlinConstructorLayout, KotlinFieldSymbol, KotlinMemberNames, KotlinMethodSymbol,
};
pub use normalize::{
    KotlinAstNormalizer, KotlinAstTransform, KotlinExtensionReceiverLowering,
    KotlinInitializerExitLowering, KotlinLocalBindingAnalysis, KotlinMutableParameterLowering,
    KotlinNameUseAnalysis, KotlinNullabilityFacts, KotlinSmartCastLowering,
};
pub use rewrite::KotlinAstRewriter;
pub(crate) use source_types::GenericTypeProjection;
pub use syntax::{KotlinValueSyntax, SourceSyntaxRecovery};
pub use unit::{
    KotlinAnnotation, KotlinAnnotationElement, KotlinAnnotationValue, KotlinAnonymousClassBody,
    KotlinCompilationUnit, KotlinEnumConstant, KotlinExtensionReceiver, KotlinFieldDeclaration,
    KotlinMethodDeclaration, KotlinMethodDeclarationKind, KotlinMethodParameter, KotlinModifier,
    KotlinPrimaryParameter, KotlinPropertyDeclaration, KotlinTypeDeclaration,
    KotlinTypeDeclarationKind,
};
