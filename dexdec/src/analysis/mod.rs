pub(crate) mod jadx_local_names;
#[path = "java_backend/mod.rs"]
pub mod java_backend;
#[path = "kotlin_backend/mod.rs"]
pub mod kotlin_backend;
mod method_input;
pub mod method_override;
mod name_recovery;
pub mod semantic_transform;
pub mod value_recovery;

pub(crate) use method_input::{ClassMethodInput, MethodRecoveryFailure, MethodRecoveryStage};
pub(crate) use name_recovery::{RelationalNameInference, TypedConstantNameInference};

pub use semantic_transform::SemanticTransform;

pub use java_backend::{JavaDecompiler, JavaDecompilerConfig, JavaDecompilerError};
pub use kotlin_backend::{KotlinDecompiler, KotlinDecompilerConfig, KotlinDecompilerError};

pub(crate) struct NestedClassInput {
    pub class: crate::frontend::ClassNode,
    pub methods: Vec<ClassMethodInput>,
    pub nested: Vec<NestedClassInput>,
}
