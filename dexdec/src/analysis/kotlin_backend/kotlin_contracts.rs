use crate::frontend::MethodOverrideSemantics;

/// Kotlin source contracts for JVM members whose nullability is stricter than
/// the erased descriptor can express.
pub(super) struct KotlinOverrideContracts;

impl KotlinOverrideContracts {
    pub(super) fn has_non_null_return(semantics: Option<&MethodOverrideSemantics>) -> bool {
        semantics.is_some_and(|semantics| {
            semantics.base_methods.iter().any(|method| {
                method.declaring_class == "Ljava/lang/Object;"
                    && method.short_id == "toString()Ljava/lang/String;"
            })
        })
    }
}
