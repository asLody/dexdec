use crate::analysis::{
    ClassMethodInput, MethodRecoveryFailure, MethodRecoveryStage, NestedClassInput,
};
use crate::frontend::{ClassNode, MethodNode};
use crate::ir::cfg::CFG;
use rayon::prelude::*;

use super::declaration_lowering::{KotlinCompilationUnitLowering, KotlinSingleMethodLowering};
use super::kotlin_model::method::collect_param_debug_names;
use super::kotlin_model::{
    KotlinClassModel, KotlinMethodDeclaration, KotlinMethodModel, OuterInstanceField,
};
use super::method_pipeline::{MethodBodyAnalysis, MethodBodyPipeline};
use super::type_uses::KotlinMethodTypeUses;
use super::{KotlinDecompiler, KotlinDecompilerError};
use crate::language::kotlin::KotlinPrinter;

struct ClassMethodBuilder<'a> {
    decompiler: &'a KotlinDecompiler,
    class: &'a ClassNode,
    source_signatures: &'a super::signature_inference::SourceSignatureInference<'a>,
    exception_contracts:
        &'a std::collections::BTreeMap<crate::ir::MethodReference, Vec<crate::ir::ArgType>>,
    outer_instance: Option<&'a OuterInstanceField>,
    function_object: bool,
}

impl ClassMethodBuilder<'_> {
    fn build(
        &self,
        decoded_method: &mut MethodNode,
        cfg: &mut CFG,
    ) -> Option<(
        (String, String),
        Result<KotlinMethodModel, KotlinDecompilerError>,
    )> {
        if decoded_method.access_flags.is_bridge() {
            return None;
        }
        let key = (
            decoded_method.info.name.clone(),
            decoded_method.info.descriptor(),
        );
        let method_reference = crate::ir::MethodReference {
            owner: self.class.class_type().clone(),
            name: decoded_method.name().to_string(),
            descriptor: crate::ir::MethodDescriptor {
                parameters: decoded_method.param_types().to_vec(),
                return_type: decoded_method.return_type().clone(),
            },
        };
        let inferred_parameter_types = self.source_signatures.parameter_types(&method_reference);
        let inferred_return_type = self.source_signatures.return_type(&method_reference);
        let body_parameter_types = self
            .source_signatures
            .body_parameter_types(&method_reference);
        let function_types = self
            .function_object
            .then(|| {
                super::function_object_types::FunctionObjectMethodInference::infer(
                    decoded_method,
                    &self.class.interfaces,
                    &body_parameter_types,
                    inferred_return_type.as_ref(),
                    &self.decompiler.source_abi,
                )
            })
            .flatten()
            .filter(|types| {
                let interface = types.interface().erased();
                self.class
                    .interfaces
                    .iter()
                    .any(|declared| declared == &interface)
            });
        let source_parameter_types = function_types
            .as_ref()
            .map(|types| types.parameters())
            .unwrap_or(inferred_parameter_types.as_slice());
        let descriptor = decoded_method.info.descriptor();
        self.decompiler.method_stage(
            self.class.type_descriptor(),
            &decoded_method.info.name,
            &descriptor,
            "start",
        );
        let model = self
            .decompiler
            .build_method_model_from_node(
                self.class,
                decoded_method,
                cfg,
                self.exception_contracts
                    .get(&method_reference)
                    .map(Vec::as_slice),
                (!source_parameter_types.is_empty()).then_some(source_parameter_types),
                inferred_return_type.as_ref(),
                function_types.as_ref().map(|types| types.interface()),
                self.outer_instance,
            )
            .map_err(|source| KotlinDecompilerError::MethodFailed {
                method: decoded_method.info.name.clone(),
                descriptor: descriptor.clone(),
                source: Box::new(source),
            });
        self.decompiler.method_stage(
            self.class.type_descriptor(),
            &decoded_method.info.name,
            &descriptor,
            if model.is_ok() { "done" } else { "failed" },
        );
        Some((key, model))
    }
}

impl KotlinDecompiler {
    /// Generate structured output for a method
    ///
    /// Pipeline:
    /// 1. Normalize CFG and construct SSA
    /// 2. Build exception, synchronization, loop, and switch regions
    /// 3. Resolve cross-region leaves and cleanup chains
    /// 4. Construct semantic IR from SCC and reaching-condition facts
    /// 5. Recover values and lower the Kotlin AST
    pub fn generate_method(&mut self, cfg: &mut CFG) -> Result<String, KotlinDecompilerError> {
        let method = self.build_method_model(cfg)?;
        let declaration = KotlinSingleMethodLowering::lower(
            &method,
            None,
            None,
            method_type_uses(&method),
            &self.source_abi,
            self.type_hierarchy.clone(),
            self.observer.clone(),
        )?;
        Ok(KotlinPrinter::new(self.config.indent.clone())
            .print_method_declaration(&declaration, 0)?)
    }

    pub fn generate_method_with_context(
        &mut self,
        class: &ClassNode,
        method: &MethodNode,
        cfg: &mut CFG,
    ) -> Result<String, KotlinDecompilerError> {
        let exception_contracts = super::exception_contract::DeclaredExceptionAnalysis::new(
            self.source_abi.as_ref(),
            self.type_hierarchy.as_ref(),
        )
        .solve(class, std::iter::once((method, &*cfg)));
        let reference = crate::ir::MethodReference {
            owner: class.class_type().clone(),
            name: method.name().to_string(),
            descriptor: crate::ir::MethodDescriptor {
                parameters: method.param_types().to_vec(),
                return_type: method.return_type().clone(),
            },
        };
        let method = self.build_method_model_from_node(
            class,
            method,
            cfg,
            exception_contracts.get(&reference).map(Vec::as_slice),
            None,
            None,
            None,
            OuterInstanceField::analyze(class).as_ref(),
        )?;
        let declaration = KotlinSingleMethodLowering::lower(
            &method,
            source_package_name(class),
            Some(class.class_type()),
            method_type_uses(&method),
            &self.source_abi,
            self.type_hierarchy.clone(),
            self.observer.clone(),
        )?;
        Ok(KotlinPrinter::new(self.config.indent.clone())
            .print_method_declaration(&declaration, 0)?)
    }

    /// Generate a class together with its nested inner classes, rendered as a
    /// single source file. Each inner class entry is `(ClassNode, methods)`
    /// in the same shape as the outer.
    pub(crate) fn generate_class_with_nested(
        &mut self,
        class: &ClassNode,
        methods: &mut [ClassMethodInput],
        inner: Vec<NestedClassInput>,
    ) -> Result<String, KotlinDecompilerError> {
        crate::profile_scope!("kotlin_backend.class.total", {
            self.generate_class_with_nested_impl(class, methods, inner)
        })
    }

    fn generate_class_with_nested_impl(
        &mut self,
        class: &ClassNode,
        methods: &mut [ClassMethodInput],
        inner: Vec<NestedClassInput>,
    ) -> Result<String, KotlinDecompilerError> {
        self.observer.checkpoint()?;
        let source_signatures = super::signature_inference::SourceSignatureInference::analyze(
            self.type_hierarchy.as_ref(),
            methods,
            &inner,
        );
        let (outer_methods, outer_instance) =
            crate::profile_scope!("kotlin_backend.class.outer_methods", {
                self.build_class_methods(class, methods, &source_signatures)
            })?;
        self.observer.checkpoint()?;
        self.class_stage(class.type_descriptor(), "build_outer_methods:done");
        let nested_models = crate::profile_scope!("kotlin_backend.class.nested_models", {
            self.build_nested_class_models(inner, &source_signatures)
        })?;
        self.observer.checkpoint()?;
        self.class_stage(class.type_descriptor(), "build_nested_models:done");
        let mut class_model = crate::profile_scope!("kotlin_backend.class.model", {
            KotlinClassModel::from_class_node(class, outer_methods, outer_instance)
                .map(|model| model.with_nested(nested_models))
        })?;
        self.observer.checkpoint()?;
        class_model.assign_lexical_type_names(&self.source_abi);
        self.class_stage(class.type_descriptor(), "class_model:done");
        crate::profile_scope!("kotlin_backend.class.render", {
            self.observer.checkpoint()?;
            self.render_class_model(&class_model)
        })
    }

    fn build_nested_class_models(
        &self,
        inputs: Vec<NestedClassInput>,
        source_signatures: &super::signature_inference::SourceSignatureInference<'_>,
    ) -> Result<Vec<KotlinClassModel>, KotlinDecompilerError> {
        let root_count = inputs.len();
        let mut pending = inputs
            .into_iter()
            .rev()
            .map(NestedModelTask::Build)
            .collect::<Vec<_>>();
        let mut results = Vec::new();
        while let Some(task) = pending.pop() {
            self.observer.checkpoint()?;
            match task {
                NestedModelTask::Build(mut input) => {
                    self.class_stage(input.class.type_descriptor(), "build_nested_class:start");
                    let (methods, outer_instance) = self.build_class_methods(
                        &input.class,
                        &mut input.methods,
                        source_signatures,
                    )?;
                    let child_count = input.nested.len();
                    pending.push(NestedModelTask::Finish {
                        class: input.class,
                        methods,
                        outer_instance,
                        child_count,
                    });
                    pending.extend(input.nested.into_iter().rev().map(NestedModelTask::Build));
                }
                NestedModelTask::Finish {
                    class,
                    methods,
                    outer_instance,
                    child_count,
                } => {
                    let start = results.len().checked_sub(child_count).ok_or(
                        KotlinDecompilerError::MalformedNestedClassStack {
                            expected: child_count,
                            actual: results.len(),
                        },
                    )?;
                    let children = results.drain(start..).collect();
                    self.class_stage(class.type_descriptor(), "build_nested_class:done");
                    results.push(
                        KotlinClassModel::from_class_node(&class, methods, outer_instance)?
                            .as_nested_source_member(&class)
                            .with_nested(children),
                    );
                }
            }
        }
        if results.len() != root_count {
            return Err(KotlinDecompilerError::MalformedNestedClassStack {
                expected: root_count,
                actual: results.len(),
            });
        }
        Ok(results)
    }

    fn build_class_methods(
        &self,
        class: &ClassNode,
        methods: &mut [ClassMethodInput],
        source_signatures: &super::signature_inference::SourceSignatureInference<'_>,
    ) -> Result<(Vec<KotlinMethodModel>, Option<OuterInstanceField>), KotlinDecompilerError> {
        let outer_instance = OuterInstanceField::analyze_cfgs(
            class,
            methods
                .iter()
                .filter_map(|input| input.cfg().map(|cfg| (input.method(), cfg))),
        )
        .or_else(|| OuterInstanceField::analyze(class));
        let exception_contracts = super::exception_contract::DeclaredExceptionAnalysis::new(
            self.source_abi.as_ref(),
            self.type_hierarchy.as_ref(),
        )
        .solve(
            class,
            methods
                .iter()
                .filter_map(|input| input.cfg().map(|cfg| (input.method(), cfg))),
        );
        let builder = ClassMethodBuilder {
            decompiler: self,
            class,
            source_signatures,
            exception_contracts: &exception_contracts,
            outer_instance: outer_instance.as_ref(),
            function_object: super::FunctionObjectClass::analyze(class),
        };
        let decoded_results = if methods.len() < 8 {
            methods
                .iter_mut()
                .filter_map(ClassMethodInput::decoded_mut)
                .filter_map(|(method, cfg)| builder.build(method, cfg))
                .collect::<Vec<_>>()
        } else {
            methods
                .par_iter_mut()
                .filter_map(ClassMethodInput::decoded_mut)
                .filter_map(|(method, cfg)| builder.build(method, cfg))
                .collect::<Vec<_>>()
        };
        let mut decoded = decoded_results
            .into_iter()
            .collect::<std::collections::BTreeMap<_, _>>();
        let inputs = methods
            .iter()
            .enumerate()
            .map(|(index, input)| {
                let method = input.method();
                ((method.info.name.clone(), method.info.descriptor()), index)
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        let mut built = Vec::new();
        for method in class
            .methods()
            .iter()
            .filter(|method| !method.access_flags.is_bridge())
        {
            if method.code().is_none() {
                let declaration = match KotlinMethodDeclaration::from_method_node(class, method) {
                    Ok(declaration) => declaration,
                    Err(error) => {
                        let failure =
                            MethodRecoveryFailure::new(MethodRecoveryStage::Metadata, error);
                        failure.observe(
                            self.observer.as_ref(),
                            class.type_descriptor(),
                            &method.info.name,
                            &method.info.descriptor(),
                        );
                        KotlinMethodDeclaration::from_method_node_erased(class, method)
                    }
                };
                built.push(KotlinMethodModel::from_declaration(declaration));
                continue;
            }
            let key = (method.info.name.clone(), method.info.descriptor());
            let Some(index) = inputs.get(&key).copied() else {
                let failure = MethodRecoveryFailure::new(
                    MethodRecoveryStage::Decode,
                    "class method input is missing",
                );
                failure.observe(
                    self.observer.as_ref(),
                    class.type_descriptor(),
                    &method.info.name,
                    &method.info.descriptor(),
                );
                built.push(KotlinMethodModel::from_failure(class, method, failure));
                continue;
            };
            if let Some(failure) = methods[index].failure().cloned() {
                let decoded_method = methods[index].method();
                failure.observe(
                    self.observer.as_ref(),
                    class.type_descriptor(),
                    &decoded_method.info.name,
                    &decoded_method.info.descriptor(),
                );
                built.push(KotlinMethodModel::from_failure(
                    class,
                    decoded_method,
                    failure,
                ));
                continue;
            }
            let model = decoded
                .remove(&key)
                .expect("decoded method result is missing");
            match model {
                Ok(model) => built.push(model),
                Err(error) if error.is_cancelled() => return Err(error),
                Err(error) => {
                    let failure = MethodRecoveryFailure::new(MethodRecoveryStage::Semantics, error);
                    failure.observe(
                        self.observer.as_ref(),
                        class.type_descriptor(),
                        &method.info.name,
                        &method.info.descriptor(),
                    );
                    built.push(KotlinMethodModel::from_failure(class, method, failure));
                }
            }
        }
        Ok((built, outer_instance))
    }

    fn build_method_model(
        &self,
        cfg: &mut CFG,
    ) -> Result<KotlinMethodModel, KotlinDecompilerError> {
        let declaration = KotlinMethodDeclaration::from_cfg(cfg);
        let options = declaration.body_options(None);
        let body = MethodBodyPipeline::new(self.type_hierarchy.as_ref(), self.observer.as_ref())
            .analyze(cfg)?;
        method_model_from_body_analysis(declaration, body, options)
    }

    fn build_method_model_from_node(
        &self,
        class: &ClassNode,
        method: &MethodNode,
        cfg: &mut CFG,
        inferred_exceptions: Option<&[crate::ir::ArgType]>,
        inferred_parameter_types: Option<&[Option<crate::ir::ArgType>]>,
        inferred_return_type: Option<&crate::ir::ArgType>,
        function_interface: Option<&crate::ir::generic_types::JvmTypeSignature>,
        outer_instance: Option<&OuterInstanceField>,
    ) -> Result<KotlinMethodModel, KotlinDecompilerError> {
        crate::profile_scope!("kotlin_backend.method.total", {
            self.build_method_model_from_node_impl(
                class,
                method,
                cfg,
                inferred_exceptions,
                inferred_parameter_types,
                inferred_return_type,
                function_interface,
                outer_instance,
            )
        })
    }

    fn build_method_model_from_node_impl(
        &self,
        class: &ClassNode,
        method: &MethodNode,
        cfg: &mut CFG,
        inferred_exceptions: Option<&[crate::ir::ArgType]>,
        inferred_parameter_types: Option<&[Option<crate::ir::ArgType>]>,
        inferred_return_type: Option<&crate::ir::ArgType>,
        function_interface: Option<&crate::ir::generic_types::JvmTypeSignature>,
        outer_instance: Option<&OuterInstanceField>,
    ) -> Result<KotlinMethodModel, KotlinDecompilerError> {
        let mut declaration = crate::profile_scope!("kotlin_backend.method.declaration", {
            KotlinMethodDeclaration::from_method_node(class, method)
        })?;
        if declaration.throws.is_empty() {
            declaration
                .throws
                .extend(inferred_exceptions.into_iter().flatten().cloned());
        }
        if declaration.access_flags.is_synthetic()
            || super::FunctionObjectClass::analyze(class)
            || function_interface.is_some()
        {
            declaration.source_parameter_types = inferred_parameter_types
                .map(<[Option<crate::ir::ArgType>]>::to_vec)
                .unwrap_or_else(|| vec![None; declaration.parameters.len()]);
            declaration.source_return_type = inferred_return_type.cloned();
            declaration.function_interface = function_interface.cloned();
        }
        // `from_method_node` does not see the decoded debug stream, so attach
        // source parameter names here. SSA bindings remain owned exclusively
        // by MethodBodyAnalysis.
        crate::profile_scope!("kotlin_backend.method.debug_params", {
            let param_names = collect_param_debug_names(cfg);
            for (idx, parameter) in declaration.parameters.iter_mut().enumerate() {
                parameter.name = param_names
                    .get(idx)
                    .and_then(|name| name.as_deref())
                    .map(crate::language::kotlin::KotlinIdentifier::from_dex);
            }
        });
        let mut options = declaration.body_options(Some(class));
        if let Some(outer_instance) = outer_instance {
            options.outer_instance = Some(outer_instance.clone());
        }
        let body = crate::profile_scope!("kotlin_backend.method.pipeline", {
            MethodBodyPipeline::new(self.type_hierarchy.as_ref(), self.observer.as_ref())
                .analyze(cfg)
        })?;
        crate::profile_scope!("kotlin_backend.method.kotlin_model", {
            KotlinMethodModel::from_body_analysis_with_options(declaration, body, options)
        })
    }

    fn render_class_model(
        &self,
        class: &KotlinClassModel,
    ) -> Result<String, KotlinDecompilerError> {
        let unit = crate::profile_scope!("kotlin_backend.class.lower", {
            KotlinCompilationUnitLowering::lower(
                class,
                &self.source_abi,
                self.type_hierarchy.clone(),
                self.observer.clone(),
            )
        })?;
        crate::profile_scope!("kotlin_backend.class.print", {
            Ok(KotlinPrinter::new(self.config.indent.clone()).print_compilation_unit(&unit)?)
        })
    }

    fn class_stage(&self, class: &str, stage: &'static str) {
        self.observer
            .observe(crate::ir::AnalysisEvent::ClassStage { class, stage });
    }

    fn method_stage(&self, class: &str, method: &str, descriptor: &str, stage: &'static str) {
        self.observer
            .observe(crate::ir::AnalysisEvent::MethodStage {
                class,
                method,
                descriptor,
                stage,
            });
    }
}

enum NestedModelTask {
    Build(NestedClassInput),
    Finish {
        class: ClassNode,
        methods: Vec<KotlinMethodModel>,
        outer_instance: Option<OuterInstanceField>,
        child_count: usize,
    },
}

fn method_model_from_body_analysis(
    declaration: KotlinMethodDeclaration,
    body: MethodBodyAnalysis,
    options: super::kotlin_model::MethodBodyOptions,
) -> Result<KotlinMethodModel, KotlinDecompilerError> {
    KotlinMethodModel::from_body_analysis_with_options(declaration, body, options)
}

fn source_package_name(class: &ClassNode) -> Option<&str> {
    let package = class.package();
    (!package.is_empty()).then_some(package)
}

fn method_type_uses(method: &KotlinMethodModel) -> Vec<crate::ir::ty::ArgType> {
    KotlinMethodTypeUses::collect(method)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::{ClassMethodInput, MethodRecoveryFailure, MethodRecoveryStage};
    use crate::frontend::{AccessInfo, ClassInfo, MethodCode, MethodInfo};
    use crate::ir::ArgType;

    #[test]
    fn class_generation_isolates_failed_method() {
        let descriptor = "Lexample/Partial;";
        let info = ClassInfo::from_type_descriptor(descriptor).expect("class descriptor");
        let mut class = ClassNode::new(0, info, AccessInfo::for_class(0x0001));
        let method = MethodNode::new(
            0,
            MethodInfo::new(
                descriptor.to_string(),
                "broken".to_string(),
                Vec::new(),
                ArgType::INT,
            ),
            AccessInfo::for_method(0x0009),
        )
        .with_code(MethodCode {
            registers_size: 0,
            ins_size: 0,
            outs_size: 0,
            insns: Vec::new(),
            tries: Vec::new(),
            debug_info: None,
        });
        class.add_method(method.clone());
        let mut methods = vec![ClassMethodInput::failed(
            method,
            MethodRecoveryFailure::new(MethodRecoveryStage::Semantics, "test failure"),
        )];

        let source = KotlinDecompiler::new(Default::default())
            .generate_class_with_nested(&class, &mut methods, Vec::new())
            .expect("partial class source");

        assert!(source.contains("class Partial"));
        assert!(source.contains("broken()"));
        assert!(source.contains("Method could not be decompiled during semantic recovery"));
    }
}
