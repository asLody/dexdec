use crate::analysis::{value_recovery::ValueRecovery, SemanticTransform};
use crate::ir::semantic::SemanticDeadCodeElimination;
use crate::ir::{
    analysis::{SourceVariableAllocation, TypeHierarchy, TypeSolver},
    cfg::CFG,
    passes::CfgPipeline,
    structure::RegionReducer,
    ArgType, ExceptionAnalyzer, MemberReference, RegionGraphBuilder, SemanticMethod, SemanticNode,
    SemanticVisitor, SourceSyntaxSemantics, StringBuildingRecovery,
};
use crate::language::kotlin::{KotlinValueSyntax, SourceSyntaxRecovery};

use super::KotlinDecompilerError;

pub(super) struct MethodBodyAnalysis {
    pub semantic: SemanticMethod<SourceSyntaxSemantics>,
    pub is_static: bool,
    pub this_code_var: Option<u32>,
    pub parameter_code_vars: Vec<Option<u32>>,
    pub type_uses: std::collections::BTreeSet<ArgType>,
}

pub(super) struct MethodBodyPipeline<'a> {
    hierarchy: &'a dyn TypeHierarchy,
    observer: &'a dyn crate::ir::AnalysisObserver,
}

impl<'a> MethodBodyPipeline<'a> {
    pub(super) fn new(
        hierarchy: &'a dyn TypeHierarchy,
        observer: &'a dyn crate::ir::AnalysisObserver,
    ) -> Self {
        Self {
            hierarchy,
            observer,
        }
    }

    pub(super) fn analyze(
        &self,
        cfg: &mut CFG,
    ) -> Result<MethodBodyAnalysis, KotlinDecompilerError> {
        crate::profile_scope!("method_pipeline.total", self.analyze_impl(cfg))
    }

    fn analyze_impl(&self, cfg: &mut CFG) -> Result<MethodBodyAnalysis, KotlinDecompilerError> {
        self.observer.checkpoint()?;
        let cfg_pipeline = CfgPipeline::new(self.hierarchy);
        let cfg_analysis = crate::profile_scope!("method_pipeline.cfg_ssa", {
            cfg_pipeline.analyze_observed(cfg, self.observer)
        })?;
        self.observe_stage(cfg, "cfg_ssa:done")?;
        let ssa_values = cfg_analysis.values;

        let exception_analysis = crate::profile_scope!("method_pipeline.exception_analysis", {
            ExceptionAnalyzer::new(cfg, &ssa_values, self.hierarchy).analyze()
        })?;
        self.observe_stage(cfg, "exceptions:done")?;
        self.observer.observe(crate::ir::AnalysisEvent::Exceptions {
            cfg,
            analysis: &exception_analysis,
        });
        self.observer
            .observe(crate::ir::AnalysisEvent::ControlFlow(cfg));

        let region_graph =
            RegionGraphBuilder::new(cfg, &exception_analysis, &ssa_values).build()?;
        self.observe_stage(cfg, "regions:done")?;
        self.observer.observe(crate::ir::AnalysisEvent::Regions {
            cfg,
            graph: &region_graph,
        });
        let body = crate::profile_scope!("method_pipeline.structure", {
            RegionReducer::new(cfg, &region_graph, self.observer)
                .and_then(|reducer| reducer.reduce())
                .map_err(KotlinDecompilerError::from)
        })?;
        self.observe_stage(cfg, "structure:done")?;
        self.observe_semantics(cfg, crate::ir::SemanticStage::Structured, &body);
        let semantic = SemanticMethod::from_ssa(body, region_graph, ssa_values);
        semantic.verify()?;
        let mut value_recovery = ValueRecovery::new(cfg)?;
        let semantic = crate::profile_scope!("method_pipeline.value_recovery", {
            value_recovery.transform(semantic)
        })?;
        self.observer
            .observe(crate::ir::AnalysisEvent::ValueRecovery {
                cfg,
                diagnostics: value_recovery.diagnostics(),
            });
        self.observe_stage(cfg, "values:done")?;
        semantic.verify()?;
        self.observe_semantics(
            cfg,
            crate::ir::SemanticStage::ValuesRecovered,
            semantic.body(),
        );
        let types = crate::profile_scope!("method_pipeline.type_recovery", {
            TypeSolver::new(self.hierarchy).solve(
                cfg,
                semantic.state().values(),
                semantic.state().constants(),
            )
        })?;
        self.observe_stage(cfg, "types:done")?;
        let source_variables = SourceVariableAllocation::analyze(
            cfg,
            semantic.state().values(),
            semantic.state().constants(),
            semantic.state().recovered_phis(),
            semantic.body(),
            &types,
            self.hierarchy,
            semantic.state().regions(),
        )?;
        self.observe_stage(cfg, "source_analysis:done")?;
        let mut semantic = crate::profile_scope!("method_pipeline.source_variables", {
            source_variables.apply(cfg, semantic, types, self.hierarchy)
        })?;
        value_recovery.bind_source_inputs(cfg);
        self.observe_stage(cfg, "source_apply:done")?;
        semantic.verify()?;
        self.observe_semantics(
            cfg,
            crate::ir::SemanticStage::SourceAllocated,
            semantic.body(),
        );
        crate::profile_scope!("method_pipeline.source_prepare", {
            value_recovery.prepare_source(&mut semantic)
        })?;
        if cfg.method().descriptor().return_type == ArgType::VOID {
            semantic.normalize_void_method_completion()?;
        }
        self.observe_stage(cfg, "source_prepare:done")?;
        semantic.verify()?;
        self.observe_semantics(
            cfg,
            crate::ir::SemanticStage::SourceVariables,
            semantic.body(),
        );
        let mut semantic = crate::profile_scope!("method_pipeline.kotlin_syntax", {
            SourceSyntaxRecovery::new(self.hierarchy).transform(semantic)
        })?;
        self.observe_stage(cfg, "kotlin_syntax:done")?;
        semantic.verify()?;
        self.observe_semantics(cfg, crate::ir::SemanticStage::SourceSyntax, semantic.body());
        crate::profile_scope!("method_pipeline.java_value_fixed_point", {
            KotlinValueFixedPoint::new(&mut value_recovery, self.hierarchy).apply(&mut semantic)
        })?;
        self.observe_stage(cfg, "kotlin_values:done")?;
        semantic.verify()?;
        semantic.compact()?;
        self.observe_stage(cfg, "compact:done")?;
        semantic.verify()?;
        self.observe_semantics(cfg, crate::ir::SemanticStage::Normalized, semantic.body());
        if cfg.method().descriptor().return_type != ArgType::VOID
            && crate::ir::semantic::SemanticCompletion::analyze(semantic.body())
                .can_complete_normally()
        {
            self.observer
                .observe(crate::ir::AnalysisEvent::IncompleteMethod {
                    cfg,
                    stage: crate::ir::SemanticStage::Normalized,
                });
        }
        let type_uses = MethodTypeUses::collect(&semantic)?;
        self.observe_stage(cfg, "type_uses:done")?;

        Ok(MethodBodyAnalysis {
            semantic,
            is_static: cfg.method().is_static(),
            this_code_var: cfg.this_code_variable(),
            parameter_code_vars: cfg.parameter_code_variables().to_vec(),
            type_uses,
        })
    }

    fn observe_semantics(&self, cfg: &CFG, stage: crate::ir::SemanticStage, root: &SemanticNode) {
        self.observer
            .observe(crate::ir::AnalysisEvent::Semantics { cfg, stage, root });
    }

    fn observe_stage(&self, cfg: &CFG, stage: &'static str) -> Result<(), KotlinDecompilerError> {
        self.observer
            .observe(crate::ir::AnalysisEvent::MethodPipeline { cfg, stage });
        self.observer.checkpoint()?;
        Ok(())
    }
}

/// Alternates source-identity scheduling and Kotlin expression canonicalization
/// until neither can expose another simplification.
///
/// Both components are monotone: scheduling removes definitions or substitutes
/// their uses, while syntax recovery replaces expressions with cheaper
/// equivalents. The fixed point therefore terminates without an iteration cap.
struct KotlinValueFixedPoint<'a, 'hierarchy> {
    values: &'a mut ValueRecovery,
    syntax: KotlinValueSyntax<'hierarchy>,
}

impl<'a, 'hierarchy> KotlinValueFixedPoint<'a, 'hierarchy> {
    fn new(values: &'a mut ValueRecovery, hierarchy: &'hierarchy dyn TypeHierarchy) -> Self {
        Self {
            values,
            syntax: KotlinValueSyntax::new(hierarchy),
        }
    }

    fn apply(
        &mut self,
        method: &mut SemanticMethod<SourceSyntaxSemantics>,
    ) -> Result<bool, KotlinDecompilerError> {
        let mut changed = false;
        loop {
            let values_changed =
                crate::profile_scope!("java_value.values", self.values.recover_source(method))?;
            let building_changed = crate::profile_scope!(
                "java_value.string_building",
                StringBuildingRecovery::apply(method.body_mut())
            )?;
            let syntax_changed =
                crate::profile_scope!("java_value.syntax", self.syntax.apply(method))?;
            let dead_changed = crate::profile_scope!(
                "java_value.dce",
                SemanticDeadCodeElimination::apply(method.body_mut())
            )?;
            changed |= values_changed || building_changed || syntax_changed || dead_changed;
            if building_changed || syntax_changed || dead_changed {
                continue;
            }
            let conditions_changed = crate::profile_scope!(
                "java_value.conditions",
                self.syntax.reduce_conditions(method)
            )?;
            changed |= conditions_changed;
            if !conditions_changed {
                return Ok(changed);
            }
        }
    }
}

struct MethodTypeUses<'a> {
    types: &'a crate::ir::analysis::SourceTypeEnvironment,
    uses: std::collections::BTreeSet<ArgType>,
    error: Option<crate::ir::analysis::TypeConstraintError>,
}

impl<'a> MethodTypeUses<'a> {
    fn collect(
        method: &'a SemanticMethod<SourceSyntaxSemantics>,
    ) -> Result<std::collections::BTreeSet<ArgType>, KotlinDecompilerError> {
        let mut uses = method
            .state()
            .types()
            .known_types()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>();
        uses.extend([
            ArgType::object("java/lang/Float"),
            ArgType::object("java/lang/Double"),
            ArgType::object("java/lang/Long"),
        ]);
        let mut collector = Self {
            types: method.state().types(),
            uses,
            error: None,
        };
        collector.visit_node(method.body());
        match collector.error {
            Some(error) => Err(error.into()),
            None => Ok(collector.uses),
        }
    }

    fn insert(&mut self, ty: &ArgType) {
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            if !ty.is_known() {
                continue;
            }
            self.uses.insert(ty.clone());
            if let ArgType::Array(element) = ty {
                pending.push(element);
            }
        }
    }
}

impl SemanticVisitor for MethodTypeUses<'_> {
    fn enter_node(&mut self, node: &SemanticNode) {
        let catches = match node {
            SemanticNode::Try { catches, .. } => Some(catches.as_slice()),
            _ => None,
        };
        if let Some(catches) = catches {
            for ty in catches
                .iter()
                .flat_map(|catch| catch.exception_types.iter())
            {
                self.insert(ty);
            }
        }
    }

    fn enter_operation(&mut self, operation: &crate::ir::SemanticOperation) {
        if let Some(result) = &operation.result {
            match self.types.register_type(result).cloned() {
                Ok(ty) => self.insert(&ty),
                Err(error) if self.error.is_none() => self.error = Some(error),
                Err(_) => {}
            }
        }
        self.insert_option(operation.payload.class_type.as_ref());
        self.insert_option(operation.payload.cast_type.as_ref());
        match operation.payload.reference.as_ref() {
            Some(MemberReference::Field(field)) => {
                self.insert(&field.owner);
                self.insert(&field.field_type);
            }
            Some(MemberReference::Method(method)) => {
                self.insert(&method.owner);
                for ty in &method.descriptor.parameters {
                    self.insert(ty);
                }
                self.insert(&method.descriptor.return_type);
            }
            None => {}
        }
    }

    fn visit_register(&mut self, register: &crate::ir::RegisterArg) {
        match self.types.register_type(register).cloned() {
            Ok(ty) => self.insert(&ty),
            Err(error) if self.error.is_none() => self.error = Some(error),
            Err(_) => {}
        }
    }

    fn visit_binding(
        &mut self,
        _kind: crate::ir::SemanticBindingKind,
        register: &crate::ir::RegisterArg,
    ) {
        self.insert(&register.ty);
        self.visit_register(register);
    }
}

impl MethodTypeUses<'_> {
    fn insert_option(&mut self, ty: Option<&ArgType>) {
        if let Some(ty) = ty {
            self.insert(ty);
        }
    }
}
