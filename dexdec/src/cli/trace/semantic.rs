//! Trace-semantic command: region-owned semantic IR and value recovery.

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use crate::ir::{
    AnalysisEvent, AnalysisObserver, BlockId, RegionId, SemanticNode, SemanticStage,
    SemanticVisitor,
};
use crate::{DecompilerContext, JavaDecompilerConfig, KotlinDecompilerConfig, SourceLanguage};

use super::super::error::{cli_err, CliResult};
use super::super::model::TraceSemanticRequest;
use super::super::output::CliHost;
use super::format::{format_block_id_list, format_trace_block};

/// Traces semantic IR, value recovery, and source-type diagnostics.
///
/// Preserves the historical CLI behavior of always lowering through the Kotlin
/// decompiler config for this diagnostic command.
pub struct TraceSemanticCommand;

impl TraceSemanticCommand {
    pub fn run(host: &mut impl CliHost, request: &TraceSemanticRequest) -> CliResult<()> {
        let trace = Arc::new(SemanticTrace::default());
        let mut context = DecompilerContext::from_file(&request.input)?;
        if context.load_class(&request.class)?.is_none() {
            return Err(cli_err(format!("Class not found: {}", request.class)));
        }
        let generated = match request.language {
            SourceLanguage::Java => context.decompile_java_method_with_config_and_observer(
                &request.class,
                &request.method,
                request.descriptor.as_deref(),
                &JavaDecompilerConfig::default(),
                trace.clone(),
            ),
            SourceLanguage::Kotlin => context.decompile_method_with_config_and_observer(
                &request.class,
                &request.method,
                request.descriptor.as_deref(),
                &KotlinDecompilerConfig::default(),
                trace.clone(),
            ),
        }
        .map_err(|error| super::super::error::CliError::command(error.to_string()))
        .and_then(|source| {
            source.ok_or_else(|| {
                cli_err(format!(
                    "Method not found: {}->{}",
                    request.class, request.method
                ))
            })
        });
        let mut result = format!(
            "=== semantic IR for {}.{} ===\n",
            request.class, request.method
        );
        for region_graph in trace.region_graphs()? {
            result.push_str(&region_graph);
        }
        for region_cfg in trace.region_cfgs()? {
            result.push_str(&region_cfg);
        }
        for child in trace.region_children()? {
            result.push_str(&format!(
                "\n[RegionChild owner={} child={} entry={} stage={}]\n{}\n",
                child.owner, child.child, child.entry, child.stage, child.identities
            ));
        }
        for (stage, body) in trace.snapshots()? {
            result.push_str(&format!("\n[{stage:?}]\n{body}\n"));
        }
        for diagnostics in trace.value_recovery()? {
            result.push_str(&format!(
                "\n[ValueRecovery]\ncandidates={} recovered={} specialized={} decisions={} exact={} bounded={}\n",
                diagnostics.gated_candidates,
                diagnostics.gated_recovered,
                diagnostics.gated_specialized,
                diagnostics.decision_nodes,
                diagnostics.exact_partition_searches,
                diagnostics.bounded_partition_searches,
            ));
            for rejection in diagnostics.rejected {
                result.push_str(&format!(
                    "  {} v{}_{}: {:?}\n",
                    rejection.block, rejection.register, rejection.version, rejection.reason,
                ));
            }
        }
        for types in trace.source_types()? {
            result.push_str("\n[SourceTypes]\nobject types:\n");
            for (implementation, source) in types.object_types {
                result.push_str(&format!("  {implementation}: {source}\n"));
            }
            result.push_str("definition variables:\n");
            for (variable, ty) in types.definition_variables {
                result.push_str(&format!("  v{variable}: {ty}\n"));
            }
            result.push_str("definition values:\n");
            for (register, version, ty) in types.definition_values {
                result.push_str(&format!("  r{register}_{version}: {ty}\n"));
            }
            result.push_str("variables:\n");
            for (variable, ty) in types.variables {
                result.push_str(&format!("  v{variable}: {ty}\n"));
            }
            result.push_str("values:\n");
            for (register, version, ty) in types.values {
                result.push_str(&format!("  r{register}_{version}: {ty}\n"));
            }
            result.push_str("requirements:\n");
            for (variable, ty) in types.requirements {
                result.push_str(&format!("  v{variable}: {ty}\n"));
            }
            result.push_str("value requirements:\n");
            for (register, version, ty) in types.value_requirements {
                result.push_str(&format!("  r{register}_{version}: {ty}\n"));
            }
            result.push_str("equations:\n");
            for equation in types.equations {
                let version = equation
                    .version
                    .map(|version| version.to_string())
                    .unwrap_or_else(|| "?".to_string());
                let edge = if equation.edge_copy { " edge" } else { "" };
                result.push_str(&format!(
                    "  v{} <- r{}_{}: {}{}\n",
                    equation.variable, equation.register, version, equation.erased_type, edge
                ));
            }
            result.push_str("requirement candidates:\n");
            for (variable, candidates) in types.requirement_candidates {
                result.push_str(&format!("  v{variable}: {}\n", candidates.join(" | ")));
            }
            result.push_str("invocations:\n");
            for invocation in types.invocations {
                if invocation.resolved {
                    let inputs = invocation
                        .inputs
                        .into_iter()
                        .map(|input| input.unwrap_or_else(|| "?".to_string()))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let output = invocation.output.unwrap_or_else(|| "?".to_string());
                    let owner = if invocation.owner_parameters.is_empty() {
                        String::new()
                    } else {
                        format!(
                            " owner=<{}> bounds={}",
                            invocation.owner_parameters.join(", "),
                            invocation
                                .owner_bounds_satisfied
                                .map(|satisfied| satisfied.to_string())
                                .unwrap_or_else(|| "?".to_string())
                        )
                    };
                    result.push_str(&format!(
                        "  {}: ({inputs}) -> {output}{owner}\n",
                        invocation.reference,
                    ));
                } else {
                    result.push_str(&format!("  {}: unresolved\n", invocation.reference));
                }
            }
        }
        match &generated {
            Ok(source) => {
                result.push_str("\n[Kotlin]\n");
                result.push_str(source);
            }
            Err(error) => result.push_str(&format!("\n[Error]\n{error}\n")),
        }

        host.emit_or_write(request.output.as_deref(), &result)?;
        generated.map(|_| ())
    }
}

#[derive(Default)]
struct SemanticTrace {
    snapshots: Mutex<Vec<(SemanticStage, String)>>,
    region_graphs: Mutex<Vec<String>>,
    region_cfgs: Mutex<Vec<String>>,
    region_children: Mutex<Vec<RegionChildTrace>>,
    value_recovery: Mutex<Vec<crate::ir::ValueRecoveryDiagnostics>>,
    source_types: Mutex<Vec<crate::ir::SourceTypeDiagnostics>>,
}

#[derive(Clone)]
struct RegionChildTrace {
    owner: RegionId,
    child: RegionId,
    entry: BlockId,
    stage: &'static str,
    identities: String,
}

impl SemanticTrace {
    fn region_graphs(&self) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        self.region_graphs
            .lock()
            .map(|regions| regions.clone())
            .map_err(|_| "region graph trace lock is poisoned".into())
    }

    fn region_cfgs(&self) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        self.region_cfgs
            .lock()
            .map(|regions| regions.clone())
            .map_err(|_| "region CFG trace lock is poisoned".into())
    }

    fn snapshots(&self) -> Result<Vec<(SemanticStage, String)>, Box<dyn std::error::Error>> {
        self.snapshots
            .lock()
            .map(|snapshots| snapshots.clone())
            .map_err(|_| "semantic trace lock is poisoned".into())
    }

    fn source_types(
        &self,
    ) -> Result<Vec<crate::ir::SourceTypeDiagnostics>, Box<dyn std::error::Error>> {
        self.source_types
            .lock()
            .map(|types| types.clone())
            .map_err(|_| "source type trace lock is poisoned".into())
    }

    fn region_children(&self) -> Result<Vec<RegionChildTrace>, Box<dyn std::error::Error>> {
        self.region_children
            .lock()
            .map(|children| children.clone())
            .map_err(|_| "region child trace lock is poisoned".into())
    }

    fn value_recovery(
        &self,
    ) -> Result<Vec<crate::ir::ValueRecoveryDiagnostics>, Box<dyn std::error::Error>> {
        self.value_recovery
            .lock()
            .map(|diagnostics| diagnostics.clone())
            .map_err(|_| "value recovery trace lock is poisoned".into())
    }
}

impl AnalysisObserver for SemanticTrace {
    fn is_enabled(&self, kind: crate::ir::AnalysisEventKind) -> bool {
        matches!(
            kind,
            crate::ir::AnalysisEventKind::Semantics
                | crate::ir::AnalysisEventKind::Regions
                | crate::ir::AnalysisEventKind::RegionCfg
                | crate::ir::AnalysisEventKind::RegionChild
                | crate::ir::AnalysisEventKind::SourceTypes
                | crate::ir::AnalysisEventKind::ValueRecovery
        )
    }

    fn observe(&self, event: AnalysisEvent<'_>) {
        match event {
            AnalysisEvent::Regions { graph, .. } => {
                let mut rendered = String::from("\n[Regions]\n");
                for region in graph.tree().regions() {
                    rendered.push_str(&format!(
                        "  {} {:?} parent={:?} entry={:?} follow={:?} blocks={} children={:?}\n",
                        region.id,
                        region.kind,
                        region.parent,
                        region.entry,
                        region.kind.follow(),
                        format_block_id_list(&region.blocks.iter().copied().collect::<Vec<_>>()),
                        region.children,
                    ));
                }
                if let Ok(mut regions) = self.region_graphs.lock() {
                    regions.push(rendered);
                }
            }
            AnalysisEvent::RegionCfg {
                region,
                kind,
                source_cfg,
                region_cfg,
                mapping,
                open_flows,
            } => {
                let mut rendered = format!("\n[RegionCfg region={region} kind={kind:?}]\n");
                for block in region_cfg.block_ids() {
                    rendered.push_str(&format_trace_block(region_cfg, block));
                }
                let contractions = mapping
                    .iter()
                    .filter(|(block, representative)| block != representative)
                    .collect::<Vec<_>>();
                if !contractions.is_empty() {
                    rendered.push_str(&format!("  contractions={contractions:?}\n"));
                }
                let source_edges = mapping
                    .iter()
                    .filter(|(block, representative)| block == representative)
                    .filter_map(|(block, _)| {
                        let successors = source_cfg.successors_with_kind(*block);
                        (!successors.is_empty()).then_some((*block, successors))
                    })
                    .collect::<Vec<_>>();
                if !source_edges.is_empty() {
                    rendered.push_str(&format!("  source-edges={source_edges:?}\n"));
                }
                if !open_flows.is_empty() {
                    rendered.push_str(&format!("  open-flows={open_flows:?}\n"));
                }
                if let Ok(mut regions) = self.region_cfgs.lock() {
                    regions.push(rendered);
                }
            }
            AnalysisEvent::Semantics { stage, root, .. } => {
                if let Ok(mut snapshots) = self.snapshots.lock() {
                    snapshots.push((stage, format!("{root:#?}")));
                }
            }
            AnalysisEvent::RegionChild {
                owner,
                child,
                entry,
                stage,
                root,
            } => {
                if let Ok(mut children) = self.region_children.lock() {
                    children.push(RegionChildTrace {
                        owner,
                        child,
                        entry,
                        stage,
                        identities: ControlIdentitySummary::of(root),
                    });
                }
            }
            AnalysisEvent::SourceTypes(types) => {
                if let Ok(mut source_types) = self.source_types.lock() {
                    source_types.push(types.clone());
                }
            }
            AnalysisEvent::ValueRecovery { diagnostics, .. } => {
                if let Ok(mut recovered) = self.value_recovery.lock() {
                    recovered.push(diagnostics.clone());
                }
            }
            _ => {}
        }
    }
}

#[derive(Default)]
struct ControlIdentitySummary {
    blocks: BTreeSet<BlockId>,
    edge_blocks: BTreeSet<BlockId>,
}

impl ControlIdentitySummary {
    fn of(root: &SemanticNode) -> String {
        let mut summary = Self::default();
        summary.visit_node(root);
        format!(
            "blocks={} edge-blocks={}",
            format_block_id_list(&summary.blocks.into_iter().collect::<Vec<_>>()),
            format_block_id_list(&summary.edge_blocks.into_iter().collect::<Vec<_>>())
        )
    }
}

impl SemanticVisitor for ControlIdentitySummary {
    fn enter_node(&mut self, node: &SemanticNode) {
        match node {
            SemanticNode::BasicBlock(block) => {
                self.blocks.insert(block.id);
            }
            SemanticNode::Leave(leave) => {
                self.edge_blocks.extend(
                    leave
                        .edge
                        .into_iter()
                        .flat_map(|edge| [edge.source, edge.target])
                        .chain(leave.origin),
                );
            }
            _ => {}
        }
    }
}
