//! Trace-regions command: structured region tree and leave edges.

use std::collections::BTreeMap;

use crate::ir::analysis::ControlContractions;
use crate::ir::passes::CfgPipeline;
use crate::ir::{ExceptionAnalyzer, RegionGraphBuilder, RegionTransferKind};

use super::super::error::CliResult;
use super::super::method_decode::MethodCfgDecoder;
use super::super::model::TraceRegionsRequest;
use super::super::output::CliHost;
use super::format::{
    format_block_id_list, format_block_map, format_block_relations, format_exception_region_map,
    format_optional_block_id, format_optional_insn_arg, format_region_id, format_region_id_list,
    format_region_kind,
};

/// Traces structured regions and cross-region leave edges for a method.
pub struct TraceRegionsCommand;

impl TraceRegionsCommand {
    pub fn run(host: &mut impl CliHost, request: &TraceRegionsRequest) -> CliResult<()> {
        let (mut cfg, hierarchy) = MethodCfgDecoder::decode_analysis(
            &request.input,
            &request.class,
            &request.method,
            request.descriptor.as_deref(),
        )?;
        let values = CfgPipeline::new(hierarchy.as_ref())
            .analyze(&mut cfg)
            .map_err(|error| super::super::error::CliError::command(error.to_string()))?
            .values;
        let exception_analysis = ExceptionAnalyzer::new(&cfg, &values, hierarchy.as_ref())
            .analyze()
            .map_err(|error| super::super::error::CliError::command(error.to_string()))?;
        let graph = match RegionGraphBuilder::new(&cfg, &exception_analysis, &values).build() {
            Ok(graph) => graph,
            Err(error) => {
                if let Some(out_path) = request.output.as_ref() {
                    let result = format!(
                        "=== exception analysis for {}.{} ===\n{:#?}\n\nregion-error: {}\n",
                        request.class, request.method, exception_analysis, error
                    );
                    host.write_file(out_path, &result)?;
                    host.note(&format!("Output written to: {}", out_path.display()))?;
                }
                return Err(super::super::error::CliError::command(error.to_string()));
            }
        };
        let region_tree = graph.tree();
        let exception_region_map = graph.exception_regions();
        let transfers = graph.transfers();
        let leaves = graph.leaves();
        let edge_argument_contractions = ControlContractions::for_edge_arguments(&cfg, &graph);
        let edge_argument_ports = values
            .phis()
            .iter()
            .filter_map(|phi| {
                edge_argument_contractions
                    .terminal(phi.block)
                    .filter(|terminal| *terminal != phi.block)
                    .map(|terminal| (phi.block, terminal))
            })
            .collect::<BTreeMap<_, _>>();

        let mut result = String::new();
        result.push_str(&format!(
            "=== region trace for {}.{} ===\n",
            request.class, request.method
        ));
        result.push_str(&format!(
            "cfg: blocks={} handlers={} exception_regions={}\n",
            cfg.blocks.len(),
            cfg.handlers.len(),
            exception_analysis.regions.len()
        ));
        result.push_str(&format!(
            "exception-region-map: {}\n\n",
            format_exception_region_map(&exception_region_map)
        ));
        result.push_str(&format!(
            "handler-adapters: {}\ncleanup-contractions: {}\nexceptional-contractions: {}\nedge-argument-ports: {}\nphi-copy-anchors: {}\n\n",
            format_block_map(graph.handler_adapters()),
            format_block_map(graph.cleanup_representatives()),
            format_block_relations(graph.exceptional_contractions()),
            format_block_map(&edge_argument_ports),
            format_block_id_list(
                &edge_argument_contractions
                    .phi_copy_anchors(&cfg)
                    .into_iter()
                    .collect::<Vec<_>>()
            )
        ));

        result.push_str("ssa-phis:\n");
        if values.phis().is_empty() {
            result.push_str("  <none>\n");
        } else {
            for phi in values.phis() {
                let inputs = phi
                    .inputs
                    .iter()
                    .map(|input| {
                        format!(
                            "{}:{:?}={:?}",
                            input.predecessor, input.edge_kind, input.value
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                result.push_str(&format!("  {} {:?} <- {}\n", phi.block, phi.result, inputs));
            }
        }
        result.push('\n');

        result.push_str("cleanup-proofs:\n");
        if exception_analysis.cleanup_proofs.is_empty() {
            result.push_str("  <none>\n");
        } else {
            for proof in &exception_analysis.cleanup_proofs {
                result.push_str(&format!(
                    "  try{} handler{} normal={} candidate={} outcome={:?} mismatch={:?}\n",
                    proof.region,
                    proof.handler,
                    proof.normal_entry,
                    proof.candidate,
                    proof.outcome,
                    proof.mismatch
                ));
            }
        }
        result.push('\n');

        result.push_str("exception-scopes:\n");
        for scope in &exception_analysis.regions {
            result.push_str(&format!(
                "  try{} parent={} protected={} exits={}\n",
                scope.id,
                scope
                    .parent
                    .map_or_else(|| "-".to_string(), |parent| format!("try{parent}")),
                format_block_id_list(&scope.blocks),
                format_block_id_list(&scope.normal_exit_blocks)
            ));
            for handler in &scope.handlers {
                result.push_str(&format!(
                    "    {:?} entry={} body={} lexical={} continuation={} rethrows={} value={}\n",
                    handler.kind,
                    handler.handler_block,
                    format_block_id_list(&handler.blocks),
                    format_block_id_list(&handler.lexical_blocks),
                    format_optional_block_id(handler.continuation),
                    format_block_id_list(
                        &handler.rethrow_blocks.iter().copied().collect::<Vec<_>>()
                    ),
                    handler
                        .exception_value
                        .as_ref()
                        .map_or_else(|| "-".to_string(), |value| format!("{value:?}"))
                ));
            }
        }
        result.push('\n');

        result.push_str("regions:\n");
        for region in region_tree.regions() {
            let blocks: Vec<_> = region.blocks.iter().copied().collect();
            result.push_str(&format!(
                "  {} {} parent={} entry={} follow={} blocks={} children={}\n",
                region.id,
                format_region_kind(&region.kind),
                format_region_id(region.parent),
                format_optional_block_id(region.entry),
                format_optional_block_id(region.kind.follow()),
                format_block_id_list(&blocks),
                format_region_id_list(&region.children)
            ));
        }

        result.push_str("\nboundary-transfers:\n");
        let boundary_transfers: Vec<_> = transfers
            .iter()
            .filter(|transfer| transfer.kind != RegionTransferKind::Local)
            .collect();
        if boundary_transfers.is_empty() {
            result.push_str("  <none>\n");
        } else {
            for transfer in boundary_transfers {
                result.push_str(&format!(
                    "  {} -> {} {} -> {} destination={}/{} {:?} leave-target={} edge={:?} exit={:?}\n",
                    transfer.source_block,
                    transfer.target_block,
                    transfer.source_region,
                    transfer.target_region,
                    transfer.destination_block,
                    transfer.destination_region,
                    transfer.kind,
                    format_region_id(transfer.leave_target),
                    transfer.edge_kind,
                    transfer.exit_kind
                ));
            }
        }

        result.push_str("\nresolved-exits:\n");
        if leaves.is_empty() {
            result.push_str("  <none>\n");
        } else {
            for resolved in leaves {
                let leave = &resolved.leave;
                result.push_str(&format!(
                    "  {} {} -> {} {:?} edge={:?} value={} cleanup={}\n",
                    format_optional_block_id(leave.source_block),
                    leave.source,
                    leave.target,
                    leave.kind(),
                    leave.edge,
                    format_optional_insn_arg(leave.value()),
                    format_region_id_list(&resolved.cleanup_regions)
                ));
            }
        }

        host.emit_or_write(request.output.as_deref(), &result)
    }
}
