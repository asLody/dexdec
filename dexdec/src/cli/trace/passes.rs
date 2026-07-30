//! Trace-passes command: CFG pipeline stage diffs.

use std::collections::BTreeSet;

use crate::ir::passes::CfgPipeline;
use crate::ir::BlockId;

use super::super::error::CliResult;
use super::super::method_decode::MethodCfgDecoder;
use super::super::model::TracePassesRequest;
use super::super::output::CliHost;
use super::cfg_trace::{append_decode_snapshot, CfgPassTrace, CfgSnapshot};

/// Traces verified CFG pipeline transformations for a method.
pub struct TracePassesCommand;

impl TracePassesCommand {
    pub fn run(host: &mut impl CliHost, request: &TracePassesRequest) -> CliResult<()> {
        let trace_blocks = parse_trace_blocks(request.blocks.as_deref())?;
        let (mut cfg, hierarchy) = MethodCfgDecoder::decode_analysis(
            &request.input,
            &request.class,
            &request.method,
            request.descriptor.as_deref(),
        )?;

        let mut result = String::new();
        result.push_str(&format!(
            "=== pass trace for {}.{} ===\n",
            request.class, request.method
        ));
        result.push_str(&format!(
            "filters: blocks={}\n\n",
            trace_blocks
                .as_ref()
                .map(|ids| {
                    ids.iter()
                        .map(|id| id.0.to_string())
                        .collect::<Vec<_>>()
                        .join(",")
                })
                .unwrap_or_else(|| "<changed>".to_string())
        ));

        append_decode_snapshot(
            &mut result,
            "decode",
            &cfg,
            &trace_blocks,
            request.changed_details,
        );

        let trace = CfgPassTrace::new(
            result,
            CfgSnapshot::from_cfg(&cfg),
            trace_blocks,
            request.changed_details,
        );
        let pipeline = CfgPipeline::new(hierarchy.as_ref());
        let pipeline_result = pipeline.run_observed(&mut cfg, &trace);
        let result = trace.output()?;

        host.emit_or_write(request.output.as_deref(), &result)?;
        pipeline_result
            .map(|_| ())
            .map_err(|error| super::super::error::CliError::command(error.to_string()))
    }
}

fn parse_trace_blocks(blocks: Option<&str>) -> CliResult<Option<BTreeSet<BlockId>>> {
    let Some(blocks) = blocks else {
        return Ok(None);
    };
    let mut parsed = BTreeSet::new();
    for token in blocks.split(',').map(str::trim).filter(|s| !s.is_empty()) {
        let id = token
            .parse::<u32>()
            .map_err(|_| format!("Invalid block id: {}", token))?;
        parsed.insert(BlockId::new(id));
    }
    Ok(Some(parsed))
}
