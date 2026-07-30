//! CFG dump command.

use crate::{method_to_dot, method_to_text};

use super::error::{cli_err, CliResult};
use super::method_decode::MethodCfgDecoder;
use super::model::CfgRequest;
use super::output::CliHost;

/// Dumps a method control-flow graph in DOT or text form.
pub struct CfgCommand;

impl CfgCommand {
    pub fn run(host: &mut impl CliHost, request: &CfgRequest) -> CliResult<()> {
        let ir = MethodCfgDecoder::decode_raw(
            &request.input,
            &request.class,
            &request.method,
            request.descriptor.as_deref(),
        )?;

        let output_str = match request.format.as_str() {
            "dot" => method_to_dot(&ir),
            "text" => method_to_text(&ir),
            other => {
                return Err(cli_err(format!(
                    "Unknown format: {other}. Use 'dot' or 'text'."
                )))
            }
        };

        host.emit_or_write(request.output.as_deref(), &output_str)
    }
}
