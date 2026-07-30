//! Exact class and member reference queries.

use serde::Serialize;

use crate::{ClassOutline, Decompiler, ReferenceTarget};

use super::error::{CliError, CliResult};
use super::model::{ReferenceQuery, ReferencesRequest};
use super::output::{CliHost, CommandContext};
use super::resolve::ClassResolver;

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ReferenceReport {
    kind: &'static str,
    target: String,
    count: usize,
    locations: Vec<ReferenceLocationView>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ReferenceLocationView {
    class: String,
    method: String,
    descriptor: String,
    offset: u32,
    offset_hex: String,
}

pub struct ReferencesCommand;

impl ReferencesCommand {
    pub fn run<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &ReferencesRequest,
    ) -> CliResult<()> {
        let mut decompiler = Decompiler::open(&request.input)?;
        let catalog = decompiler.catalog();
        let resolver = ClassResolver::new(&catalog);

        let (kind, display, target) = match &request.target {
            ReferenceQuery::Class { class } => {
                let class = resolver.resolve(class)?.descriptor.clone();
                ("class", class.clone(), ReferenceTarget::class(class))
            }
            ReferenceQuery::Field {
                class,
                name,
                descriptor,
            } => {
                let class = resolver.resolve(class)?.descriptor.clone();
                let outline = decompiler.class_outline(class.clone())?;
                let descriptor = Self::field_descriptor(&outline, name, descriptor.as_deref())?;
                let display = format!("{class}->{name}:{descriptor}");
                (
                    "field",
                    display,
                    ReferenceTarget::field(class, name, descriptor),
                )
            }
            ReferenceQuery::Method {
                class,
                name,
                descriptor,
            } => {
                let class = resolver.resolve(class)?.descriptor.clone();
                let outline = decompiler.class_outline(class.clone())?;
                let descriptor = Self::method_descriptor(&outline, name, descriptor.as_deref())?;
                let display = format!("{class}->{name}{descriptor}");
                (
                    "method",
                    display,
                    ReferenceTarget::method(class, name, descriptor),
                )
            }
        };

        let locations = decompiler
            .references(target)?
            .locations
            .into_iter()
            .map(|location| ReferenceLocationView {
                class: location.class,
                method: location.method,
                descriptor: location.descriptor,
                offset_hex: format!("0x{:x}", location.offset),
                offset: location.offset,
            })
            .collect::<Vec<_>>();
        let report = ReferenceReport {
            kind,
            target: display,
            count: locations.len(),
            locations,
        };
        let mut text = String::new();
        for location in &report.locations {
            text.push_str(&format!(
                "{}\t{}\t{}\t{}\n",
                location.class, location.method, location.descriptor, location.offset_hex
            ));
        }
        context.respond("references", &report, &text)
    }

    fn field_descriptor(
        outline: &ClassOutline,
        name: &str,
        requested: Option<&str>,
    ) -> CliResult<String> {
        let matches = outline
            .fields
            .iter()
            .filter(|field| field.name == name)
            .filter(|field| requested.is_none_or(|descriptor| field.descriptor == descriptor))
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [field] => Ok(field.descriptor.clone()),
            [] => Err(CliError::not_found(format!(
                "field not found: {}->{name}{}",
                outline.descriptor,
                requested.map_or(String::new(), |descriptor| format!(":{descriptor}"))
            ))),
            fields => Err(CliError::ambiguous(format!(
                "field name is ambiguous: {}->{name}",
                outline.descriptor
            ))
            .with_hint(format!(
                "Choose --descriptor from: {}",
                fields
                    .iter()
                    .map(|field| field.descriptor.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ))),
        }
    }

    fn method_descriptor(
        outline: &ClassOutline,
        name: &str,
        requested: Option<&str>,
    ) -> CliResult<String> {
        let matches = outline
            .methods
            .iter()
            .filter(|method| method.name == name)
            .filter(|method| requested.is_none_or(|descriptor| method.descriptor == descriptor))
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [method] => Ok(method.descriptor.clone()),
            [] => Err(CliError::not_found(format!(
                "method not found: {}->{name}{}",
                outline.descriptor,
                requested.unwrap_or_default()
            ))),
            methods => Err(CliError::ambiguous(format!(
                "method name is overloaded: {}->{name}",
                outline.descriptor
            ))
            .with_hint(format!(
                "Choose --descriptor from: {}",
                methods
                    .iter()
                    .map(|method| method.descriptor.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ))),
        }
    }
}
