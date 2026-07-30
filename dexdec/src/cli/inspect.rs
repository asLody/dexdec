//! Archive and class inspection without source generation.

use serde::Serialize;

use crate::{ClassKind, ClassOutline, Decompiler, MemberKind};

use super::error::CliResult;
use super::model::InspectRequest;
use super::output::{CliHost, CommandContext};
use super::resolve::ClassResolver;
use super::resources::ResourceArchive;

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ArchiveInspection {
    input: String,
    input_kind: &'static str,
    size_bytes: u64,
    classes: usize,
    fields: usize,
    methods: usize,
    methods_with_code: usize,
    resources: usize,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ClassInspection {
    descriptor: String,
    qualified_name: String,
    kind: &'static str,
    access_flags: u32,
    super_class: Option<String>,
    interfaces: Vec<String>,
    source_file: Option<String>,
    parent_class: Option<String>,
    nested_classes: Vec<String>,
    fields: Vec<FieldInspection>,
    methods: Vec<MethodInspection>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct FieldInspection {
    name: String,
    descriptor: String,
    display_type: String,
    access_flags: u32,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct MethodInspection {
    name: String,
    descriptor: String,
    display_signature: String,
    access_flags: u32,
    has_code: bool,
    constructor: bool,
}

impl From<ClassOutline> for ClassInspection {
    fn from(outline: ClassOutline) -> Self {
        Self {
            descriptor: outline.descriptor,
            qualified_name: outline.qualified_name,
            kind: match outline.kind {
                ClassKind::Class => "class",
                ClassKind::Interface => "interface",
                ClassKind::Annotation => "annotation",
                ClassKind::Enum => "enum",
            },
            access_flags: outline.access_flags,
            super_class: outline.super_class,
            interfaces: outline.interfaces,
            source_file: outline.source_file,
            parent_class: outline.parent_class,
            nested_classes: outline.nested_classes,
            fields: outline
                .fields
                .into_iter()
                .map(|field| FieldInspection {
                    name: field.name,
                    descriptor: field.descriptor,
                    display_type: field.display_type,
                    access_flags: field.access_flags,
                })
                .collect(),
            methods: outline
                .methods
                .into_iter()
                .map(|method| MethodInspection {
                    name: method.name,
                    descriptor: method.descriptor,
                    display_signature: method.display_signature,
                    access_flags: method.access_flags,
                    has_code: method.has_code,
                    constructor: method.constructor,
                })
                .collect(),
        }
    }
}

pub struct InspectCommand;

impl InspectCommand {
    pub fn run<H: CliHost>(
        context: &mut CommandContext<'_, H>,
        request: &InspectRequest,
    ) -> CliResult<()> {
        let mut decompiler = Decompiler::open(&request.input)?;
        let catalog = decompiler.catalog();
        if let Some(class) = request.class.as_deref() {
            let descriptor = ClassResolver::new(&catalog)
                .resolve(class)?
                .descriptor
                .clone();
            let inspection: ClassInspection = decompiler.class_outline(descriptor)?.into();
            let text = Self::format_class(&inspection);
            return context.respond("inspect.class", &inspection, &text);
        }

        let members = decompiler.member_catalog()?;
        let mut fields = 0usize;
        let mut methods = 0usize;
        let mut methods_with_code = 0usize;
        for member in members.members() {
            match member.kind {
                MemberKind::Field => fields += 1,
                MemberKind::Method => {
                    methods += 1;
                    methods_with_code += usize::from(member.has_code);
                }
            }
        }
        let resources = ResourceArchive::open_optional(&request.input)?
            .map_or(0, |archive| archive.entries().len());
        let inspection = ArchiveInspection {
            input: request.input.display().to_string(),
            input_kind: request
                .input
                .extension()
                .and_then(|extension| extension.to_str())
                .filter(|extension| extension.eq_ignore_ascii_case("apk"))
                .map_or("dex", |_| "apk"),
            size_bytes: context.host_mut().metadata_len(&request.input)?,
            classes: catalog.len(),
            fields,
            methods,
            methods_with_code,
            resources,
        };
        let text = format!(
            "input={}\ntype={}\nsizeBytes={}\nclasses={}\nfields={}\nmethods={}\nmethodsWithCode={}\nresources={}\n",
            inspection.input,
            inspection.input_kind,
            inspection.size_bytes,
            inspection.classes,
            inspection.fields,
            inspection.methods,
            inspection.methods_with_code,
            inspection.resources,
        );
        context.respond("inspect", &inspection, &text)
    }

    fn format_class(class: &ClassInspection) -> String {
        let mut text = format!(
            "{}\t{}\t{}\n",
            class.kind, class.descriptor, class.qualified_name
        );
        if let Some(super_class) = class.super_class.as_deref() {
            text.push_str(&format!("extends\t{super_class}\n"));
        }
        for interface in &class.interfaces {
            text.push_str(&format!("implements\t{interface}\n"));
        }
        for field in &class.fields {
            text.push_str(&format!("field\t{}\t{}\n", field.name, field.descriptor));
        }
        for method in &class.methods {
            text.push_str(&format!(
                "method\t{}\t{}\tcode={}\n",
                method.name, method.descriptor, method.has_code
            ));
        }
        text
    }
}
