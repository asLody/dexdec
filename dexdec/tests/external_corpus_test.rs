//! External source-backed DEX corpus tests.
//!
//! These cases come from public upstream projects and are compiled to DEX during
//! the test. The snapshots are intentionally class-level, matching the main
//! Kotlin decompiler output.

mod common;

use dexdec::analysis::KotlinDecompilerConfig;
use dexdec::api::DecompilerContext;
use std::fs;
use std::io;
use std::path::PathBuf;

#[derive(Debug)]
struct ExternalCase {
    id: String,
    upstream_url: String,
    source_roots: Vec<PathBuf>,
    target_class: String,
    focus: String,
}

fn corpus_dir() -> PathBuf {
    common::workspace_root()
        .expect("workspace root should exist")
        .join("dexdec/tests/external_corpus")
}

fn expected_dir() -> PathBuf {
    corpus_dir().join("expected")
}

fn expected_path(case_id: &str) -> PathBuf {
    expected_dir().join(format!("{}.kt.expected", case_id))
}

fn load_external_cases() -> io::Result<Vec<ExternalCase>> {
    let root = common::workspace_root()
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "workspace root not found"))?;
    let manifest = corpus_dir().join("cases.tsv");
    let content = fs::read_to_string(&manifest)?;
    let mut cases = Vec::new();

    for (line_index, line) in content.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 5 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "{}:{}: expected 5 tab-separated fields, got {}",
                    manifest.display(),
                    line_index + 1,
                    fields.len()
                ),
            ));
        }

        let source_roots = fields[2]
            .split(';')
            .map(|path| root.join(path))
            .collect::<Vec<_>>();

        cases.push(ExternalCase {
            id: fields[0].to_string(),
            upstream_url: fields[1].to_string(),
            source_roots,
            target_class: fields[3].to_string(),
            focus: fields[4].to_string(),
        });
    }

    Ok(cases)
}

fn normalize_snapshot(text: &str) -> String {
    text.lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

fn assert_snapshot_eq(actual: &str, expected: &str, case: &ExternalCase) {
    let actual = normalize_snapshot(actual);
    let expected = normalize_snapshot(expected);
    if actual != expected {
        panic!(
            "external corpus snapshot mismatch for {}\nsource: {}\nfocus: {}\n\nExpected:\n{}\n\nActual:\n{}",
            case.id, case.upstream_url, case.focus, expected, actual
        );
    }
}

fn decompile_case(case: &ExternalCase) -> String {
    let dex_path = common::compile_java_source_set_to_dex(&case.id, &case.source_roots)
        .unwrap_or_else(|err| panic!("failed to compile external case {}: {}", case.id, err));

    let mut ctx = DecompilerContext::from_file(&dex_path)
        .unwrap_or_else(|err| panic!("failed to load DEX for {}: {}", case.id, err));
    ctx.load_all_classes()
        .unwrap_or_else(|err| panic!("failed to load classes for {}: {}", case.id, err));

    let config = KotlinDecompilerConfig::default();

    ctx.decompile_class_with_config(&case.target_class, &config)
        .unwrap_or_else(|err| panic!("failed to decompile {}: {}", case.id, err))
        .unwrap_or_else(|| {
            panic!(
                "target class {} not found for {}",
                case.target_class, case.id
            )
        })
}

#[test]
fn test_external_corpus_class_codegen() {
    if common::find_d8_tool().is_none() {
        eprintln!("external corpus skipped: d8 not found");
        return;
    }

    let cases = load_external_cases().expect("external corpus manifest should load");
    assert!(!cases.is_empty(), "external corpus should not be empty");

    let regen = std::env::var("DEXDEC_REGEN_EXTERNAL_EXPECTED").is_ok()
        || std::env::var("DEXDEC_REGEN_EXPECTED").is_ok();

    for case in cases {
        let actual = decompile_case(&case);
        assert!(
            actual.contains("class ") || actual.contains("interface "),
            "external case {} produced no class/interface declaration",
            case.id
        );

        let path = expected_path(&case.id);
        if regen {
            fs::create_dir_all(expected_dir()).expect("external expected dir should exist");
            fs::write(&path, actual).expect("external expected snapshot should be writable");
        } else {
            let expected = fs::read_to_string(&path).unwrap_or_else(|err| {
                panic!(
                    "missing expected snapshot for {} at {}: {}",
                    case.id,
                    path.display(),
                    err
                )
            });
            assert_snapshot_eq(&actual, &expected, &case);
        }
    }
}
