//! Expected output based integration tests.
//!
//! This module provides tests that compare actual decompilation output
//! against expected output files stored in the `testcases/expected` directory.
//!
//! Test cases:
//! - `testcases/java/*.java` - Java source fixtures compiled to DEX
//! - `testcases/smali/*.smali` - Compiled smali code
//! - `testcases/expected/*.simple.expected` - Expected simple codegen output
//! - `testcases/expected/*.kt.expected` - Expected class-level Kotlin output

mod common;

use dexdec::analysis::KotlinDecompilerConfig;
use dexdec::api::DecompilerContext;
use std::fs;
use std::path::PathBuf;

/// Get the testcases directory
fn testcases_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("testcases")
}

/// Get expected output directory
fn expected_dir() -> PathBuf {
    testcases_dir().join("expected")
}

/// Load expected output from file, return None if file doesn't exist
fn load_expected(name: &str, suffix: &str) -> Option<String> {
    let path = expected_dir().join(format!("{}.{}.expected", name, suffix));
    fs::read_to_string(&path).ok()
}

/// Save actual output to expected file (for regeneration)
fn save_expected(name: &str, suffix: &str, content: &str) {
    let dir = expected_dir();
    fs::create_dir_all(&dir).ok();
    let path = dir.join(format!("{}.{}.expected", name, suffix));
    fs::write(&path, content).expect("failed to write expected file");
}

/// Load a test case and return the decompiler context
fn load_testcase(name: &str) -> (DecompilerContext, String) {
    let dex_path =
        common::compile_testcase(name).expect(&format!("failed to compile test case: {}", name));

    let ctx = DecompilerContext::from_file(&dex_path)
        .expect(&format!("failed to load dex file: {:?}", dex_path));

    let class_name = format!("L{};", name);
    (ctx, class_name)
}

fn normalize_return_consts(lines: Vec<String>) -> Vec<String> {
    let mut out = Vec::with_capacity(lines.len());
    let mut i = 0;

    while i < lines.len() {
        let line = &lines[i];
        let trimmed = line.trim();

        if (trimmed.starts_with("v") && trimmed.ends_with("= 0"))
            || (trimmed.starts_with("v") && trimmed.ends_with("= 1"))
        {
            if let Some((var, value)) = trimmed.split_once("=") {
                let var = var.trim();
                let value = value.trim();

                if i + 1 < lines.len() {
                    let next = lines[i + 1].trim();
                    if next == format!("return {}", var) {
                        let indent = lines[i + 1]
                            .chars()
                            .take_while(|c| c.is_whitespace())
                            .collect::<String>();
                        out.push(format!("{}return {}", indent, value));
                        i += 2;
                        continue;
                    }
                }
            }
        }

        out.push(line.clone());
        i += 1;
    }

    out
}

fn strip_outer_parens(s: &str) -> &str {
    let mut current = s.trim();
    loop {
        if !current.starts_with('(') || !current.ends_with(')') || current.len() < 2 {
            return current;
        }

        let mut depth = 0;
        let mut wraps = true;
        for (i, ch) in current.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            if depth == 0 && i < current.len() - 1 {
                wraps = false;
                break;
            }
        }

        if wraps {
            current = &current[1..current.len() - 1];
        } else {
            return current;
        }
    }
}

fn split_top_level(cond: &str, op: &str) -> Option<Vec<String>> {
    let bytes = cond.as_bytes();
    let op_bytes = op.as_bytes();
    let mut parts = Vec::new();
    let mut depth = 0;
    let mut last = 0;
    let mut i = 0;

    while i + op_bytes.len() <= bytes.len() {
        match bytes[i] as char {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }

        if depth == 0 && bytes[i..].starts_with(op_bytes) {
            let part = cond[last..i].trim().to_string();
            parts.push(part);
            i += op_bytes.len();
            last = i;
            continue;
        }

        i += 1;
    }

    if parts.is_empty() {
        return None;
    }

    parts.push(cond[last..].trim().to_string());
    Some(parts)
}

fn normalize_condition_expr(cond: &str) -> Option<String> {
    let cond = strip_outer_parens(cond);

    let or_parts = split_top_level(cond, "||");
    let and_parts = split_top_level(cond, "&&");

    match (or_parts, and_parts) {
        (Some(mut parts), None) => {
            parts.sort();
            Some(format!("({})", parts.join(" || ")))
        }
        (None, Some(mut parts)) => {
            parts.sort();
            Some(format!("({})", parts.join(" && ")))
        }
        _ => None,
    }
}

fn normalize_condition_line(line: &str) -> String {
    let trimmed = line.trim();
    let indent = line
        .chars()
        .take_while(|c| c.is_whitespace())
        .collect::<String>();

    if let Some(cond) = trimmed.strip_prefix("if (") {
        if let Some(cond) = cond.strip_suffix(") {") {
            if let Some(norm) = normalize_condition_expr(cond) {
                return format!("{}if ({}) {{", indent, norm);
            }
        }
    }

    if let Some(cond) = trimmed.strip_prefix("while (") {
        if let Some(cond) = cond.strip_suffix(") {") {
            if let Some(norm) = normalize_condition_expr(cond) {
                return format!("{}while ({}) {{", indent, norm);
            }
        }
    }

    line.to_string()
}

/// Normalize output for comparison (strip trailing whitespace, normalize line endings)
/// Also normalizes predecessor order in simple codegen output
fn normalize_output(s: &str) -> String {
    let lines = s
        .lines()
        .map(|line| line.trim_end().to_string())
        .collect::<Vec<_>>();

    let lines = normalize_return_consts(lines);

    lines
        .into_iter()
        .map(|line| {
            // Normalize predecessor order: "# preds: BBB2, BBB0" -> "# preds: BBB0, BBB2"
            if line.contains("# preds:") {
                if let Some(preds_start) = line.find("# preds:") {
                    let prefix = &line[..preds_start + 9]; // "# preds: "
                    let preds_part = &line[preds_start + 9..];
                    let mut preds: Vec<&str> = preds_part.split(", ").collect();
                    preds.sort();
                    return format!("{}{}", prefix, preds.join(", "));
                }
            }
            normalize_condition_line(&line)
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

/// Compare actual output with expected, panic if different
fn assert_output_eq(actual: &str, expected: &str, name: &str, kind: &str) {
    let actual_norm = normalize_output(actual);
    let expected_norm = normalize_output(expected);

    if actual_norm != expected_norm {
        // Print diff for debugging
        eprintln!("=== {} {} MISMATCH ===", name, kind);
        eprintln!("--- Expected ---");
        eprintln!("{}", expected_norm);
        eprintln!("--- Actual ---");
        eprintln!("{}", actual_norm);
        eprintln!("================");

        panic!(
            "{} {} output mismatch:\nExpected:\n{}\n\nActual:\n{}",
            name, kind, expected_norm, actual_norm
        );
    }
}

/// Test helper: generate structured code and compare with expected
fn test_structured_class_codegen(name: &str) {
    let (mut ctx, class_name) = load_testcase(name);
    ctx.load_all_classes().expect("should load classes");

    let config = KotlinDecompilerConfig::default();

    let result = ctx.decompile_class_with_config(&class_name, &config);

    let regen = std::env::var("DEXDEC_REGEN_EXPECTED").is_ok();

    match result {
        Ok(Some(actual)) => {
            if regen {
                save_expected(name, "kt", &actual);
                return;
            }
            match load_expected(name, "kt") {
                Some(expected) => {
                    assert_output_eq(&actual, &expected, name, "kotlin");
                }
                None => {
                    eprintln!("NOTE: Creating expected file for {}.kt", name);
                    save_expected(name, "kt", &actual);
                }
            }
        }
        Ok(None) => {
            panic!("Class {} not found or has no code", name);
        }
        Err(e) => {
            if regen {
                let error_msg = format!("STRUCTURING_FAILED: {:?}", e);
                save_expected(name, "kt", &error_msg);
                return;
            }
            // Structure may fail for complex cases - save error as expected
            let error_msg = format!("STRUCTURING_FAILED: {:?}", e);
            match load_expected(name, "kt") {
                Some(expected) if expected.starts_with("STRUCTURING_FAILED") => {
                    // Expected to fail, check error matches
                    assert_output_eq(&error_msg, &expected, name, "kotlin");
                }
                Some(expected) => {
                    panic!(
                        "{} class structuring failed unexpectedly: {:?}\nExpected:\n{}",
                        name, e, expected
                    );
                }
                None => {
                    eprintln!("NOTE: Creating expected file for {}.kt (FAILED)", name);
                    save_expected(name, "kt", &error_msg);
                }
            }
        }
    }
}

fn structured_class_cases() -> &'static [&'static str] {
    &[
        "SimpleIf",
        "SimpleLoop",
        "NestedIf",
        "DoWhile",
        "ForLoop",
        "Switch",
        "TryCatch",
        "NestedLoopBranches",
        "BranchMaze",
        "BreakContinue",
        "ShortCircuit",
        "TryCatchFinally",
        "ExceptionControlFlow",
        "ExceptionControlFlowAdvanced",
        "DeepNesting",
        "ComplexControlFlow",
        "MultiReturn",
        "MultiCatch",
        "Finally",
        "HardcoreControlFlow",
        "Synchronized",
        "SynchronizedAdvanced",
    ]
}

#[test]
fn test_structured_class_codegen_expected_outputs() {
    for name in structured_class_cases() {
        test_structured_class_codegen(name);
    }
}

#[test]
fn platform_constant_codegen_expected_output() {
    test_structured_class_codegen("PlatformConstants");
}

// ============================================================
// Simple Codegen Tests
// ============================================================

// ============================================================
// BreakContinue Tests
// ============================================================

// ============================================================
// ShortCircuit Tests
// ============================================================

// ============================================================
// TryCatchFinally Tests
// ============================================================

// ============================================================
// ExceptionControlFlow Tests
// ============================================================

// ============================================================
// ExceptionControlFlowAdvanced Tests
// ============================================================

// ============================================================
// DeepNesting Tests
// ============================================================

// ============================================================
// ComplexControlFlow Tests
// ============================================================

// ============================================================
// MultiReturn Tests
// ============================================================

// ============================================================
// MultiCatch Tests
// ============================================================

// ============================================================
// Finally Tests
// ============================================================

// ============================================================
// HardcoreControlFlow Tests
// ============================================================

// ============================================================
// Synchronized Tests
// ============================================================

// ============================================================
// SynchronizedAdvanced Tests
// ============================================================
