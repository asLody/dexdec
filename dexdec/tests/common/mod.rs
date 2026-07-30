//! Test utilities for locating committed DEX fixtures and compiling external
//! Java source sets with the Android SDK.

#![allow(dead_code)]

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

static COMPILE_MUTEX: Mutex<()> = Mutex::new(());
/// Find d8 tool
fn find_d8() -> Option<PathBuf> {
    // Check PATH first
    if Command::new("d8").arg("--version").output().is_ok() {
        return Some(PathBuf::from("d8"));
    }

    // Check ANDROID_HOME
    if let Ok(android_home) = std::env::var("ANDROID_HOME") {
        if let Some(d8) = find_d8_in_sdk(Path::new(&android_home)) {
            return Some(d8);
        }
    }

    // Check common locations
    let home = std::env::var("HOME").ok()?;
    let common_paths = [
        format!("{}/Library/Android/sdk", home),
        format!("{}/Android/Sdk", home),
        "/usr/local/android-sdk".to_string(),
    ];

    for sdk_path in common_paths {
        if let Some(d8) = find_d8_in_sdk(Path::new(&sdk_path)) {
            return Some(d8);
        }
    }

    None
}

/// Find d8 using the same search order as the Kotlin-to-smali test pipeline.
pub fn find_d8_tool() -> Option<PathBuf> {
    find_d8()
}

fn find_d8_in_sdk(sdk_path: &Path) -> Option<PathBuf> {
    let build_tools = sdk_path.join("build-tools");
    if !build_tools.exists() {
        return None;
    }

    // Find the latest version
    let mut versions: Vec<_> = fs::read_dir(&build_tools)
        .ok()?
        .filter_map(|e| e.ok())
        .filter(|e| e.path().is_dir())
        .collect();

    versions.sort_by(|a, b| b.file_name().cmp(&a.file_name()));

    for version_dir in versions {
        let d8 = version_dir.path().join("d8");
        if d8.exists() {
            return Some(d8);
        }
    }

    None
}

/// Find workspace root directory
fn find_workspace_root() -> Option<PathBuf> {
    let mut path = std::env::current_dir().ok()?;

    loop {
        // Check if this is the workspace root (contains Cargo.toml with [workspace])
        let cargo_toml = path.join("Cargo.toml");
        if cargo_toml.exists() {
            if let Ok(content) = fs::read_to_string(&cargo_toml) {
                if content.contains("[workspace]") {
                    return Some(path);
                }
            }
        }

        // Go up one level
        if !path.pop() {
            break;
        }
    }

    None
}

/// Find the workspace root for tests that need to resolve repo-relative paths.
pub fn workspace_root() -> Option<PathBuf> {
    find_workspace_root()
}

fn collect_files_with_extension(root: &Path, extension: &str) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    if !root.exists() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("source root not found: {}", root.display()),
        ));
    }

    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(&dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == extension) {
                files.push(path);
            }
        }
    }

    files.sort();
    Ok(files)
}

fn is_older_than_any(path: &Path, inputs: &[PathBuf]) -> io::Result<bool> {
    if !path.exists() {
        return Ok(true);
    }

    let output_mtime = fs::metadata(path)?.modified()?;
    for input in inputs {
        if fs::metadata(input)?.modified()? > output_mtime {
            return Ok(true);
        }
    }

    Ok(false)
}

/// Compile one external Kotlin source set to a DEX file.
///
/// Unlike the small testcase helper, this compiles every Kotlin source under the
/// supplied roots and feeds all generated class files to d8. This is required
/// for real-world source sets where the target class depends on helper classes.
pub fn compile_java_source_set_to_dex(
    case_id: &str,
    source_roots: &[PathBuf],
) -> io::Result<PathBuf> {
    let _lock = COMPILE_MUTEX.lock().unwrap();

    let d8 = find_d8().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            "d8 not found. Install Android SDK or set ANDROID_HOME",
        )
    })?;

    let workspace_root = find_workspace_root()
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "workspace root not found"))?;

    let mut sources = Vec::new();
    for root in source_roots {
        sources.extend(collect_files_with_extension(root, "java")?);
    }
    sources.sort();
    sources.dedup();
    if sources.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("no Kotlin sources found for external case '{}'", case_id),
        ));
    }

    let case_dir = workspace_root.join("target/external-corpus").join(case_id);
    let classes_dir = case_dir.join("classes");
    let dex_dir = case_dir.join("dex");
    let dex_path = dex_dir.join("classes.dex");

    if !is_older_than_any(&dex_path, &sources)? {
        return Ok(dex_path);
    }

    let _ = fs::remove_dir_all(&case_dir);
    fs::create_dir_all(&classes_dir)?;
    fs::create_dir_all(&dex_dir)?;

    let output = Command::new("javac")
        .args(["-source", "8", "-target", "8"])
        .arg("-d")
        .arg(&classes_dir)
        .args(&sources)
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("javac failed for external case '{}': {}", case_id, stderr),
        ));
    }

    let class_files = collect_files_with_extension(&classes_dir, "class")?;
    if class_files.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("javac produced no class files for '{}'", case_id),
        ));
    }

    let output = Command::new(d8)
        .arg("--output")
        .arg(&dex_dir)
        .args(&class_files)
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("d8 failed for external case '{}': {}", case_id, stderr),
        ));
    }

    Ok(dex_path)
}

/// Test case paths
#[allow(dead_code)]
pub struct TestCase {
    pub name: String,
    pub java_path: PathBuf,
    pub smali_path: PathBuf,
    pub expected_path: Option<PathBuf>,
}

impl TestCase {
    /// Find all committed smali test cases.
    pub fn find_all() -> Vec<TestCase> {
        let Some(workspace_root) = find_workspace_root() else {
            return Vec::new();
        };

        let testcases_dir = workspace_root.join("dexdec/tests/testcases");
        let java_dir = testcases_dir.join("java");
        let smali_dir = testcases_dir.join("smali");
        let expected_dir = testcases_dir.join("expected");

        let mut cases = Vec::new();

        if let Ok(entries) = fs::read_dir(&smali_dir) {
            for entry in entries.filter_map(|e| e.ok()) {
                let path = entry.path();
                if path
                    .extension()
                    .is_some_and(|extension| extension == "smali")
                {
                    let name = path.file_stem().unwrap().to_string_lossy().to_string();
                    let java_path = java_dir.join(format!("{}.java", name));
                    let expected_path = expected_dir.join(format!("{}.expected", name));
                    cases.push(TestCase {
                        name,
                        java_path,
                        smali_path: path,
                        expected_path: expected_path.exists().then_some(expected_path),
                    });
                }
            }
        }

        cases.sort_by(|a, b| a.name.cmp(&b.name));
        cases
    }

    /// Get a specific committed test case by name.
    pub fn get(name: &str) -> Option<TestCase> {
        let workspace_root = find_workspace_root()?;
        let testcases_dir = workspace_root.join("dexdec/tests/testcases");
        let java_dir = testcases_dir.join("java");
        let smali_dir = testcases_dir.join("smali");
        let expected_dir = testcases_dir.join("expected");

        let java_path = java_dir.join(format!("{}.java", name));
        let smali_path = smali_dir.join(format!("{}.smali", name));
        let expected_path = expected_dir.join(format!("{}.expected", name));

        if smali_path.exists() {
            Some(TestCase {
                name: name.to_string(),
                java_path,
                smali_path,
                expected_path: expected_path.exists().then_some(expected_path),
            })
        } else {
            None
        }
    }
}

/// Return the committed DEX containing all smali test cases.
pub fn compile_testcase(name: &str) -> io::Result<PathBuf> {
    TestCase::get(name).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            format!("test case '{}' not found", name),
        )
    })?;
    let dex_path = find_workspace_root()
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "workspace root not found"))?
        .join("dexdec/tests/testcases/classes.dex");
    dex_path
        .exists()
        .then_some(dex_path)
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "test DEX fixture not found"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_workspace_root() {
        let root = find_workspace_root();
        assert!(root.is_some(), "should find workspace root");
        let root = root.unwrap();
        assert!(root.join("Cargo.toml").exists());
    }

    #[test]
    fn test_find_test_cases() {
        let cases = TestCase::find_all();
        // Should find at least some test cases
        if !cases.is_empty() {
            for case in &cases {
                assert!(
                    case.smali_path.exists(),
                    "smali file should exist: {:?}",
                    case.smali_path
                );
            }
        }
    }
}
