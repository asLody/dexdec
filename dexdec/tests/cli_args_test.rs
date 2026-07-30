use clap::Parser;

use dexdec::cli::{Cli, Command};
use dexdec::SourceLanguage;

#[test]
fn decompile_defaults_to_kotlin() {
    let cli = Cli::try_parse_from(["dexdec", "decompile", "classes.dex"]).unwrap();
    let Command::Decompile(request) = cli.into_command() else {
        panic!("expected decompile command");
    };

    assert_eq!(request.language, SourceLanguage::Kotlin);
    assert!(request.include_inner);
}

#[test]
fn decompile_accepts_java_without_nested_classes() {
    let cli = Cli::try_parse_from([
        "dexdec",
        "decompile",
        "classes.dex",
        "--language",
        "java",
        "--no-inner",
    ])
    .unwrap();
    let Command::Decompile(request) = cli.into_command() else {
        panic!("expected decompile command");
    };

    assert_eq!(request.language, SourceLanguage::Java);
    assert!(!request.include_inner);
}
