use clap::Parser;

use dexdec::cli::{Cli, Command, LanguageSelection};
use dexdec::SourceLanguage;

#[test]
fn decompile_defaults_to_auto_language() {
    let cli = Cli::try_parse_from(["dexdec", "decompile", "classes.dex"]).unwrap();
    let Command::Decompile(request) = cli.into_invocation().command else {
        panic!("expected decompile command");
    };

    assert_eq!(request.language, LanguageSelection::Auto);
    assert!(request.include_nested);
}

#[test]
fn decompile_accepts_java_without_nested_classes() {
    let cli = Cli::try_parse_from([
        "dexdec",
        "decompile",
        "classes.dex",
        "--language",
        "java",
        "--no-nested",
    ])
    .unwrap();
    let Command::Decompile(request) = cli.into_invocation().command else {
        panic!("expected decompile command");
    };

    assert_eq!(
        request.language,
        LanguageSelection::Fixed(SourceLanguage::Java)
    );
    assert!(!request.include_nested);
}
