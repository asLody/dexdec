mod common;

use dexdec::api::DecompilerContext;
use dexdec::frontend::AnalysisState;

fn load_testcase(name: &str) -> (DecompilerContext, String) {
    let dex_path =
        common::compile_testcase(name).expect(&format!("failed to compile test case: {}", name));

    let ctx = DecompilerContext::from_file(&dex_path)
        .expect(&format!("failed to load dex file: {:?}", dex_path));

    let class_name = format!("L{};", name);
    (ctx, class_name)
}

#[test]
fn context_load_class_transitions_override_analysis_to_ready() {
    let (mut ctx, class_name) = load_testcase("TryCatch");

    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Dirty);

    ctx.load_class(&class_name)
        .expect("class load should succeed")
        .expect("class should exist");

    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Ready);
}

#[test]
fn context_load_class_is_revision_stable_when_class_is_already_loaded() {
    let (mut ctx, class_name) = load_testcase("TryCatch");

    ctx.load_class(&class_name)
        .expect("first class load should succeed")
        .expect("class should exist");
    let first_revision = ctx.reader().loaded_classes_revision();
    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Ready);

    ctx.load_class(&class_name)
        .expect("second class load should succeed")
        .expect("class should exist");

    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Ready);
    assert_eq!(ctx.reader().loaded_classes_revision(), first_revision);
}

#[test]
fn context_load_all_classes_is_revision_stable_when_repeated() {
    let (mut ctx, _class_name) = load_testcase("TryCatch");

    ctx.load_all_classes().expect("first load should succeed");
    let first_revision = ctx.reader().loaded_classes_revision();
    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Ready);

    ctx.load_all_classes().expect("second load should succeed");

    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Ready);
    assert_eq!(ctx.reader().loaded_classes_revision(), first_revision);
}

#[test]
fn reader_mut_load_class_is_recovered_by_decompile_method() {
    let (mut ctx, class_name) = load_testcase("TryCatch");

    ctx.reader_mut()
        .load_class(&class_name)
        .expect("reader load should succeed")
        .expect("class should exist");
    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Dirty);

    let output = ctx
        .decompile_method(&class_name, "divide", Some("(II)I"))
        .expect("method decompile should succeed")
        .expect("method should exist");

    assert_eq!(ctx.reader().override_analysis_state(), AnalysisState::Ready);
    assert!(output.contains(": ArithmeticException)"), "{output}");
}
