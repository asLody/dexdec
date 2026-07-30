mod common;

use dexdec::api::DecompilerContext;

fn load_testcase(name: &str) -> (DecompilerContext, String) {
    let dex_path =
        common::compile_testcase(name).expect(&format!("failed to compile test case: {}", name));

    let ctx = DecompilerContext::from_file(&dex_path)
        .expect(&format!("failed to load dex file: {:?}", dex_path));

    let class_name = format!("L{};", name);
    (ctx, class_name)
}

#[test]
fn test_method_level_constructor_decompile_keeps_super_delegate() {
    let (mut ctx, class_name) = load_testcase("ConstructorDelegate");

    let output = ctx
        .decompile_method(&class_name, "<init>", Some("(I)V"))
        .expect("constructor decompile should succeed")
        .expect("constructor should be present");

    assert!(output.contains(": super(p0)"), "{output}");
    assert!(!output.contains("this.<init>()"), "{output}");
}
