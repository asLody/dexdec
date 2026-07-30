use dexdec::{Decompiler, ReferenceTarget};

#[test]
fn finds_symbol_uses_without_loading_classes() {
    let dex = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/testcases/classes.dex");
    let mut decompiler = Decompiler::open(dex).expect("open test DEX");
    let results = decompiler
        .references(ReferenceTarget::method(
            "Ljava/io/PrintStream;",
            "println",
            "(Ljava/lang/String;)V",
        ))
        .expect("scan references");

    assert!(results.locations.iter().any(|location| {
        location.class == "LHelloWorld;"
            && location.method == "main"
            && location.descriptor == "([Ljava/lang/String;)V"
    }));
    let overload_results = decompiler
        .references(ReferenceTarget::method_arity(
            "Ljava/io/PrintStream;",
            "println",
            1,
        ))
        .expect("scan method overload references");
    assert!(overload_results.locations.iter().any(|location| {
        location.class == "LHelloWorld;"
            && location.method == "main"
            && location.descriptor == "([Ljava/lang/String;)V"
    }));
    let parameter_results = decompiler
        .references(ReferenceTarget::method_parameters(
            "Ljava/io/PrintStream;",
            "println",
            ["Ljava/lang/String;"],
        ))
        .expect("scan method-parameter references");
    assert!(parameter_results.locations.iter().any(|location| {
        location.class == "LHelloWorld;"
            && location.method == "main"
            && location.descriptor == "([Ljava/lang/String;)V"
    }));

    let field_results = decompiler
        .references(ReferenceTarget::field(
            "Ljava/lang/System;",
            "out",
            "Ljava/io/PrintStream;",
        ))
        .expect("scan field references");
    assert!(field_results
        .locations
        .iter()
        .any(|location| location.class == "LHelloWorld;" && location.method == "main"));
    let field_name_results = decompiler
        .references(ReferenceTarget::field_name("Ljava/lang/System;", "out"))
        .expect("scan field-name references");
    assert!(field_name_results
        .locations
        .iter()
        .any(|location| location.class == "LHelloWorld;" && location.method == "main"));

    let class_results = decompiler
        .references(ReferenceTarget::class("Ljava/lang/String;"))
        .expect("scan class references");
    assert!(class_results
        .locations
        .iter()
        .any(|location| location.class == "LHelloWorld;" && location.method == "main"));
}
