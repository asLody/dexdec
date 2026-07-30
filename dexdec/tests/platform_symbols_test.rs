use dexdec::{
    PlatformConstant, PlatformConstantDomain, PlatformConstantKind, PlatformConstantMember,
    PlatformFamily, PlatformFieldReference, PlatformSymbolDatabase, PlatformTarget,
};

const EMBEDDED: &[u8] = include_bytes!("../resources/symbols/platform.dexsym");

#[test]
fn embedded_symbols_cover_java_and_android_abis() {
    let database = PlatformSymbolDatabase::from_bytes(EMBEDDED).expect("embedded platform symbols");
    let stats = database.stats();
    assert_eq!(database.default_target(), PlatformTarget::android(36));
    assert!(stats.selected_classes > 12_000);
    assert!(stats.methods > 120_000);
    assert!(database
        .sources()
        .iter()
        .any(|source| source.family == PlatformFamily::Java));
    assert!(database
        .sources()
        .iter()
        .any(|source| source.family == PlatformFamily::Android));

    let symbols = database.select(PlatformTarget::android(36));
    let list = symbols
        .class("Ljava/util/List;")
        .expect("java.util.List platform ABI");
    assert!(list
        .signature
        .as_deref()
        .is_some_and(|signature| { signature.starts_with("<E:Ljava/lang/Object;>") }));
    assert!(list
        .methods
        .iter()
        .any(|method| method.name == "addAll" && method.descriptor == "(Ljava/util/Collection;)Z"));
    assert!(symbols.is_subtype("Ljava/lang/String;", "Ljava/lang/CharSequence;"));
    assert!(symbols.is_subtype("Ljava/util/ArrayList;", "Ljava/util/List;"));
    assert!(!symbols.is_subtype("Ljava/lang/CharSequence;", "Ljava/lang/String;"));

    let activity = symbols
        .class("Landroid/app/Activity;")
        .expect("android.app.Activity platform ABI");
    assert!(activity.methods.iter().any(
        |method| method.name == "findViewById" && method.descriptor == "(I)Landroid/view/View;"
    ));
}

#[test]
fn embedded_symbols_include_kotlin_source_abi() {
    let database = PlatformSymbolDatabase::from_bytes(EMBEDDED).expect("embedded platform symbols");
    assert!(database.sources().iter().any(|source| {
        source.family == PlatformFamily::Library && source.name.starts_with("kotlin-stdlib-")
    }));

    let symbols = database.select(PlatformTarget::android(36));
    let facade = symbols
        .class("Lkotlin/collections/ArraysKt;")
        .expect("Kotlin arrays facade");
    assert_eq!(
        facade.super_class.as_deref(),
        Some("Lkotlin/collections/ArraysKt___ArraysKt;")
    );
    let (declaration, _) = symbols
        .resolve_method(
            "Lkotlin/collections/ArraysKt;",
            "joinToString$default",
            "([Ljava/lang/Object;Ljava/lang/CharSequence;Ljava/lang/CharSequence;Ljava/lang/CharSequence;ILjava/lang/CharSequence;Lkotlin/jvm/functions/Function1;ILjava/lang/Object;)Ljava/lang/String;",
        )
        .expect("Kotlin default dispatcher through facade hierarchy");
    assert_eq!(
        declaration.descriptor,
        "Lkotlin/collections/ArraysKt___ArraysKt;"
    );
    assert!(declaration
        .annotations
        .iter()
        .any(|annotation| annotation.descriptor == "Lkotlin/Metadata;"));
}

#[test]
fn android_constant_domains_are_exact_and_ambiguity_safe() {
    let database = PlatformSymbolDatabase::from_bytes(EMBEDDED).expect("embedded platform symbols");
    let symbols = database.select(PlatformTarget::android(36));
    let flags = symbols
        .parameter_domain(
            "Landroid/content/Intent;",
            "setFlags",
            "(I)Landroid/content/Intent;",
            0,
        )
        .expect("Intent.setFlags parameter domain");
    assert!(flags
        .resolve(&PlatformConstant::Integer(0x1400_0000))
        .is_none());

    let orientation = symbols
        .parameter_domain(
            "Landroid/app/Activity;",
            "setRequestedOrientation",
            "(I)V",
            0,
        )
        .expect("Activity.setRequestedOrientation parameter domain");
    let fields = orientation
        .resolve(&PlatformConstant::Integer(1))
        .expect("unique orientation constant")
        .into_iter()
        .map(|member| member.field.name.as_str())
        .collect::<Vec<_>>();
    assert_eq!(fields, ["SCREEN_ORIENTATION_PORTRAIT"]);

    assert!(symbols
        .parameter_domain(
            "Landroid/app/Activity;",
            "startActivityForResult",
            "(Landroid/content/Intent;I)V",
            1,
        )
        .is_none());
}

#[test]
fn flag_decomposition_requires_one_minimum_solution() {
    let member = |name: &str, value: i64| PlatformConstantMember {
        field: PlatformFieldReference {
            owner: "Lexample/Flags;".to_string(),
            name: name.to_string(),
            descriptor: "I".to_string(),
        },
        value: PlatformConstant::Integer(value),
    };
    let mut domain = PlatformConstantDomain {
        kind: PlatformConstantKind::Integer,
        flags: true,
        members: vec![member("READ", 1), member("WRITE", 2)],
    };
    let fields = domain
        .resolve(&PlatformConstant::Integer(3))
        .expect("unique minimum flag decomposition")
        .into_iter()
        .map(|member| member.field.name.as_str())
        .collect::<Vec<_>>();
    assert_eq!(fields, ["READ", "WRITE"]);

    domain.members.push(member("READ_ALIAS", 1));
    assert!(domain.resolve(&PlatformConstant::Integer(3)).is_none());
}

#[test]
fn dexsym_codec_is_deterministic_and_lossless() {
    let database = PlatformSymbolDatabase::from_bytes(EMBEDDED).expect("embedded platform symbols");
    let encoded = database.to_bytes().expect("encode platform symbols");
    let decoded = PlatformSymbolDatabase::from_bytes(&encoded).expect("decode platform symbols");
    assert_eq!(decoded, database);
    assert_eq!(
        encoded,
        decoded.to_bytes().expect("deterministic re-encode")
    );
}
