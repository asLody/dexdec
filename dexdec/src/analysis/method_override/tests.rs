use super::*;
use std::collections::BTreeMap;

#[test]
fn loads_platform_symbol_methods() {
    let platform = PlatformClassSet::load_default().expect("platform symbols should load");
    let class = platform
        .class_details(&ArgType::object("java/util/AbstractMap"))
        .expect("AbstractMap should be in platform symbols");
    assert!(class.methods.iter().any(|method| {
        method.reference.short_id == "size()I"
            && method.reference.declaring_class == "Ljava/util/AbstractMap;"
    }));
}

#[test]
fn embedded_platform_resource_is_available() {
    let platform = default_platform_symbols().expect("embedded dexsym parses");
    assert!(platform.class("Ljava/util/Map;").is_some());
}

#[test]
fn resolves_inherited_platform_generic_method_contract() {
    let hierarchy =
        GenericTypeHierarchy::from_classes(std::iter::empty::<&ClassNode>()).expect("hierarchy");
    let method = "Ljava/util/concurrent/ConcurrentMap;->computeIfAbsent(Ljava/lang/Object;Ljava/util/function/Function;)Ljava/lang/Object;"
        .parse()
        .expect("method reference");
    let contract = hierarchy
        .method_contract(&method)
        .expect("inherited generic method contract");

    assert_eq!(
        contract.owner_type_parameters().collect::<Vec<_>>(),
        vec!["K", "V"]
    );
    assert_eq!(
        contract.signature,
        GenericSignatures::method("(TK;Ljava/util/function/Function<-TK;+TV;>;)TV;")
            .expect("generic method signature")
    );
}

#[test]
fn resolves_declared_platform_generic_method_contract() {
    let hierarchy =
        GenericTypeHierarchy::from_classes(std::iter::empty::<&ClassNode>()).expect("hierarchy");
    let method = "Ljava/util/Comparator;->compare(Ljava/lang/Object;Ljava/lang/Object;)I"
        .parse()
        .expect("method reference");
    let contract = hierarchy
        .method_contract(&method)
        .expect("declared generic method contract");

    assert_eq!(
        contract.owner_type_parameters().collect::<Vec<_>>(),
        vec!["T"]
    );
    assert_eq!(
        contract.signature,
        GenericSignatures::method("(TT;TT;)I").expect("generic method signature")
    );
}

#[test]
fn infers_parameterized_platform_subtype_from_target_type() {
    let hierarchy =
        GenericTypeHierarchy::from_classes(std::iter::empty::<&ClassNode>()).expect("hierarchy");
    let expected = GenericSignatures::field("Ljava/util/List<Ljava/lang/String;>;")
        .expect("parameterized List");
    let inferred = hierarchy
        .infer_subtype(&ArgType::object("java/util/ArrayList"), &expected)
        .expect("ArrayList should inherit the List element type");

    assert_eq!(
        inferred,
        GenericSignatures::field("Ljava/util/ArrayList<Ljava/lang/String;>;")
            .expect("parameterized ArrayList")
    );
}

#[test]
fn detects_override_against_platform_hierarchy() {
    let platform = PlatformClassSet::load_default().expect("platform symbols should load");
    let hierarchy = TestHierarchy {
        platform,
        app: ClassDetails {
            descriptor: "Lcom/example/MyMap;".to_string(),
            package: "com.example".to_string(),
            access_flags: AccessInfo::for_class(0x0001),
            parents: vec![ArgType::object("java/util/AbstractMap")],
            generic_parents: vec![JvmTypeSignature::ClassType(parse_class_type_signature(
                "java/util/AbstractMap",
            ))],
            generic_signature: None,
            instantiated_self: None,
            methods: vec![MethodDetails {
                reference: MethodReference {
                    declaring_class: "Lcom/example/MyMap;".to_string(),
                    short_id: "size()I".to_string(),
                },
                params: Vec::new(),
                return_type: ArgType::INT,
                generic_signature: None,
                throws: Vec::new(),
                access_flags: AccessInfo::for_method(0x0001),
            }],
        },
    };
    let method = hierarchy.app.methods[0].clone();
    let analyzer = MethodOverrideAnalyzer::new(&hierarchy);
    let ancestors = analyzer
        .collect_super_types(&hierarchy.app)
        .expect("ancestor analysis should succeed");
    let semantics = analyzer
        .analyze_method(&hierarchy.app, &method, &ancestors)
        .expect("override analysis should succeed")
        .expect("size should override AbstractMap.size");
    assert!(semantics
        .overridden_methods
        .iter()
        .any(|method| method.declaring_class == "Ljava/util/AbstractMap;"
            && method.short_id == "size()I"));
}

#[test]
fn detects_covariant_return_override() {
    let hierarchy = LocalHierarchy::new([
        class("Ljava/lang/Number;", [], [], "java.lang"),
        class(
            "Ljava/lang/Integer;",
            ["Ljava/lang/Number;"],
            [],
            "java.lang",
        ),
        class(
            "Lcom/example/Base;",
            [],
            [method(
                "Lcom/example/Base;",
                "value()Ljava/lang/Number;",
                vec![],
                ArgType::object("java/lang/Number"),
                0x0001,
            )],
            "com.example",
        ),
        class(
            "Lcom/example/Child;",
            ["Lcom/example/Base;"],
            [method(
                "Lcom/example/Child;",
                "value()Ljava/lang/Integer;",
                vec![],
                ArgType::object("java/lang/Integer"),
                0x0001,
            )],
            "com.example",
        ),
    ]);
    let child = hierarchy
        .class_details(&ArgType::object("com/example/Child"))
        .expect("child class");
    let method = child.methods[0].clone();

    let analyzer = MethodOverrideAnalyzer::new(&hierarchy);
    let ancestors = analyzer
        .collect_super_types(&child)
        .expect("ancestor analysis should succeed");
    let semantics = analyzer
        .analyze_method(&child, &method, &ancestors)
        .expect("override analysis should succeed")
        .expect("covariant return should override");

    assert_eq!(
        semantics.overridden_methods,
        vec![MethodReference {
            declaring_class: "Lcom/example/Base;".to_string(),
            short_id: "value()Ljava/lang/Number;".to_string(),
        }]
    );
}

#[test]
fn does_not_match_distinct_object_parameter_types() {
    let hierarchy = LocalHierarchy::new([
        class(
            "Lcom/example/Base;",
            [],
            [method(
                "Lcom/example/Base;",
                "put(Ljava/lang/String;)V",
                vec![ArgType::object("java/lang/String")],
                ArgType::VOID,
                0x0001,
            )],
            "com.example",
        ),
        class(
            "Lcom/example/Child;",
            ["Lcom/example/Base;"],
            [method(
                "Lcom/example/Child;",
                "put(Ljava/lang/Integer;)V",
                vec![ArgType::object("java/lang/Integer")],
                ArgType::VOID,
                0x0001,
            )],
            "com.example",
        ),
    ]);
    let child = hierarchy
        .class_details(&ArgType::object("com/example/Child"))
        .expect("child class");
    let method = child.methods[0].clone();

    let analyzer = MethodOverrideAnalyzer::new(&hierarchy);
    let ancestors = analyzer
        .collect_super_types(&child)
        .expect("ancestor analysis should succeed");
    let semantics = analyzer
        .analyze_method(&child, &method, &ancestors)
        .expect("override analysis should succeed");
    assert!(
        semantics.is_none(),
        "different object params must not override"
    );
}

#[test]
fn prefers_non_bridge_exact_signature_candidate() {
    let hierarchy = LocalHierarchy::new([
        class(
            "Lcom/example/Base;",
            [],
            [
                method(
                    "Lcom/example/Base;",
                    "get()Ljava/lang/Object;",
                    vec![],
                    ArgType::object("java/lang/Object"),
                    0x0041,
                ),
                method(
                    "Lcom/example/Base;",
                    "get()Ljava/lang/String;",
                    vec![],
                    ArgType::object("java/lang/String"),
                    0x0001,
                ),
            ],
            "com.example",
        ),
        class(
            "Lcom/example/Child;",
            ["Lcom/example/Base;"],
            [method(
                "Lcom/example/Child;",
                "get()Ljava/lang/String;",
                vec![],
                ArgType::object("java/lang/String"),
                0x0001,
            )],
            "com.example",
        ),
    ]);
    let child = hierarchy
        .class_details(&ArgType::object("com/example/Child"))
        .expect("child class");
    let method = child.methods[0].clone();

    let analyzer = MethodOverrideAnalyzer::new(&hierarchy);
    let ancestors = analyzer
        .collect_super_types(&child)
        .expect("ancestor analysis should succeed");
    let semantics = analyzer
        .analyze_method(&child, &method, &ancestors)
        .expect("override analysis should succeed")
        .expect("real method should be preferred");

    assert_eq!(
        semantics.overridden_methods,
        vec![MethodReference {
            declaring_class: "Lcom/example/Base;".to_string(),
            short_id: "get()Ljava/lang/String;".to_string(),
        }]
    );
    assert_eq!(semantics.base_methods, semantics.overridden_methods);
}

#[test]
fn inherited_signature_tracks_instantiated_generic_base_method() {
    let hierarchy = LocalHierarchy::new([
        class_with_signature(
            "Lcom/example/Base;",
            [],
            [method_with_signature(
                "Lcom/example/Base;",
                "value()Ljava/lang/Object;",
                vec![],
                ArgType::object("java/lang/Object"),
                Some(GenericSignatures::method("()TT;").expect("generic method signature")),
                0x0001,
            )],
            Some(
                GenericSignatures::class("<T:Ljava/lang/Object;>Ljava/lang/Object;")
                    .expect("base class signature"),
            ),
            "com.example",
        ),
        class_with_signature(
            "Lcom/example/Child;",
            ["Lcom/example/Base;"],
            [method(
                "Lcom/example/Child;",
                "value()Ljava/lang/String;",
                vec![],
                ArgType::object("java/lang/String"),
                0x0001,
            )],
            Some(
                GenericSignatures::class("Lcom/example/Base<Ljava/lang/String;>;")
                    .expect("child class signature"),
            ),
            "com.example",
        ),
    ]);
    let child = hierarchy
        .class_details(&ArgType::object("com/example/Child"))
        .expect("child class");
    let method = child.methods[0].clone();

    let analyzer = MethodOverrideAnalyzer::new(&hierarchy);
    let ancestors = analyzer
        .collect_super_types(&child)
        .expect("ancestor analysis should succeed");
    let semantics = analyzer
        .analyze_method(&child, &method, &ancestors)
        .expect("override analysis should succeed")
        .expect("generic override should resolve");

    let inherited = semantics
        .inherited_signature
        .expect("inherited signature should be preserved");
    assert_eq!(inherited.parameter_types.len(), 0);
    assert_eq!(
        inherited.return_type,
        JvmTypeSignature::ClassType(parse_class_type_signature("java/lang/String"))
    );
}

#[test]
fn platform_list_iterator_keeps_generic_signature() {
    let platform = PlatformClassSet::load_default().expect("platform symbols should load");
    let list = platform
        .class_details(&ArgType::object("java/util/List"))
        .expect("List should be in platform symbols");
    let iterator = list
        .methods
        .iter()
        .find(|method| method.reference.short_id == "iterator()Ljava/util/Iterator;")
        .expect("iterator method");
    assert!(
        iterator.generic_signature.is_some(),
        "iterator generic signature missing: {:?}",
        iterator
    );
    let signature = iterator
        .generic_signature
        .as_ref()
        .expect("iterator generic signature");
    assert_eq!(
        signature.return_type,
        JvmTypeSignature::ClassType(ClassTypeSignature {
            raw_name: "java/util/Iterator".to_string(),
            type_arguments: vec![TypeArgument::Exact(JvmTypeSignature::TypeVariable(
                "E".to_string()
            ))],
            inner_segments: Vec::new(),
        })
    );
}

#[test]
fn platform_generic_method_keeps_type_variable_return() {
    let platform = PlatformClassSet::load_default().expect("platform symbols should load");
    let key_factory = platform
        .class_details(&ArgType::object("java/security/KeyFactorySpi"))
        .expect("KeyFactorySpi should be in platform symbols");
    let method = key_factory
        .methods
        .iter()
        .find(|method| {
            method.reference.short_id
                == "engineGetKeySpec(Ljava/security/Key;Ljava/lang/Class;)Ljava/security/spec/KeySpec;"
        })
        .expect("engineGetKeySpec should be in platform symbols");
    let signature = method
        .generic_signature
        .as_ref()
        .expect("engineGetKeySpec should retain its generic signature");

    assert_eq!(
        signature.return_type,
        JvmTypeSignature::TypeVariable("T".to_string())
    );
}

#[test]
fn binds_outer_and_inner_generic_scopes() {
    let outer = class_with_signature(
        "Lcom/example/Outer;",
        [],
        [],
        Some(
            GenericSignatures::class(
                "<K:Ljava/lang/Object;V:Ljava/lang/Object;>Ljava/lang/Object;",
            )
            .expect("outer signature"),
        ),
        "com.example",
    );
    let inner = class_with_signature(
        "Lcom/example/Outer$Inner;",
        [],
        [method_with_signature(
            "Lcom/example/Outer$Inner;",
            "combine(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
            vec![
                ArgType::object("java/lang/Object"),
                ArgType::object("java/lang/Object"),
            ],
            ArgType::object("java/lang/Object"),
            Some(GenericSignatures::method("(TK;TT;)TV;").expect("inner method signature")),
            0x0001,
        )],
        Some(
            GenericSignatures::class("<T:Ljava/lang/Object;>Ljava/lang/Object;")
                .expect("inner signature"),
        ),
        "com.example",
    );
    let hierarchy = LocalHierarchy::new([outer, inner.clone()]);
    let instantiated = GenericSignatures::field(
        "Lcom/example/Outer<Ljava/lang/String;Ljava/lang/Integer;>.Inner<Ljava/lang/Long;>;",
    )
    .expect("instantiated inner type");

    let bound = bind_class(&hierarchy, &inner, &instantiated).expect("nested binding");
    let method = bound.methods.first().expect("bound method");
    let signature = method.generic_signature.as_ref().expect("generic method");

    assert_eq!(
        signature.parameter_types,
        vec![
            JvmTypeSignature::ClassType(parse_class_type_signature("java/lang/String")),
            JvmTypeSignature::ClassType(parse_class_type_signature("java/lang/Long")),
        ]
    );
    assert_eq!(
        signature.return_type,
        JvmTypeSignature::ClassType(parse_class_type_signature("java/lang/Integer"))
    );
}

#[test]
fn incomplete_functionn_instantiation_does_not_fail_scope_binding() {
    let function3 = class_with_signature(
        "Lkotlin/jvm/functions/Function3;",
        ["Ljava/lang/Object;"],
        [],
        Some(
            GenericSignatures::class(
                "<P1:Ljava/lang/Object;P2:Ljava/lang/Object;P3:Ljava/lang/Object;R:Ljava/lang/Object;>Ljava/lang/Object;",
            )
            .expect("Function3 class signature"),
        ),
        "kotlin.jvm.functions",
    );
    let args = ["java/lang/String", "java/lang/Integer", "java/lang/Long"]
        .into_iter()
        .map(|name| {
            TypeArgument::Exact(JvmTypeSignature::ClassType(parse_class_type_signature(
                name,
            )))
        })
        .collect::<Vec<_>>();
    let mut substitutions = TypeSubstitution::new();

    collect_scope_type_parameters(&function3, &args, &mut substitutions)
        .expect("Function3 instantiated with three arguments must not fail");
}

#[test]
fn incomplete_functionn_parent_does_not_abort_override_analysis() {
    let function3 = class_with_signature(
        "Lkotlin/jvm/functions/Function3;",
        ["Ljava/lang/Object;"],
        [method(
            "Lkotlin/jvm/functions/Function3;",
            "invoke(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
            vec![
                ArgType::object("java/lang/Object"),
                ArgType::object("java/lang/Object"),
                ArgType::object("java/lang/Object"),
            ],
            ArgType::object("java/lang/Object"),
            0x0401,
        )],
        Some(
            GenericSignatures::class(
                "<P1:Ljava/lang/Object;P2:Ljava/lang/Object;P3:Ljava/lang/Object;R:Ljava/lang/Object;>Ljava/lang/Object;",
            )
            .expect("Function3 class signature"),
        ),
        "kotlin.jvm.functions",
    );
    let child = class_with_signature(
        "Lcom/example/Callback;",
        ["Lkotlin/jvm/functions/Function3;"],
        [method(
            "Lcom/example/Callback;",
            "invoke(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
            vec![
                ArgType::object("java/lang/Object"),
                ArgType::object("java/lang/Object"),
                ArgType::object("java/lang/Object"),
            ],
            ArgType::object("java/lang/Object"),
            0x0001,
        )],
        Some(
            GenericSignatures::class(
                "Ljava/lang/Object;Lkotlin/jvm/functions/Function3<Ljava/lang/String;Ljava/lang/Integer;Ljava/lang/Long;>;",
            )
            .expect("three-argument Function3 instantiation"),
        ),
        "com.example",
    );
    let hierarchy = LocalHierarchy::new([function3, child.clone()]);
    let analyzer = MethodOverrideAnalyzer::new(&hierarchy);
    let ancestors = analyzer
        .collect_super_types(&child)
        .expect("ancestor walk must survive a Function3 arity mismatch");
    assert!(ancestors
        .iter()
        .any(|class| class.descriptor == "Lkotlin/jvm/functions/Function3;"));

    let mut sink = OverrideSink::default();
    analyzer
        .analyze(&mut sink, std::slice::from_ref(&child))
        .expect("archive override analysis must not fail");
    assert!(sink.0.iter().any(|(class, method)| {
        class == "Lcom/example/Callback;"
            && method
                == "invoke(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"
    }));
}

#[test]
fn override_analysis_skips_a_broken_class_and_continues() {
    let healthy = class(
        "Lcom/example/Ok;",
        ["Ljava/lang/Object;"],
        [method(
            "Lcom/example/Ok;",
            "size()I",
            Vec::new(),
            ArgType::INT,
            0x0001,
        )],
        "com.example",
    );
    let broken = ClassDetails {
        descriptor: "Lcom/example/Broken;".to_string(),
        package: "com.example".to_string(),
        access_flags: AccessInfo::for_class(0x0001),
        parents: vec![ArgType::object("java/lang/Object")],
        generic_parents: Vec::new(),
        generic_signature: None,
        instantiated_self: None,
        methods: vec![method(
            "Lcom/example/Broken;",
            "size()I",
            Vec::new(),
            ArgType::INT,
            0x0001,
        )],
    };
    let hierarchy = LocalHierarchy::new([healthy.clone(), broken.clone()]);
    let mut sink = OverrideSink::default();
    MethodOverrideAnalyzer::new(&hierarchy)
        .analyze(&mut sink, &[broken, healthy])
        .expect("one broken class must not abort the archive");
    assert!(
        sink.0.iter().any(|(class, _)| class == "Lcom/example/Ok;"),
        "healthy class should still be analyzed"
    );
}

#[derive(Default)]
struct OverrideSink(Vec<(String, String)>);

impl OverrideAnalysisTarget for OverrideSink {
    fn set_method_override(
        &mut self,
        declaring_class: &str,
        method_short_id: &str,
        _semantics: Option<MethodOverrideSemantics>,
    ) {
        self.0
            .push((declaring_class.to_string(), method_short_id.to_string()));
    }
}

struct TestHierarchy {
    app: ClassDetails,
    platform: PlatformClassSet,
}

impl ClassHierarchy for TestHierarchy {
    fn class_details(&self, ty: &ArgType) -> Option<ClassDetails> {
        if ty.to_descriptor() == self.app.descriptor {
            return Some(self.app.clone());
        }
        self.platform.class_details(ty)
    }
}

#[derive(Default)]
struct LocalHierarchy {
    classes: BTreeMap<String, ClassDetails>,
}

impl LocalHierarchy {
    fn new<const N: usize>(classes: [ClassDetails; N]) -> Self {
        Self {
            classes: classes
                .into_iter()
                .map(|class| (class.descriptor.clone(), class))
                .collect(),
        }
    }
}

impl ClassHierarchy for LocalHierarchy {
    fn class_details(&self, ty: &ArgType) -> Option<ClassDetails> {
        self.classes.get(&ty.to_descriptor()).cloned()
    }
}

fn class<const P: usize, const M: usize>(
    descriptor: &str,
    parents: [&str; P],
    methods: [MethodDetails; M],
    package: &str,
) -> ClassDetails {
    class_with_signature(descriptor, parents, methods, None, package)
}

fn class_with_signature<const P: usize, const M: usize>(
    descriptor: &str,
    parents: [&str; P],
    methods: [MethodDetails; M],
    generic_signature: Option<ClassSignature>,
    package: &str,
) -> ClassDetails {
    let parsed_parents = parents
        .into_iter()
        .map(|parent| {
            parent
                .parse::<ArgType>()
                .unwrap_or_else(|_| panic!("invalid type: {parent}"))
        })
        .collect::<Vec<_>>();
    let generic_parents = if let Some(signature) = generic_signature.as_ref() {
        let mut values = Vec::new();
        values.push(JvmTypeSignature::ClassType(signature.super_class.clone()));
        values.extend(
            signature
                .super_interfaces
                .iter()
                .cloned()
                .map(JvmTypeSignature::ClassType),
        );
        values
    } else {
        parsed_parents
            .iter()
            .map(arg_type_to_signature)
            .collect::<OverrideResult<Vec<_>>>()
            .expect("test parent types are concrete")
    };
    ClassDetails {
        descriptor: descriptor.to_string(),
        package: package.to_string(),
        access_flags: AccessInfo::for_class(0x0001),
        parents: parsed_parents,
        generic_parents,
        generic_signature,
        instantiated_self: None,
        methods: methods.into_iter().collect(),
    }
}

fn method(
    declaring_class: &str,
    short_id: &str,
    params: Vec<ArgType>,
    return_type: ArgType,
    access_flags: u32,
) -> MethodDetails {
    method_with_signature(
        declaring_class,
        short_id,
        params,
        return_type,
        None,
        access_flags,
    )
}

fn method_with_signature(
    declaring_class: &str,
    short_id: &str,
    params: Vec<ArgType>,
    return_type: ArgType,
    generic_signature: Option<MethodSignature>,
    access_flags: u32,
) -> MethodDetails {
    MethodDetails {
        reference: MethodReference {
            declaring_class: declaring_class.to_string(),
            short_id: short_id.to_string(),
        },
        params,
        return_type,
        generic_signature,
        throws: Vec::new(),
        access_flags: AccessInfo::for_method(access_flags),
    }
}
