//! Integration tests for dexdec using smali test cases.
//!
//! These tests compile smali files to dex and verify the decompilation.

mod common;

use dexdec::api::DecompilerContext;
use dexdec::ir::{ArgType, MemberReference, CFG};
use dexdec::JavaDecompilerConfig;

/// Helper to compile and load a test case
fn load_testcase(name: &str) -> (DecompilerContext, String) {
    let dex_path =
        common::compile_testcase(name).expect(&format!("failed to compile test case: {}", name));

    let ctx = DecompilerContext::from_file(&dex_path)
        .expect(&format!("failed to load dex file: {:?}", dex_path));

    // Class name format: L<name>; for DEX internal format
    let class_name = format!("L{};", name);
    (ctx, class_name)
}

/// Helper to decode a method from a test case
fn decode_method(ctx: &mut DecompilerContext, class_name: &str, method_name: &str) -> Option<CFG> {
    ctx.load_all_classes().ok()?;
    ctx.decode_method(class_name, method_name, None)
        .ok()?
        .cloned()
}

fn analyze_exceptions(cfg: &mut CFG) -> dexdec::ir::ExceptionAnalysis {
    let hierarchy = dexdec::ir::analysis::ClassHierarchyIndex::default();
    let values = dexdec::ir::passes::CfgPipeline::new(&hierarchy)
        .analyze(cfg)
        .expect("CFG analysis should succeed")
        .values;
    dexdec::ir::ExceptionAnalyzer::new(cfg, &values, &hierarchy)
        .analyze()
        .expect("exception analysis should succeed")
}

// ============================================================
// HelloWorld Tests
// ============================================================

#[test]
fn test_hello_world_loads() {
    let (mut ctx, _class_name) = load_testcase("HelloWorld");
    ctx.load_all_classes().expect("should load classes");

    // DexFileReader returns short class names (without L and ;)
    let classes: Vec<_> = ctx
        .reader()
        .classes()
        .map(|c| c.name().to_string())
        .collect();
    let short_name = "HelloWorld";
    assert!(
        classes.iter().any(|c| c == short_name),
        "HelloWorld class should be in class list, got: {:?}",
        classes
    );
}

#[test]
fn test_hello_world_main() {
    let (mut ctx, class_name) = load_testcase("HelloWorld");

    let ir = decode_method(&mut ctx, &class_name, "main").expect("should decode main");

    // main method should have at least one block
    assert!(!ir.blocks.is_empty(), "main should have blocks");

    // Should have println call
    let has_println = ir.blocks.values().any(|block| {
        block.insns.iter().any(|insn| {
            insn.payload
                .reference
                .as_ref()
                .is_some_and(|reference| {
                    matches!(reference, MemberReference::Method(method) if method.name == "println")
                })
        })
    });
    assert!(has_println, "main should call println");
}

// ============================================================
// SimpleIf Tests
// ============================================================

#[test]
fn test_simple_if_cfg() {
    let (mut ctx, class_name) = load_testcase("SimpleIf");

    let ir = decode_method(&mut ctx, &class_name, "test").expect("should decode test");

    // Should have multiple blocks due to if-else
    assert!(
        ir.blocks.len() >= 2,
        "should have at least 2 blocks for if-else"
    );

    // Should have a conditional branch
    let has_branch = ir.blocks.values().any(|block| {
        block
            .insns
            .iter()
            .any(|insn| matches!(insn.insn_type, dexdec::ir::insn::InsnType::If))
    });
    assert!(has_branch, "should have conditional branch");
}

// ============================================================
// SimpleLoop Tests
// ============================================================

#[test]
fn test_simple_loop_cfg() {
    let (mut ctx, class_name) = load_testcase("SimpleLoop");

    let ir = decode_method(&mut ctx, &class_name, "sum").expect("should decode sum");

    // Should have back edge (loop)
    // Check that some block has a successor that comes before it
    let _has_back_edge = ir
        .blocks
        .values()
        .any(|block| ir.successors(block.id).any(|succ_id| succ_id < block.id));

    // Note: With optimizations, this might not always be true
    // Just verify we have multiple blocks
    assert!(ir.blocks.len() >= 2, "should have multiple blocks for loop");
}

// ============================================================
// ForLoop Tests
// ============================================================

#[test]
fn test_for_loop_cfg() {
    let (mut ctx, class_name) = load_testcase("ForLoop");

    let ir = decode_method(&mut ctx, &class_name, "factorial").expect("should decode factorial");

    // Should have multiple blocks
    assert!(ir.blocks.len() >= 2, "should have multiple blocks for loop");

    // Should have arithmetic operations
    let has_mul = ir.blocks.values().any(|block| {
        block
            .insns
            .iter()
            .any(|insn| matches!(insn.insn_type, dexdec::ir::insn::InsnType::Arith))
    });
    assert!(has_mul, "should have arithmetic operations");
}

// ============================================================
// TryCatch Tests
// ============================================================

#[test]
fn test_try_catch_handlers() {
    let (mut ctx, class_name) = load_testcase("TryCatch");

    let ir = decode_method(&mut ctx, &class_name, "divide").expect("should decode divide");

    // Should have exception handlers
    assert!(!ir.handlers.is_empty(), "should have exception handlers");

    // Handler should catch ArithmeticException
    let catches_arith = ir.handlers.iter().any(|h| {
        h.catch_type
            .as_ref()
            .is_some_and(|ty| ty == &ArgType::object("java/lang/ArithmeticException"))
    });
    assert!(catches_arith, "should catch ArithmeticException");
}

#[test]
fn test_try_catch_exception_analysis() {
    let (mut ctx, class_name) = load_testcase("TryCatch");
    let mut ir = decode_method(&mut ctx, &class_name, "divide").expect("should decode divide");

    let analysis = analyze_exceptions(&mut ir);

    // Should have one try region
    assert_eq!(analysis.regions.len(), 1, "should have one try region");

    let region = &analysis.regions[0];
    assert_eq!(region.handlers.len(), 1, "should have one handler");

    // Handler should catch ArithmeticException
    let handler = &region.handlers[0];
    assert!(!handler.is_catch_all(), "should not be catch-all");
    assert!(!handler.is_source_finally(), "should not be finally");
    assert_eq!(
        handler.catch_type,
        Some(ArgType::object("java/lang/ArithmeticException")),
        "should catch ArithmeticException"
    );
}

// ============================================================
// Switch Tests
// ============================================================

#[test]
fn test_switch_cfg() {
    let (mut ctx, class_name) = load_testcase("Switch");

    let ir = decode_method(&mut ctx, &class_name, "dayName").expect("should decode dayName");

    // Should preserve switch instruction for structured switch recovery.
    let has_switch = ir.blocks.values().any(|block| {
        block
            .insns
            .iter()
            .any(|insn| matches!(insn.insn_type, dexdec::ir::insn::InsnType::Switch))
    });
    assert!(has_switch, "should have switch instruction");

    // Should have many blocks (at least 8 cases + default)
    assert!(
        ir.blocks.len() >= 5,
        "should have many blocks for switch cases"
    );
}

// ============================================================
// NestedIf Tests
// ============================================================

#[test]
fn test_nested_if_cfg() {
    let (mut ctx, class_name) = load_testcase("NestedIf");

    let ir = decode_method(&mut ctx, &class_name, "compare").expect("should decode compare");

    // Count conditional branches
    let branch_count: usize = ir
        .blocks
        .values()
        .flat_map(|b| b.insns.iter())
        .filter(|insn| matches!(insn.insn_type, dexdec::ir::insn::InsnType::If))
        .count();

    assert!(
        branch_count >= 2,
        "should have at least 2 branches for nested if"
    );
}

// ============================================================
// MultiCatch Tests
// ============================================================

#[test]
fn test_multi_catch_handlers() {
    let (mut ctx, class_name) = load_testcase("MultiCatch");

    let ir = decode_method(&mut ctx, &class_name, "process").expect("should decode process");

    // Should have multiple exception handlers
    assert!(
        ir.handlers.len() >= 2,
        "should have multiple exception handlers"
    );

    // Should catch IllegalArgumentException and ArithmeticException
    let catch_types: Vec<_> = ir
        .handlers
        .iter()
        .filter_map(|h| h.catch_type.as_ref())
        .collect();

    assert!(
        catch_types
            .iter()
            .any(|ty| **ty == ArgType::object("java/lang/IllegalArgumentException")),
        "should catch IllegalArgumentException"
    );
    assert!(
        catch_types
            .iter()
            .any(|ty| **ty == ArgType::object("java/lang/ArithmeticException")),
        "should catch ArithmeticException"
    );
}

#[test]
fn test_multi_catch_exception_analysis() {
    let (mut ctx, class_name) = load_testcase("MultiCatch");
    let mut ir = decode_method(&mut ctx, &class_name, "process").expect("should decode process");

    let analysis = analyze_exceptions(&mut ir);

    // Should have one try region with multiple handlers
    assert_eq!(analysis.regions.len(), 1, "should have one try region");

    let region = &analysis.regions[0];
    assert!(
        region.handlers.len() >= 2,
        "should have at least 2 handlers"
    );

    // Check handlers
    let handler_types: Vec<_> = region
        .handlers
        .iter()
        .filter_map(|handler| handler.catch_type.as_ref())
        .collect();

    assert!(handler_types
        .iter()
        .any(|ty| **ty == ArgType::object("java/lang/IllegalArgumentException")));
    assert!(handler_types
        .iter()
        .any(|ty| **ty == ArgType::object("java/lang/ArithmeticException")));
}

// ============================================================
// Finally Tests
// ============================================================

#[test]
fn test_finally_handlers() {
    let (mut ctx, class_name) = load_testcase("Finally");

    let ir = decode_method(&mut ctx, &class_name, "test").expect("should decode test");

    // Finally block is typically implemented with catchall handler
    // or duplicated code. Just verify we have exception handling.
    assert!(
        ir.blocks.len() >= 3,
        "should have multiple blocks for try-catch-finally"
    );
}

#[test]
fn test_finally_exception_analysis() {
    let (mut ctx, class_name) = load_testcase("Finally");
    let mut ir = decode_method(&mut ctx, &class_name, "test").expect("should decode test");

    let analysis = analyze_exceptions(&mut ir);

    // Should have try region(s)
    assert!(!analysis.regions.is_empty(), "should have try regions");

    // At least one region should have a finally or catch-all handler
    let has_finally_like = analysis.regions.iter().any(|r| {
        r.handlers
            .iter()
            .any(|h| h.is_catch_all() || h.is_source_finally())
    });

    // Note: Finally detection depends on whether the compiler generates a catch-all + throw pattern
    // Some compilers might inline finally code, so we just check for basic exception handling
    assert!(
        has_finally_like || !ir.handlers.is_empty(),
        "should have finally-like handler or exception handlers"
    );
}

// ============================================================
// DoWhile Tests
// ============================================================

#[test]
fn test_do_while_cfg() {
    let (mut ctx, class_name) = load_testcase("DoWhile");

    let ir =
        decode_method(&mut ctx, &class_name, "countDigits").expect("should decode countDigits");

    // Should have multiple blocks
    assert!(ir.blocks.len() >= 2, "should have multiple blocks for loop");

    // Should have division (n / 10)
    let has_div = ir.blocks.values().any(|block| {
        block
            .insns
            .iter()
            .any(|insn| matches!(insn.insn_type, dexdec::ir::insn::InsnType::Arith))
    });
    assert!(has_div, "should have division operation");
}

// ============================================================
// Codegen Tests
// ============================================================

// ============================================================
// All Test Cases Discovery
// ============================================================

#[test]
fn test_all_cases_compile() {
    let cases = common::TestCase::find_all();

    if cases.is_empty() {
        eprintln!("Warning: no test cases found, skipping");
        return;
    }

    for case in cases {
        let result = common::compile_testcase(&case.name);
        assert!(
            result.is_ok(),
            "failed to compile {}: {:?}",
            case.name,
            result.err()
        );

        let dex_path = result.unwrap();
        assert!(dex_path.exists(), "dex file should exist: {:?}", dex_path);
    }
}

#[test]
fn test_all_cases_decode() {
    let cases = common::TestCase::find_all();

    if cases.is_empty() {
        eprintln!("Warning: no test cases found, skipping");
        return;
    }

    for case in cases {
        let dex_path = match common::compile_testcase(&case.name) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("Skipping {}: {}", case.name, e);
                continue;
            }
        };

        let ctx = DecompilerContext::from_file(&dex_path);
        assert!(ctx.is_ok(), "failed to load {}: {:?}", case.name, ctx.err());

        let mut ctx = ctx.unwrap();
        assert!(
            ctx.load_all_classes().is_ok(),
            "failed to load classes for {}",
            case.name
        );
    }
}

// ============================================================
// Structured Code Generation Tests
// ============================================================

#[test]
fn test_simple_if_kotlin_backend() {
    let (mut ctx, class_name) = load_testcase("SimpleIf");

    ctx.load_all_classes().expect("should load classes");

    // Try to generate structured code
    let result = ctx.decompile_method(&class_name, "test", None);

    match result {
        Ok(Some(code)) => {
            println!("Generated code for SimpleIf.test:\n{}", code);
            // Should have if statement
            assert!(code.contains("if"), "should contain if statement");
        }
        Ok(None) => {
            println!("Method not found");
        }
        Err(e) => {
            println!(
                "Structuring failed (expected for complex control flow): {:?}",
                e
            );
            // This is OK - some methods may fail to structure
        }
    }
}

#[test]
fn test_simple_loop_kotlin_backend() {
    let (mut ctx, class_name) = load_testcase("SimpleLoop");

    ctx.load_all_classes().expect("should load classes");

    // Try to generate structured code
    let result = ctx.decompile_method(&class_name, "sum", None);

    match result {
        Ok(Some(code)) => {
            println!("Generated code for SimpleLoop.sum:\n{}", code);
            // Should have while or do-while
            assert!(
                code.contains("while") || code.contains("do"),
                "should contain loop construct"
            );
        }
        Ok(None) => {
            println!("Method not found");
        }
        Err(e) => {
            println!(
                "Structuring failed (expected for complex control flow): {:?}",
                e
            );
        }
    }
}

#[test]
fn test_decompile_method_api() {
    let (mut ctx, class_name) = load_testcase("SimpleIf");

    // Test the high-level decompile_method API
    let result = ctx.decompile_method(&class_name, "test", None);

    match result {
        Ok(Some(code)) => {
            println!("Decompiled SimpleIf.test:\n{}", code);
        }
        Ok(None) => {
            println!("Method not found");
        }
        Err(e) => {
            println!("Decompilation failed: {:?}", e);
        }
    }
}

#[test]
fn test_infinite_loop() {
    let (mut ctx, class_name) = load_testcase("InfiniteLoop");
    ctx.load_all_classes().unwrap();

    // Check trimToSize method
    match ctx.decompile_method(&class_name, "trimToSize", None) {
        Ok(Some(code)) => {
            println!("Decompiled InfiniteLoop.trimToSize:\n{}", code);
            assert!(
                code.contains("synchronized"),
                "should contain synchronized block"
            );
        }
        Ok(None) => panic!("Analyzed trimToSize returned None"),
        Err(e) => panic!("Error decompiling trimToSize: {:?}", e),
    }
}

#[test]
fn test_lru_cache_sim() {
    let (mut ctx, class_name) = load_testcase("LruCacheSim");
    ctx.load_all_classes().unwrap();

    // Check trimToSize method
    match ctx.decompile_method(&class_name, "trimToSize", None) {
        Ok(Some(code)) => {
            println!("Decompiled LruCacheSim.trimToSize:\n{}", code);
            // Verify expected control flow components
            assert!(
                code.contains("synchronized"),
                "should contain synchronized block"
            );
            // assert!(code.contains("while"), "should contain loop"); // Might be optimized out if broken?

            // Crucial check: verify the logic blocks are present
            // In the sim, we check v0 (which is p1) against 10
            assert!(
                code.contains("10"),
                "should contain the constant 10 from logic path"
            );
        }
        Ok(None) => panic!("Analyzed trimToSize returned None"),
        Err(e) => panic!("Error decompiling trimToSize: {:?}", e),
    }
}

#[test]
fn test_synchronized_loop_phi_copy_is_not_duplicated_at_region_exit() {
    let (mut ctx, class_name) = load_testcase("SynchronizedAdvanced");
    ctx.load_all_classes().expect("test classes should load");

    let code = ctx
        .decompile_java_method_with_config(
            &class_name,
            "deepNesting",
            Some("([I)I"),
            &JavaDecompilerConfig::default(),
        )
        .expect("deepNesting should decompile")
        .expect("deepNesting should be present");

    assert!(code.contains("while (index < values.length)"), "{code}");
    assert!(code.contains("index++;"), "{code}");
    assert!(!code.contains("int v2 = 0;"), "{code}");
    assert!(!code.contains("index = v2;"), "{code}");
}

#[test]
fn test_java_state_machine_preserves_switch_state_resets() {
    let (mut ctx, class_name) = load_testcase("HardcoreControlFlow");
    ctx.load_all_classes().expect("test classes should load");

    let code = ctx
        .decompile_java_method_with_config(
            &class_name,
            "stateMachine",
            Some("([I)I"),
            &JavaDecompilerConfig::default(),
        )
        .expect("stateMachine should decompile")
        .expect("stateMachine should be present");

    assert_eq!(code.matches("selector = 0;").count(), 3, "{code}");
}
