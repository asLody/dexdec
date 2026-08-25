//! Documents the in-memory cost of the core IR node types; guards against
//! silent growth of the hot per-instruction footprint.
use dexdec::ir::insn::FillArrayData;
use dexdec::ir::{
    ArgType, BoolExpr, InsnArg, InsnNode, InsnPayload, MemberReference, MethodReference,
    RegisterArg, Utf16String, CFG,
};

#[test]
fn report_core_ir_sizes() {
    eprintln!(
        "sizeof InsnNode        = {}",
        std::mem::size_of::<InsnNode>()
    );
    eprintln!(
        "sizeof InsnPayload     = {}",
        std::mem::size_of::<InsnPayload>()
    );
    eprintln!(
        "sizeof MemberReference = {}",
        std::mem::size_of::<MemberReference>()
    );
    eprintln!(
        "sizeof MethodReference = {}",
        std::mem::size_of::<MethodReference>()
    );
    eprintln!(
        "sizeof ArgType         = {}",
        std::mem::size_of::<ArgType>()
    );
    eprintln!(
        "sizeof Utf16String     = {}",
        std::mem::size_of::<Utf16String>()
    );
    eprintln!(
        "sizeof BoolExpr        = {}",
        std::mem::size_of::<BoolExpr>()
    );
    eprintln!(
        "sizeof FillArrayData   = {}",
        std::mem::size_of::<FillArrayData>()
    );
    eprintln!(
        "sizeof InsnArg         = {}",
        std::mem::size_of::<InsnArg>()
    );
    eprintln!(
        "sizeof RegisterArg     = {}",
        std::mem::size_of::<RegisterArg>()
    );
    eprintln!("sizeof CFG             = {}", std::mem::size_of::<CFG>());

    // Regression guard: the rare/heavy payload fields (reference, string_value,
    // class_type, switch_cases, cast_type, fill_array_data, compound_target) are
    // boxed precisely so the hot per-instruction footprint stays small. Every
    // decoded archive holds millions of payloads, so even +8 bytes here is a
    // real memory win handed back. Raise these bounds only alongside a
    // documented memory-profile win.
    assert!(
        std::mem::size_of::<InsnPayload>() <= 184,
        "InsnPayload grew to {} bytes; payload fields are boxed to keep it small",
        std::mem::size_of::<InsnPayload>()
    );
    assert!(
        std::mem::size_of::<InsnNode>() <= 280,
        "InsnNode grew to {} bytes; payload fields are boxed to keep it small",
        std::mem::size_of::<InsnNode>()
    );
}
