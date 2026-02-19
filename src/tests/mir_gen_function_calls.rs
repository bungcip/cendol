use super::semantic_common::setup_mir;

#[test]
fn test_call_int_cast_to_fn_ptr() {
    let source = r#"
        void test() {
            ((void (*)(void))0)();
        }
    "#;

    // This should not panic
    let mir_dump = setup_mir(source);

    // We expect an indirect call to an integer constant
    // The exact specific output might vary, but we look for the key elements.
    // Ideally we'd use a snapshot but creating one from scratch without running is hard.
    // For now, just ensure it runs (setup_mir panics on failure) and check for indirect call pattern.

    // A casted constant call should look like:
    // call cast<ptr<fn() -> void>>(0)()
    // or
    // %0 = cast<ptr<fn() -> void>>(0)
    // call %0()

    // Based on mir_gen_expression.rs:
    // CallTarget::Indirect(Operand::Constant(const_id)) is generated.
    // The dumper typically dumps indirect calls as `call <operand>(...)`

    // Temporarily trigger failure with diff to see output
    // Verify indirect call to constant 0 is generated
    // Output format seen: "call *const 0()"
    assert!(mir_dump.contains("call *const 0()"), "MIR Dump:\n{}", mir_dump);
}
