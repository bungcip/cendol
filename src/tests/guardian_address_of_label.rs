use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn rejects_address_of_label() {
    let src = "int main() {\n    void *ptr;\nlabel:\n    ptr = &label;\n    return 0;\n}";
    // C11 6.5.3.2p1: The operand of the unary & operator shall be either a function designator,
    // the result of a [] or unary * operator, or an lvalue that designates an object...
    // A label is none of these.
    // In this compiler, 'label' in an expression will fail to resolve in the ordinary namespace.
    // Line 4: "    ptr = &label;"
    // Column:  123456789012
    // label starts at column 12.
    run_fail_with_diagnostic(src, CompilePhase::Mir, "Undeclared identifier 'label'", 4, 12);
}
