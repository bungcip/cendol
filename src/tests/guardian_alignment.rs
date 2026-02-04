use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_fail_with_message;

#[test]
fn test_alignas_constraints() {
    // C11 6.7.5p3: An alignment specifier shall not be used in a typedef declaration,
    // or in the declaration of a function or a bit-field, or in the declaration
    // of a function parameter, or an object with storage-class specifier register.

    // 1. Typedef
    run_fail_with_message(
        "typedef _Alignas(16) int aligned_int;",
        CompilePhase::SemanticLowering,
        "alignment specifier cannot be used in a typedef",
    );

    // 2. Function
    run_fail_with_message(
        "_Alignas(16) void f(void);",
        CompilePhase::SemanticLowering,
        "alignment specifier cannot be used in a function",
    );

    // 3. Bit-field
    run_fail_with_message(
        "struct S { _Alignas(16) int x : 1; };",
        CompilePhase::SemanticLowering,
        "alignment specifier cannot be used in a bit-field",
    );

    // 4. Function parameter
    run_fail_with_message(
        "void f(_Alignas(8) int x) {}",
        CompilePhase::SemanticLowering,
        "alignment specifier cannot be used in a function parameter",
    );

    // 5. Register object
    run_fail_with_message(
        "void f() { register _Alignas(8) int x; }",
        CompilePhase::SemanticLowering,
        "alignment specifier cannot be used in a register object",
    );

    // C11 6.7.5p4: alignment must be at least as strict as natural alignment
    run_fail_with_message(
        "_Alignas(1) int x;",
        CompilePhase::SemanticLowering,
        "alignment specifier specifies 1-byte alignment, but 4-byte alignment is required",
    );
}
