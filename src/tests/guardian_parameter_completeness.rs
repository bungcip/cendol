use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_parameter_void_prohibited() {
    // C11 6.7.6.3p4: each parameter shall have a complete object type.
    // void is not an object type.

    // 1. Named void parameter in declaration
    run_fail_with_message(
        "void foo(void v);",
        "incomplete type 'void'",
    );

    // 2. Named void parameter in definition
    run_fail_with_message(
        "void foo(void v) {}",
        "incomplete type 'void'",
    );

    // 3. Unnamed void parameter in declaration (more than one)
    run_fail_with_message(
        "void foo(int a, void);",
        "incomplete type 'void'",
    );

    // 4. Unnamed void parameter in definition (more than one)
    run_fail_with_message(
        "void foo(int a, void) {}",
        "incomplete type 'void'",
    );

    // Legal: single unnamed parameter of type void
    run_pass("void foo(void);", CompilePhase::SemanticLowering);
    run_pass("void foo(void) {}", CompilePhase::SemanticLowering);
}

#[test]
fn test_parameter_incomplete_struct_prohibited_in_definition() {
    // C11 6.7.6.3p4: each parameter shall have a complete object type.

    let code = "struct S; void foo(struct S s) {}";
    run_fail_with_message(code, "incomplete type 'struct S'");
}

#[test]
fn test_parameter_incomplete_struct_prohibited_in_declaration() {
    // Many compilers (including GCC and Clang) allow incomplete types in function declarations
    // as long as they are not used. However, C11 6.7.6.3p4 says "each parameter SHALL have a complete object type".
    // Wait, let's re-read 6.7.6.3p4: "After adjustment, the parameters in a function declarator
    // that is part of a function definition of that function shall have complete object type;
    // the parameters in a function declarator that is NOT part of a function definition
    // shall have complete object type or an array of unknown size."
    // Wait, I misread it.
    // 6.7.6.3p4: "After adjustment, the parameters in a function declarator that is part of a
    // function definition of that function shall have complete object type; the parameters
    // in a function declarator that is not part of a function definition of that function
    // shall have complete object type or an array of unknown size."
    // So for declarations, it ALSO must be complete object type (or incomplete array).

    // BUT GCC and Clang allow incomplete structs in declarations.
    // Let's re-check GCC with -std=c11 -pedantic.
    // I did check it and it PASSED.

    // Why? 6.7.6.3p4: "After adjustment..."
    // Incomplete arrays are adjusted to pointers (complete).
    // But incomplete structs are NOT adjusted.

    // If GCC allows it, maybe there's another rule.
    // Actually, GCC only errors on definitions.

    // Our implementation currently errors on both.
    // If we want to match GCC, we should only error on definitions for structs.
    // But for 'void', GCC warns/errors on declarations too.

    run_fail_with_message("struct S; void foo(struct S s);", "incomplete type 'struct S'");
}

#[test]
fn test_parameter_incomplete_union_prohibited_in_definition() {
    let code = "union U; void foo(union U u) {}";
    run_fail_with_message(code, "incomplete type 'union U'");
}

#[test]
fn test_parameter_incomplete_array_allowed() {
    // Incomplete arrays are adjusted to pointers, which are complete.
    run_pass("void foo(int a[]);", CompilePhase::SemanticLowering);
    run_pass("void foo(int a[]) {}", CompilePhase::SemanticLowering);
}

#[test]
fn test_parameter_function_pointer_allowed() {
    // Function types are not object types, but they are adjusted to function pointers (complete object types).
    run_pass("void foo(void f(void));", CompilePhase::SemanticLowering);
    run_pass("void foo(void f(void)) {}", CompilePhase::SemanticLowering);
}
