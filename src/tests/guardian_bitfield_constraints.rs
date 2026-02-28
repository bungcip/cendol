use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_bitfield_atomic_prohibited() {
    // C11 6.7.2.4p4: A bit-field shall not have an atomic type.

    // 1. Named bit-field with _Atomic specifier
    run_fail_with_message(
        "struct S { _Atomic(int) x : 1; };",
        "bit-field shall not have an atomic type",
    );

    // 2. Unnamed bit-field with _Atomic specifier
    run_fail_with_message(
        "struct S { _Atomic(int) : 1; };",
        "bit-field shall not have an atomic type",
    );

    // 3. Named bit-field with _Atomic qualifier
    run_fail_with_message(
        "struct S { _Atomic int x : 1; };",
        "bit-field shall not have an atomic type",
    );

    // 4. Via typedef
    run_fail_with_message(
        "typedef _Atomic int atomic_int; struct S { atomic_int x : 1; };",
        "bit-field shall not have an atomic type",
    );
}

#[test]
fn test_bitfield_invalid_types() {
    // C11 6.7.2.1p5: A bit-field shall have a type that is a qualified or unqualified version of
    // _Bool, signed int, unsigned int, or some other implementation-defined addressable storage unit.

    // 1. Float bit-field
    run_fail_with_message(
        "struct S { float x : 1; };",
        "bit-field type 'float' is invalid",
    );

    // 2. Double bit-field
    run_fail_with_message(
        "struct S { double x : 1; };",
        "bit-field type 'double' is invalid",
    );

    // 3. Pointer bit-field
    run_fail_with_message(
        "struct S { int *x : 1; };",
        "bit-field type 'int*' is invalid",
    );

    // 4. Void bit-field
    run_fail_with_message(
        "struct S { void x : 1; };",
        "bit-field type 'void' is invalid",
    );

    // 5. Array bit-field
    run_fail_with_message(
        "struct S { int x[10] : 1; };",
        "bit-field type 'int[10]' is invalid",
    );

    // 6. Function bit-field
    run_fail_with_message(
        "struct S { void f(void) : 1; };",
        "bit-field type 'void()' is invalid",
    );
}

#[test]
fn test_bitfield_width_constraints() {
    // C11 6.7.2.1p4: The expression that specifies the width of a bit-field shall be
    // an integer constant expression with a nonnegative value that does not exceed
    // the width of an object of the type that would be specified were the colon and
    // expression omitted.

    // 1. Negative width
    run_fail_with_message(
        "struct S { int x : -1; };",
        "invalid bit-field width",
    );

    // 2. Width exceeds type width (char is 8 bits in this compiler)
    run_fail_with_message(
        "struct S { char x : 9; };",
        "width of bit-field (9 bits) exceeds width of its type (8 bits)",
    );

    // 3. Named zero-width bit-field (C11 6.7.2.1p12)
    run_fail_with_message(
        "struct S { int x : 0; };",
        "zero-width bit-field shall not specify a declarator",
    );

    // Legal: unnamed zero-width bit-field
    run_pass("struct S { int : 0; };", CompilePhase::SemanticLowering);
}

#[test]
fn test_bitfield_valid_types() {
    // Legal bit-field types
    run_pass("struct S { _Bool x : 1; };", CompilePhase::SemanticLowering);
    run_pass("struct S { signed int x : 1; };", CompilePhase::SemanticLowering);
    run_pass("struct S { unsigned int x : 1; };", CompilePhase::SemanticLowering);
    run_pass("struct S { char x : 1; };", CompilePhase::SemanticLowering);
    run_pass("struct S { long x : 1; };", CompilePhase::SemanticLowering);
}
