use crate::tests::semantic_common::setup_cranelift;

#[test]
fn test_fixed_struct_param() {
    let source = r#"
        struct S { char x[1]; };
        void foo(struct S s) {
        }
    "#;
    let clif_dump = setup_cranelift(source);

    // Optimized: Small structs (1 byte) are passed in register (i8) and stored to stack.
    // We expect NO memcpy call.
    assert!(
        !clif_dump.contains("call"),
        "Expected optimized register passing (no memcpy) for small struct. Dump:\n{}",
        clif_dump
    );
    assert!(
        clif_dump.contains("store"),
        "Expected store instruction for struct parameter. Dump:\n{}",
        clif_dump
    );
}

#[test]
fn test_variadic_struct_arg() {
    let source = r#"
        #include <stdarg.h>
        struct S { char x[1]; };
        void foo(int n, ...) {
            va_list ap;
            va_start(ap, n);
            struct S s = va_arg(ap, struct S);
        }
    "#;
    let clif_dump = setup_cranelift(source);

    // Optimized: va_arg for small struct loads value directly from spill area (or register save area).
    // We expect NO memcpy call for assignment.
    assert!(
        !clif_dump.contains("call memcpy"),
        "Expected no memcpy call for va_arg small struct assignment. Dump:\n{}",
        clif_dump
    );
    assert!(
        clif_dump.contains("load"),
        "Expected load instruction for va_arg. Dump:\n{}",
        clif_dump
    );
}

#[test]
fn test_partial_load_struct_arg() {
    let source = r#"
        struct S { char x[1]; };
        void variadic(int n, ...);
        void caller() {
            struct S s = {0};
            variadic(1, s);
        }
    "#;
    let clif_dump = setup_cranelift(source);

    // In caller(), passing `s` to variadic function involves loading it.
    // Since `s` is 1 byte, we should see partial loading logic (load.i8)
    // instead of load.i64.

    assert!(
        clif_dump.contains("load.i8"),
        "Expected partial load (load.i8) for 1-byte struct argument to variadic function. Dump:\n{}",
        clif_dump
    );
}

#[test]
fn test_hfa_passing() {
    let source = r#"
        struct HFA { float a; float b; };
        void foo(struct HFA h) {}
    "#;
    let clif_dump = setup_cranelift(source);

    // HFA (2 floats, 8 bytes) should be passed as F64 (XMM) to align with ABI expectations
    // and avoid GPR corruption issues.
    assert!(
        clif_dump.contains("f64"),
        "Expected HFA to be passed as f64. Dump:\n{}",
        clif_dump
    );
}
