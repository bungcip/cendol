use crate::tests::semantic_common::setup_cranelift;

#[test]
fn test_fixed_struct_param() {
    let source = r#"
        struct S { char x[1]; };
        void foo(struct S s) {
        }
    "#;
    let clif_dump = setup_cranelift(source);

    // We expect a call to memcpy (or similar) to copy the struct from the pointer param
    // to the local stack slot.
    assert!(
        clif_dump.contains("call"),
        "Expected memcpy call for struct parameter copy. Dump:\n{}",
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

    // For va_arg with aggregate, we expect:
    // 1. Calculation of address
    // 2. No load of the value from that address (in the register path)
    // 3. A memcpy call to copy from that address to the destination

    assert!(
        clif_dump.contains("call"),
        "Expected memcpy call for va_arg aggregate assignment. Dump:\n{}",
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
