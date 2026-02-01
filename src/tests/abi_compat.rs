use crate::tests::semantic_common::setup_cranelift;

#[test]
fn test_hfa_packing() {
    let source = r#"
        struct HFA { float a, b; };
        void take_hfa(struct HFA h) {}
    "#;
    let clif_dump = setup_cranelift(source);

    // Should be packed into I64 (1 register for 8 bytes)
    assert!(
        clif_dump.contains("function u0:0(i64)"),
        "Expected HFA to be packed into i64. Dump:\n{}",
        clif_dump
    );

    // Check that we unpack it (implied by stack store of parts)
    // The lowered code should look like storing the i64 to stack
    // or unpacking if we implemented partial store logic.
    // In our implementation we do partial store or full store depending on size.
    // 8 bytes is full store.
    assert!(
        clif_dump.contains("stack_store") || clif_dump.contains("store"),
        "Expected stack store for HFA param. Dump:\n{}",
        clif_dump
    );
}

#[test]
fn test_fixed_struct_param() {
    let source = r#"
        struct S { char x[1]; };
        void foo(struct S s) {
        }
    "#;
    let clif_dump = setup_cranelift(source);

    // 1 byte struct should be packed into i64
    assert!(
        clif_dump.contains("function u0:0(i64)"),
        "Expected small struct to be packed into i64. Dump:\n{}",
        clif_dump
    );

    // Should be unpacked using shifts/reductions because it is < 8 bytes (1 byte)
    // The generic packing logic generates partial stores for < 8 bytes
    assert!(
        clif_dump.contains("ushr") || clif_dump.contains("ireduce"),
        "Expected unpacking logic (shift/reduce) for small struct. Dump:\n{}",
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
