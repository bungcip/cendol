use crate::tests::semantic_common::{setup_diagnostics_output, setup_mir};

#[test]
fn test_atomic_load_store() {
    let source = r#"
        void test(int *ptr, int val) {
            int ret;
            ret = __atomic_load_n(ptr, 0);
            __atomic_store_n(ptr, val, 0);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_atomic_exchange() {
    let source = r#"
        void test(int *ptr, int val) {
            int ret;
            ret = __atomic_exchange_n(ptr, val, 0);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_atomic_compare_exchange() {
    let source = r#"
        void test(int *ptr, int expected, int desired) {
            _Bool success;
            success = __atomic_compare_exchange_n(ptr, &expected, desired, 0, 0, 0);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_atomic_fetch_ops() {
    let source = r#"
        void test(int *ptr, int val) {
            int ret;
            ret = __atomic_fetch_add(ptr, val, 0);
            ret = __atomic_fetch_sub(ptr, val, 0);
            ret = __atomic_fetch_and(ptr, val, 0);
            ret = __atomic_fetch_or(ptr, val, 0);
            ret = __atomic_fetch_xor(ptr, val, 0);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_atomic_invalid_memorder_type() {
    let source = r#"
        void test(int *ptr) {
            __atomic_load_n(ptr, "invalid");
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_atomic_invalid_pointer_type() {
    let source = r#"
        void test(int val) {
            __atomic_load_n(val, 0);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_atomic_invalid_float_bitwise() {
    let source = r#"
        void test(float *ptr, float val) {
            __atomic_fetch_and(ptr, val, 0);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
