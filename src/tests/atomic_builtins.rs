use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_pass;

#[test]
fn test_atomic_builtins_compilation() {
    let source = r#"
        void test_atomic(int *ptr, int val, int *expected) {
            int ret;
            ret = __atomic_load_n(ptr, 0);
            __atomic_store_n(ptr, val, 0);
            ret = __atomic_exchange_n(ptr, val, 0);
            _Bool success = __atomic_compare_exchange_n(ptr, expected, val, 0, 0, 0);
            ret = __atomic_fetch_add(ptr, val, 0);
            ret = __atomic_fetch_sub(ptr, val, 0);
            ret = __atomic_fetch_and(ptr, val, 0);
            ret = __atomic_fetch_or(ptr, val, 0);
            ret = __atomic_fetch_xor(ptr, val, 0);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_atomic_semantic_errors() {
    use crate::tests::semantic_common::run_fail_with_diagnostic;

    // Invalid memory order type
    let source_memorder = r#"
        void test(int *ptr) {
            __atomic_load_n(ptr, "invalid");
        }
    "#;
    run_fail_with_diagnostic(
        source_memorder,
        CompilePhase::Mir,
        "invalid argument type for atomic builtin: char[8]",
        3,
        34,
    );

    // Invalid pointer type
    let source_ptr = r#"
        void test(int val) {
            __atomic_load_n(val, 0);
        }
    "#;
    run_fail_with_diagnostic(
        source_ptr,
        CompilePhase::Mir,
        "invalid argument type for atomic builtin: int",
        3,
        29,
    );

    // Invalid bitwise operation on float
    let source_bitwise = r#"
        void test(float *ptr, float val) {
            __atomic_fetch_and(ptr, val, 0);
        }
    "#;
    run_fail_with_diagnostic(
        source_bitwise,
        CompilePhase::Mir,
        "invalid argument type for atomic builtin: float",
        3,
        32,
    );
}

#[test]
fn test_atomic_compare_exchange_loop() {
    let source = r#"
        #include <stdbool.h>

        bool atomic_cas(int *ptr, int old, int new_val) {
            return __atomic_compare_exchange_n(ptr, &old, new_val, false, 5, 5);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
