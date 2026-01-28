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
fn test_atomic_compare_exchange_loop() {
    let source = r#"
        #include <stdbool.h>

        bool atomic_cas(int *ptr, int old, int new_val) {
            return __atomic_compare_exchange_n(ptr, &old, new_val, false, 5, 5);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
