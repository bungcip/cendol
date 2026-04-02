use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_alignas_on_vla_rejected() {
    // C11 6.7.5p2: An alignment specifier shall not be used in the declaration
    // of an object with a variably modified type.

    // 1. VLA in block scope
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int a[n];
        }
        "#,
        "alignment specifier cannot be used on an object with a variably modified type",
    );

    // 2. Pointer to VLA in block scope
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int (*p)[n];
        }
        "#,
        "alignment specifier cannot be used on an object with a variably modified type",
    );

    // 3. VLA of pointers to VLA (multi-level variably modified)
    run_fail_with_message(
        r#"
        void f(int n, int m) {
            _Alignas(16) int (*a[n])[m];
        }
        "#,
        "alignment specifier cannot be used on an object with a variably modified type",
    );
}

#[test]
fn test_alignas_on_regular_array_allowed() {
    // Regular arrays are not variably modified types.
    run_pass(
        r#"
        void f() {
            _Alignas(16) int a[10];
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}
