use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_alignas_vla_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not be used in a declaration
    // of an object with a variably modified type.

    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int a[n];
        }
        "#,
        "alignment specifier cannot be used on an object with a variably modified type",
    );
}

#[test]
fn test_alignas_pointer_to_vla_prohibited() {
    // Pointer to VLA is also a variably modified type.
    run_fail_with_message(
        r#"
        void f(int n) {
            _Alignas(16) int (*p)[n];
        }
        "#,
        "alignment specifier cannot be used on an object with a variably modified type",
    );
}

#[test]
fn test_alignas_normal_array_allowed() {
    // Normal arrays (not VM) are allowed.
    run_pass(
        r#"
        void f(void) {
            _Alignas(16) int a[10];
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}
