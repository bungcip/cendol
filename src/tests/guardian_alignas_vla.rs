use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_alignas_vla_prohibited() {
    // C11 6.7.5p2: An alignment specifier shall not be used in the declaration
    // of an object whose type is a variably modified type.
    run_fail_with_diagnostic(
        r#"
        void f(int n) {
            _Alignas(16) int vla[n];
        }
        "#,
        CompilePhase::Mir,
        "alignment specifier cannot be used in a variably modified type",
        3,
        13,
    );
}

#[test]
fn test_alignas_pointer_to_vla_prohibited() {
    // Pointers to VLAs are also variably modified types.
    run_fail_with_diagnostic(
        r#"
        void f(int n) {
            _Alignas(16) int (*ptr)[n];
        }
        "#,
        CompilePhase::Mir,
        "alignment specifier cannot be used in a variably modified type",
        3,
        13,
    );
}
