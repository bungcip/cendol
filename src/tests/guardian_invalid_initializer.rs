use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_extern_with_initializer_in_block_scope() {
    // C11 6.7.9p5: If the declaration of an identifier has block scope, and the identifier has external or
    // internal linkage, the declaration shall have no initializer for the identifier.
    run_fail_with_diagnostic(
        r#"
void f() {
    extern int x = 1;
}
        "#,
        CompilePhase::Mir,
        "invalid initializer",
        3,
        5,
    );
}
