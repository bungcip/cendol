use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_binary_conversion_complex_cast() {
    run_pass(
        r#"
        void foo() {
            _Complex float a = 1.0;
            _Complex double b = 2.0;
            a + b;

            _Complex double c = 1.0;
            _Complex float d = 2.0;
            c + d; // check rhs conversion too
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}
