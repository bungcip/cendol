use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_union_cast_extension() {
    let source = r#"
        typedef union { int x; } t;
        void test(int n) {
            ((t)n);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_union_cast_invalid_type_rejected() {
    let source = r#"
        typedef union { float x; } t;
        void test(int n) {
            ((t)n);
        }
    "#;
    run_fail_with_message(source, "expected scalar type");
}
