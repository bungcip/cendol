use crate::tests::test_utils::*;

#[test]
fn test_incomplete_deref_statement_error() {
    let source = r#"
        typedef struct _x x;
        void test(x *p) {
            *p;
        }
    "#;
    run_fail_with_message(source, "incomplete type 'struct _x'");
}
