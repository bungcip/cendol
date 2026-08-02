use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_gnu_local_label_duplicate() {
    let source = r#"
    int main() {
        __label__ my_label;
        __label__ my_label;
        return 0;
    }
    "#;
    run_fail_with_message(source, "duplicate label declaration 'my_label'");
}
