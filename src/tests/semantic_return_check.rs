use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_return_struct_in_int_function() {
    let code = r#"
    typedef struct {
    } S;

    int main() {
        S s;
        return s;
    }
    "#;
    run_fail_with_message(code, "type mismatch: expected int, found struct (anonymous)");
}

#[test]
fn test_return_missing_value() {
    let code = r#"
    int foo() {
        return;
    }
    "#;
    run_fail_with_message(code, "non-void function 'foo' should return a value");
}
