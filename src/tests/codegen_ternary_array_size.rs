use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_ternary_array_size() {
    let code = r#"
int main() {
    // This array size calculation relies on constant folding of the ternary operator.
    // If it fails, it might be treated as a VLA of size 0 or cause a crash.
    int a[1 ? 1 : 10];

    a[0] = 42;
    return a[0];
}
"#;
    let output = run_c_code_exit_status(code);
    assert_eq!(output, 42);
}
