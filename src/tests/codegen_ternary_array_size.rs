use crate::tests::codegen_common::run_c_code_with_output;

#[test]
fn test_ternary_array_size() {
    let code = r#"
int printf(const char *fmt, ...);

int main() {
    // This array size calculation relies on constant folding of the ternary operator.
    // If it fails, it might be treated as a VLA of size 0 or cause a crash.
    int a[1 ? 1 : 10];

    a[0] = 42;
    printf("%d\n", a[0]);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "42");
}
