use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::run_pass;

#[test]
fn test_array_with_large_zero_init() {
    // this must be fast
    let source = r#"
        int bigarray[2147483647];
        int main() { return 0; }
    "#;
    run_pass(source, CompilePhase::EmitObject);
}

#[test]
fn test_array_size_in_tenary() {
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
