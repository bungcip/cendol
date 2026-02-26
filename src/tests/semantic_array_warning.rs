use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_pass, run_pass_with_diagnostic_message};

#[test]
fn test_array_in_condition_warning() {
    let source = r#"
        int main() {
            int a[5];
            if (a) {
                return 0;
            }
            return 1;
        }
    "#;
    run_pass_with_diagnostic_message(
        source,
        CompilePhase::Mir,
        "address of array 'a' will always evaluate to 'true'",
    );
}

#[test]
fn test_function_in_condition_no_warning() {
    let source = r#"
        void f() {}
        int main() {
            if (f) {
                return 0;
            }
            return 1;
        }
    "#;
    // Functions should decay to pointers but no warning is required by the user request
    run_pass(source, CompilePhase::Mir);
}
