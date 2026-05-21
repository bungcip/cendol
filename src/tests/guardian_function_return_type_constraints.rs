use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_function_returning_array_rejected() {
    // C11 6.7.6.3p1: A function declarator shall not specify a return type that is a function type or an array type.
    run_fail_with_message(
        r#"
        typedef int arr[10];
        arr f();
        "#,
        "function cannot return an array type",
    );
}

#[test]
fn test_function_returning_function_rejected() {
    // C11 6.7.6.3p1: A function declarator shall not specify a return type that is a function type or an array type.
    run_fail_with_message(
        r#"
        typedef int func();
        func f();
        "#,
        "function cannot return a function type",
    );
}

#[test]
fn test_function_returning_pointer_to_array_accepted() {
    run_pass(
        r#"
        typedef int arr[10];
        arr *f();
        int main() { return 0; }
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_function_returning_pointer_to_function_accepted() {
    run_pass(
        r#"
        typedef int func();
        func *f();
        int main() { return 0; }
        "#,
        CompilePhase::SemanticLowering,
    );
}
