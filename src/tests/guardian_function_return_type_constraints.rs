use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_function_returning_array_rejected() {
    // C11 6.7.6.3p1: A function declarator shall not specify a return type that is a function type or an array type.
    run_fail_with_diagnostic(
        r#"
        typedef int arr[10];
        arr f();
        "#,
        CompilePhase::SemanticLowering,
        "function cannot return an array type",
        3,
        15,
    );
}

#[test]
fn test_function_returning_function_rejected() {
    // C11 6.7.6.3p1: A function declarator shall not specify a return type that is a function type or an array type.
    run_fail_with_diagnostic(
        r#"
        typedef int func();
        func f();
        "#,
        CompilePhase::SemanticLowering,
        "function cannot return a function type",
        3,
        16,
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

#[test]
fn test_function_returning_multidimensional_array_rejected() {
    run_fail_with_diagnostic(
        r#"
        typedef int arr[10][20];
        arr f();
        "#,
        CompilePhase::SemanticLowering,
        "function cannot return an array type",
        3,
        15,
    );
}
