use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_array_of_functions_rejected() {
    // C11 6.7.6.2p1: An array type describes a contiguously allocated nonempty set of
    // objects with a particular member object type, called the element type.
    // Functions are not objects, so an array of functions is invalid.
    run_fail_with_message(
        r#"
        typedef int func();
        func arr[10];
        "#,
        "declaration of array of functions is invalid",
    );
}

#[test]
fn test_array_of_function_pointers_accepted() {
    run_pass(
        r#"
        typedef int func();
        func *arr[10];
        int main() { return 0; }
        "#,
        CompilePhase::SemanticLowering,
    );
}
