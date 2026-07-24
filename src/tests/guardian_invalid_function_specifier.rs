use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_fail_with_message};

#[test]
fn test_inline_on_variable() {
    run_fail_with_diagnostic(
        "inline int x;",
        CompilePhase::SemanticLowering,
        "'inline' function specifier appears on non-function declaration",
        1,
        1,
    );
}

#[test]
fn test_noreturn_on_variable() {
    run_fail_with_diagnostic(
        "_Noreturn int x;",
        CompilePhase::SemanticLowering,
        "'_Noreturn' function specifier appears on non-function declaration",
        1,
        1,
    );
}

#[test]
fn test_inline_on_typedef() {
    // A typedef defining a function type is still a typedef, not a function
    run_fail_with_message(
        "typedef inline void f(void);",
        "'inline' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_noreturn_on_function_pointer() {
    // A function pointer variable is not a function
    run_fail_with_diagnostic(
        "_Noreturn void (*f)(void);",
        CompilePhase::SemanticLowering,
        "'_Noreturn' function specifier appears on non-function declaration",
        1,
        1,
    );
}

#[test]
fn test_inline_on_struct_member() {
    // A struct member cannot have a function specifier
    run_fail_with_message(
        "struct S { inline int x; };",
        "'inline' function specifier appears on non-function declaration",
    );
}
