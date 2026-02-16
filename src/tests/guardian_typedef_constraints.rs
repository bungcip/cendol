use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_typedef_redefinition_same_type() {
    run_pass(
        r#"
        typedef int T;
        typedef int T;
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_typedef_redefinition_different_type() {
    run_fail_with_message(
        r#"
        typedef int T;
        typedef float T;
        "#,
        CompilePhase::SemanticLowering,
        "redefinition of 'T' with a different type",
    );
}

#[test]
fn test_typedef_redefinition_compatible_but_not_same() {
    // int[] and int[10] are compatible but NOT the same type.
    // C11 6.7p3 requires same type for typedef redefinition.
    run_fail_with_message(
        r#"
        typedef int A[];
        typedef int A[10];
        "#,
        CompilePhase::SemanticLowering,
        "redefinition of 'A' with a different type",
    );
}

#[test]
fn test_typedef_redefinition_defines_new_struct() {
    // C11 6.7p3: provided that no specifier of the type name is a type specifier
    // that defines a new structure...
    // Even if the members are the same, they are different anonymous struct types.
    run_fail_with_message(
        r#"
        typedef struct { int x; } S;
        typedef struct { int x; } S;
        "#,
        CompilePhase::SemanticLowering,
        "redefinition of 'S'",
    );
}

#[test]
fn test_typedef_redefinition_using_same_tag_ok() {
    run_pass(
        r#"
        struct s { int x; };
        typedef struct s S;
        typedef struct s S;
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_typedef_redefinition_function_params_ok() {
    // Parameter names don't matter for function type identity in Cendol
    run_pass(
        r#"
        typedef int (*F)(int a);
        typedef int (*F)(int b);
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_typedef_redefinition_function_params_different_type_rejects() {
    run_fail_with_message(
        r#"
        typedef int (*F)(int a);
        typedef int (*F)(float b);
        "#,
        CompilePhase::SemanticLowering,
        "redefinition of 'F' with a different type",
    );
}
