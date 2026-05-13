use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_typedef_redefinition_different_type() {
    // C11 6.7p3: "If an identifier has no linkage, there shall be no more than one declaration of the identifier (in a declarator or type specifier) with the same scope and in the same name space, except for tags..."
    // "typedef redefinition in the same scope must denote the SAME type."
    run_fail_with_message(
        r#"
        typedef int arr[10];
        typedef int arr[];
        "#,
        "redefinition of 'arr' with a different type",
    );
}

#[test]
fn test_typedef_redefinition_qualifiers() {
    // int and const int are compatible types in some contexts, but they are not the SAME type.
    run_fail_with_message(
        r#"
        typedef int T;
        typedef const int T;
        "#,
        "redefinition of 'T' with a different type",
    );
}

#[test]
fn test_typedef_redefinition_atomic() {
    run_fail_with_message(
        r#"
        typedef int T;
        typedef _Atomic int T;
        "#,
        "redefinition of 'T' with a different type",
    );
}

#[test]
fn test_typedef_redefinition_same_type_allowed() {
    run_pass(
        r#"
        typedef const int T;
        typedef const int T;
        int main() { return 0; }
        "#,
        CompilePhase::SemanticLowering,
    );
}
