use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_pointer_assignment_nested_qualifiers_prohibited() {
    // C11 6.5.16.1p1: "...both operands are pointers to qualified or unqualified versions of
    // compatible types, and the type pointed to by the left has all the qualifiers of
    // the type pointed to by the right;"
    // For nested pointers, `int **` and `const int **` are NOT compatible types.
    // The type pointed to by the left is `const int *`. The type pointed to by the right is `int *`.
    // These are not qualified/unqualified versions of compatible types.
    run_fail_with_message(
        r#"
        int main() {
            int **p;
            const int **q;
            q = p; // Invalid!
        }
        "#,
        "type mismatch", // We expect a type mismatch, not just a discards qualifier warning
    );
}

#[test]
fn test_pointer_assignment_nested_qualifiers_multiple_levels() {
    run_fail_with_message(
        r#"
        int main() {
            int ***p;
            const int ***q;
            q = p; // Invalid!
        }
        "#,
        "type mismatch",
    );
}

#[test]
fn test_pointer_assignment_nested_qualifiers_valid() {
    // Left: pointer to const pointer to int
    // Right: pointer to pointer to int
    // Compatible: Yes. The type pointed to by left is `const pointer to int`.
    // The type pointed to by right is `pointer to int`.
    // They are qualified/unqualified versions of compatible types.
    run_pass(
        r#"
        int main() {
            int *p;
            int * const *q;
            q = &p; // Valid!
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
