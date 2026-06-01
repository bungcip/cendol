use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_pointer_assignment_nested_qualifiers() {
    // C11 6.5.16.1p1 requires that operands for assignment are pointers to qualified or unqualified versions of compatible types.
    // For nested pointers, `int **` and `const int **` are not compatible types, and assignments between them
    // are strictly rejected as type mismatches, preventing implicit qualifier conversions.

    // 1. Assigning int** to const int**
    run_fail_with_message(
        r#"
        int main() {
            int **p = 0;
            const int **q = p;
            return 0;
        }
        "#,
        "type mismatch: expected const int**, found int**",
    );

    // 2. Assigning const int** to int**
    run_fail_with_message(
        r#"
        int main() {
            const int **q = 0;
            int **p = q;
            return 0;
        }
        "#,
        "type mismatch: expected int**, found const int**",
    );
}

#[test]
fn test_pointer_assignment_top_level_qualifiers() {
    // Top-level pointer qualifier conversions are permitted with a warning.
    // (A warning is standard behavior for implicit discarding of qualifiers).
    // Here we ensure it doesn't fail with a hard "type mismatch" error.
    run_pass(
        r#"
        int main() {
            int *p = 0;
            const int *q = p;
            p = (int*)q; // cast to avoid warning on exact match if we were strictly testing pass
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
