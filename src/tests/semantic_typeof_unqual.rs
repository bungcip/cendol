use super::test_utils::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_typeof_unqual_type_compile() {
    run_pass(
        r#"
        int main() {
            const int x = 5;
            typeof_unqual(x) y = 5;
            y = 10; // should be allowed because typeof_unqual drops const
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_typeof_unqual_expr_compile() {
    run_pass(
        r#"
        int main() {
            const int x = 5;
            typeof_unqual(x + 1) y = 5;
            y = 10;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_typeof_unqual_pointer() {
    run_pass(
        r#"
        int main() {
            int const * p = 0;
            // typeof_unqual(p) is `int const *`, because the top-level pointer is unqualified.
            // But wait, typeof_unqual strips top-level qualifiers.
            // If p is `const int *`, it's a pointer to const int.
            // The pointer itself is unqualified. typeof_unqual(p) == `const int *`.
            typeof_unqual(p) y = 0;

            int * const p2 = 0;
            // p2 is `int * const`. typeof_unqual(p2) should be `int *`.
            typeof_unqual(p2) y2 = 0;
            y2 = p; // this is just testing assignment
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
