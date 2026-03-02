use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_selection_rejects_compatible_array_types() {
    run_fail_with_message(
        r#"
        int main() {
            int a[10];
            return _Generic(&a, int(*)[10]: 1, int(*)[]: 2);
        }
        "#,
        "compatible with previously specified type",
    );
}

#[test]
fn test_generic_selection_rejects_compatible_enum_type() {
    run_fail_with_message(
        r#"
        enum E { A = -1 };
        int main() {
            // enum E is compatible with 'int' because it has a negative value
            return _Generic(0, int: 1, enum E: 2);
        }
        "#,
        "compatible with previously specified type",
    );

    run_fail_with_message(
        r#"
        enum E { A };
        int main() {
            // enum E is compatible with 'unsigned int' by default in this compiler
            return _Generic(0u, unsigned int: 1, enum E: 2);
        }
        "#,
        "compatible with previously specified type",
    );
}

#[test]
fn test_generic_selection_rejects_compatible_function_pointers() {
    // Parameter names don't affect compatibility
    run_fail_with_message(
        r#"
        int main() {
            return _Generic((void(*)(int))0, void(*)(int x): 1, void(*)(int y): 2);
        }
        "#,
        "compatible with previously specified type",
    );
}

#[test]
fn test_generic_selection_qualifier_compatibility_constraints() {
    // C11 6.5.1.1p2: "No two generic associations in the same generic selection
    // shall specify compatible types."

    // 1. int and const int are NOT compatible types and can both be present.
    run_pass(
        r#"
        int main() {
            return _Generic(0, int: 1, const int: 2);
        }
        "#,
        CompilePhase::Mir,
    );

    // 2. Exact same types are compatible and must be rejected.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, int: 1, int: 2);
        }
        "#,
        "compatible with previously specified type 'int'",
    );
}
