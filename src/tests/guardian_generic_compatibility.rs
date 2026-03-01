use crate::tests::test_utils::run_fail_with_message;

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
