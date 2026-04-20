use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_parameter_top_level_qualifiers_ignored_for_compatibility() {
    // C11 6.7.6.3p15: "In determining the compatibility of two function types...
    // (each parameter declaration is adjusted as specified in 6.7.6.3 to have a
    // qualified version of an object pointer type, and) any top-level qualifiers
    // of its type are ignored for the purpose of determining compatibility."

    // 1. Plain vs Const parameter
    run_pass(
        r#"
        void f(int x);
        void f(const int x);
        void f(int x) {}

        int main() {
            f(0);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );

    // 2. Pointer vs Const Pointer (top-level const on the pointer itself)
    run_pass(
        r#"
        void g(int *p);
        void g(int * const p);
        void g(int *p) {}

        int main() {
            g(0);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_adjusted_array_parameter_qualifiers_ignored() {
    // C11 6.7.6.3p7: "A declaration of a parameter as 'array of type' shall
    // be adjusted to 'qualified pointer to type', where the type qualifiers
    // (if any) are those specified within the [ and ] of the array type derivation."
    // Combined with 6.7.6.3p15, these qualifiers are ignored for compatibility.

    run_pass(
        r#"
        void h(int *p);
        void h(int a[const]);
        void h(int a[static const 10]);
        void h(int *p) {}

        int main() {
            h(0);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_rejects_compatible_function_pointers_due_to_parameter_qualifiers() {
    // _Generic prohibits compatible types in associations.
    // void(*)(int) and void(*)(const int) are compatible.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic((void(*)(int))0,
                void(*)(int): 1,
                void(*)(const int): 2
            );
        }
        "#,
        "compatible with previously specified type",
    );

    // void(*)(int *) and void(*)(int * const) are compatible.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic((void(*)(int *))0,
                void(*)(int *): 1,
                void(*)(int * const): 2
            );
        }
        "#,
        "compatible with previously specified type",
    );
}

#[test]
fn test_parameter_pointed_to_qualifiers_not_ignored() {
    // Qualifiers on the pointed-to type are NOT top-level qualifiers of the parameter.
    // Thus int* and const int* are NOT compatible.

    run_fail_with_message(
        r#"
        void f(int *p);
        void f(const int *p);
        "#,
        "conflicting types for 'f'",
    );

    run_pass(
        r#"
        int main() {
            // Should match void(*)(int *) specifically, NOT const int *
            return _Generic((void(*)(int *))0,
                void(*)(int *): 1,
                void(*)(const int *): 2
            );
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_multi_dimensional_array_parameter_adjustment() {
    // Only the outermost array is adjusted to a pointer.
    // void f(int a[const 10][20]) -> void f(int (* const a)[20])
    // This is compatible with void f(int (*a)[20])

    run_pass(
        r#"
        void f(int (*a)[20]);
        void f(int a[const 10][20]);
        void f(int (*a)[20]) {}

        int main() {
            int arr[10][20];
            f(arr);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
