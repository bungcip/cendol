use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_incomplete_array_prohibited() {
    // C11 6.5.1.1p2: The controlling expression shall be an expression of a complete object type, or the void type.
    // An incomplete array is NOT a complete object type.
    run_fail_with_message(
        r#"
        extern int a[];
        int main() {
            return _Generic(a, int*: 1);
        }
        "#,
        "controlling expression type 'int[]' is an incomplete type",
    );
}

#[test]
fn test_generic_function_prohibited() {
    // C11 6.5.1.1p2: The controlling expression shall be an expression of a complete object type, or the void type.
    // A function type is NOT an object type.
    run_fail_with_message(
        r#"
        void f(void);
        int main() {
            return _Generic(f, void(*)(void): 1);
        }
        "#,
        "controlling expression type 'void()' is an incomplete type",
    );
}

#[test]
fn test_generic_incomplete_struct_prohibited() {
    // C11 6.5.1.1p2: The controlling expression shall be an expression of a complete object type, or the void type.
    run_fail_with_message(
        r#"
        struct S;
        extern struct S s;
        int main() {
            return _Generic(s, default: 1);
        }
        "#,
        "controlling expression type 'struct S' is an incomplete type",
    );
}

#[test]
fn test_generic_void_allowed() {
    // C11 6.5.1.1p2 explicitly allows the void type for the controlling expression.
    run_pass(
        r#"
        int main() {
            return _Generic((void)0, default: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_complete_object_types_allowed() {
    run_pass(
        r#"
        struct S { int x; };
        int main() {
            int i;
            struct S s;
            int a[10];
            _Generic(i, int: 1);
            _Generic(s, struct S: 1);
            _Generic(a, int*: 1);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
