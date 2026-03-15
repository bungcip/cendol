use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_relational_function_pointers_prohibited() {
    // C11 6.5.8p2: Relational operators require pointers to compatible object types.
    // Function pointers are NOT pointers to object types.
    run_fail_with_message(
        r#"
        void f(void);
        void g(void);
        int test() {
            return &f < &g;
        }
        "#,
        "Invalid operands for binary operation",
    );
}

#[test]
fn test_equality_function_pointers_allowed() {
    // C11 6.5.9p2: Equality operators allow pointers to compatible types (including function types).
    run_pass(
        r#"
        void f(void);
        void g(void);
        int test() {
            return &f == &g;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_relational_void_pointers_allowed() {
    // void is an incomplete object type, so void* is a pointer to an object type.
    run_pass(
        r#"
        int test(void *p, void *q) {
            return p < q;
        }
        "#,
        CompilePhase::Mir,
    );
}
