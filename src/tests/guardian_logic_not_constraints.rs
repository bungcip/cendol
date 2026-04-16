use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_logic_not_on_struct_prohibited() {
    // C11 6.5.3.3p1: The operand of the unary ! operator shall have scalar type.
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            struct S s = {0};
            return !s;
        }
        "#,
        "expected scalar type",
    );
}

#[test]
fn test_logic_not_on_union_prohibited() {
    run_fail_with_message(
        r#"
        union U { int x; };
        int main() {
            union U u = {0};
            return !u;
        }
        "#,
        "expected scalar type",
    );
}

#[test]
fn test_logic_not_on_array_allowed() {
    // Array decays to pointer, which is scalar.
    run_pass(
        r#"
        int main() {
            int a[10];
            return !a;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_logic_not_on_function_allowed() {
    // Function decays to pointer, which is scalar.
    run_pass(
        r#"
        void f() {}
        int main() {
            return !f;
        }
        "#,
        CompilePhase::Mir,
    );
}
