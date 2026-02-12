use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_alignof_function_prohibited() {
    // C11 6.5.3.4p1: The _Alignof operator shall not be applied to a function type.
    run_fail_with_message(
        r#"
        void f(void);
        int main() {
            return _Alignof(void(void));
        }
        "#,
        CompilePhase::Mir,
        "Invalid application of '_Alignof' to a function type",
    );
}

#[test]
fn test_sizeof_function_type_prohibited() {
    // C11 6.5.3.4p1: The sizeof operator shall not be applied to a function type.
    run_fail_with_message(
        r#"
        int main() {
            return sizeof(void(void));
        }
        "#,
        CompilePhase::Mir,
        "Invalid application of 'sizeof' to a function type",
    );
}

#[test]
fn test_alignof_incomplete_type_prohibited() {
    // C11 6.5.3.4p1: The _Alignof operator shall not be applied to an incomplete type.
    run_fail_with_message(
        r#"
        struct S;
        int main() {
            return _Alignof(struct S);
        }
        "#,
        CompilePhase::Mir,
        "Invalid application of '_Alignof' to an incomplete type",
    );
}

#[test]
fn test_sizeof_incomplete_type_prohibited() {
    // C11 6.5.3.4p1: The sizeof operator shall not be applied to an incomplete type.
    run_fail_with_message(
        r#"
        struct S;
        int main() {
            return sizeof(struct S);
        }
        "#,
        CompilePhase::Mir,
        "Invalid application of 'sizeof' to an incomplete type",
    );
}
