use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_named_void_parameter_prohibited() {
    // C11 6.7.6.3p10: "A parameter list consisting of a single parameter of type void
    // and no identifier is a special case. It specifies that the function has no parameters."
    // A named void parameter is therefore illegal.

    run_fail_with_diagnostic(
        r#"
        void f(void x);
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
        "incomplete type 'void'",
        2,
        16,
    );
}

#[test]
fn test_void_parameter_in_list_prohibited() {
    // C11 6.7.6.3p10: void as a parameter is ONLY allowed as the sole parameter, unnamed.
    run_fail_with_diagnostic(
        r#"
        void f(int a, void);
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
        "incomplete type 'void'",
        2,
        23,
    );
}

#[test]
fn test_incomplete_struct_parameter_prohibited() {
    // C11 6.7.6.3p4: parameters shall have complete object type (after adjustment).
    run_fail_with_diagnostic(
        r#"
        struct S;
        void f(struct S s) {}
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
        "incomplete type 'struct S'",
        3,
        16,
    );
}

#[test]
fn test_valid_parameter_declarations_accepted() {
    // 1. Special (void) case
    run_pass(
        r#"
        void f(void);
        int main() { f(); return 0; }
        void f(void) {}
        "#,
        CompilePhase::Mir,
    );

    // 2. Pointer to void
    run_pass(
        r#"
        void f(void *p);
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );

    // 3. Array (decays to complete pointer)
    run_pass(
        r#"
        void f(int a[]);
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}
