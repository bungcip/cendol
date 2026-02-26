use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_pass, run_pass_with_diagnostic_message};

#[test]
fn test_pointer_assignment_discards_const() {
    crate::tests::test_utils::run_pass_with_diagnostic(
        r#"
        int main() {
            const int *cp;
            int *p;
            p = cp;
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "discards qualifiers",
        5,
        13,
    );
}

#[test]
fn test_pointer_assignment_discards_volatile() {
    run_pass_with_diagnostic_message(
        r#"
        int main() {
            volatile int *vp;
            int *p;
            p = vp;
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "discards qualifiers",
    );
}

#[test]
fn test_void_pointer_assignment_discards_const() {
    run_pass_with_diagnostic_message(
        r#"
        int main() {
            const int *cp;
            void *vp;
            vp = cp;
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "discards qualifiers",
    );
}

#[test]
fn test_pointer_initializer_discards_const() {
    run_pass_with_diagnostic_message(
        r#"
        int main() {
            const int *cp;
            int *p = cp;
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "discards qualifiers",
    );
}

#[test]
fn test_function_argument_discards_const() {
    run_pass_with_diagnostic_message(
        r#"
        void f(int *p) {}
        int main() {
            const int *cp;
            f(cp);
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "discards qualifiers",
    );
}

#[test]
fn test_return_discards_const() {
    run_pass_with_diagnostic_message(
        r#"
        int *f(const int *cp) {
            return cp;
        }
        "#,
        CompilePhase::Mir,
        "discards qualifiers",
    );
}

#[test]
fn test_adding_qualifiers_is_ok() {
    // Adding const is allowed
    run_pass(
        r#"
        int main() {
            int *p;
            const int *cp;
            cp = p;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_pointer_comparison_ignores_qualifiers() {
    crate::tests::test_utils::run_pass(
        r#"
        int main() {
            int *p;
            const int *cp;
            return p == cp;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_pointer_subtraction_ignores_qualifiers() {
    crate::tests::test_utils::run_pass(
        r#"
        int main() {
            int *p;
            const int *cp;
            return p - cp;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_void_pointer_adding_qualifiers_is_ok() {
    run_pass(
        r#"
        int main() {
            int *p;
            const void *cvp;
            cvp = p;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
