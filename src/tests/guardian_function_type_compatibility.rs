use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_distinguishes_function_return_qualifiers() {
    // C11 6.7.6.3p15: "For two function types to be compatible, both shall specify compatible return types."
    // 'int' and 'const int' are NOT compatible types.
    // Therefore, 'int (*)(void)' and 'const int (*)(void)' are NOT compatible types.
    // They should be allowed as distinct associations in _Generic.

    run_pass(
        r#"
        int main() {
            int (*f)(void) = 0;
            int r = _Generic(f,
                int (*)(void): 1,
                const int (*)(void): 2,
                default: 3
            );
            return r == 1 ? 0 : 1;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_function_pointer_assignment_respects_return_qualifiers() {
    run_fail_with_message(
        r#"
        int foo(void) { return 0; }
        int main() {
            const int (*f)(void) = foo;
            return 0;
        }
        "#,
        "type mismatch: expected const int()*, found int()",
    );
}

#[test]
fn test_generic_distinguishes_atomic_return_types() {
    run_pass(
        r#"
        int main() {
            int (*f)(void) = 0;
            int r = _Generic(f,
                int (*)(void): 1,
                _Atomic int (*)(void): 2,
                default: 3
            );
            return r == 1 ? 0 : 1;
        }
        "#,
        CompilePhase::Mir,
    );
}
