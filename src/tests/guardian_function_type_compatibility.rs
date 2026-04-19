use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_pass, run_fail_with_message};

#[test]
fn test_generic_distinguishes_qualified_return_types() {
    // C11 6.7.6.3p15: "...and the return type is a compatible type."
    // 6.7.3p10: "...both shall have the identically qualified version of a compatible type."
    // Thus, int(*)(void) and const int(*)(void) are NOT compatible because their
    // return types (int and const int) are not identically qualified.

    run_pass(
        r#"
        int f(void);
        const int g(void);
        int main() {
            // This should match both associations correctly if they are distinct (incompatible).
            _Static_assert(_Generic(&f, int(*)(void): 1, const int(*)(void): 0) == 1, "Match f");
            _Static_assert(_Generic(&g, int(*)(void): 0, const int(*)(void): 1) == 1, "Match g");
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_rejects_assignment_of_incompatible_return_qualifiers() {
    run_fail_with_message(
        r#"
        int f(void);
        int main() {
            const int (*p)(void) = &f;
            return 0;
        }
        "#,
        "type mismatch: expected const int()*, found int()*",
    );
}

#[test]
fn test_rejects_compatible_typedef_redefinition_with_different_return_qualifiers() {
    run_fail_with_message(
        r#"
        typedef int F(void);
        typedef const int F(void);
        "#,
        "redefinition of 'F' with a different type",
    );
}

#[test]
fn test_preserves_noreturn_in_composite_type() {
    // GCC and Clang allow _Noreturn to be added in redeclarations.
    // The resulting composite type should be _Noreturn.
    run_pass(
        r#"
        _Noreturn void f(void);
        void f(void);
        void g(void) {
            f();
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_distinguishes_atomic_return_types() {
    run_pass(
        r#"
        int f(void);
        _Atomic int h(void);
        int main() {
            _Static_assert(_Generic(&f, int(*)(void): 1, _Atomic int(*)(void): 0) == 1, "Match f");
            _Static_assert(_Generic(&h, int(*)(void): 0, _Atomic int(*)(void): 1) == 1, "Match h");
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
