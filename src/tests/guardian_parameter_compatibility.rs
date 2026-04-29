use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_function_pointer_atomic_parameter_compatibility() {
    // C11 6.7.6.3p15: top-level qualifiers are stripped for parameter compatibility.
    // BUT _Atomic is special. Atomic types are NOT compatible with non-atomic types.
    // Therefore, void(*)(int) and void(*)(_Atomic int) should NOT be compatible.

    // If they were compatible, this _Generic would fail due to multiple matches.
    // If they are NOT compatible (correct), it should pass and return 0.
    run_pass(
        r#"
        typedef void (*P)(int);
        typedef void (*PA)(_Atomic int);
        int main() {
            P p = 0;
            return _Generic(p, P: 0, PA: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_function_pointer_const_parameter_compatibility() {
    // void(*)(int) and void(*)(const int) ARE compatible.
    // This should FAIL because both associations are compatible with the controlling expression.
    run_fail_with_message(
        r#"
        typedef void (*P)(int);
        typedef void (*PC)(const int);
        int main() {
            P p = 0;
            return _Generic(p, P: 0, PC: 1);
        }
        "#,
        "matches multiple associations",
    );
}

#[test]
fn test_function_pointer_array_parameter_compatibility() {
    // Parameter adjustment happens BEFORE compatibility check.
    // void(*)(int*) and void(*)(int[const 10]) ARE compatible because
    // int[const 10] adjusts to int * const, and top-level const is stripped.
    run_fail_with_message(
        r#"
        typedef void (*P)(int *);
        typedef void (*PA)(int [const 10]);
        int main() {
            P p = 0;
            return _Generic(p, P: 0, PA: 1);
        }
        "#,
        "matches multiple associations",
    );
}
