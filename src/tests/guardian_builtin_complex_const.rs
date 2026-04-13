use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtin_complex_constant_evaluation() {
    // C11 6.6p6: "...floating constants are ONLY allowed as the immediate operands of casts."
    // However, __builtin_complex is an intrinsic that constructs a complex number.
    // If its operands are constant, the result should be treatable as a constant expression
    // when accessed via __real__ or __imag__.

    run_pass(
        r#"
        _Static_assert(__real__ __builtin_complex(1.0, 2.0) == 1.0, "real part constant eval");
        _Static_assert(__imag__ __builtin_complex(1.0, 2.0) == 2.0, "imag part constant eval");

        _Static_assert(__real__ __builtin_complex(1.0f + 1.0f, 2.0f) == 2.0, "real part with expr");

        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_builtin_complex_global_init() {
    run_pass(
        r#"
        _Complex double cd = __builtin_complex(3.0, 4.0);
        int main() {
            if (__real__ cd != 3.0) return 1;
            if (__imag__ cd != 4.0) return 2;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
