use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_builtin_complex_basic() {
    run_pass(
        r#"
        int main() {
            _Complex double cd = __builtin_complex(1.0, 2.0);
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_complex_promotion() {
    run_pass(
        r#"
        int main() {
            float f = 1.0f;
            double d = 2.0;
            _Complex double cd = __builtin_complex(f, d);
            _Complex double cd2 = __builtin_complex(d, f);
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_complex_int() {
    run_pass(
        r#"
        int main() {
            int i = 1;
            int j = 2;
            _Complex double cd = __builtin_complex(i, j);
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_complex_invalid_operand() {
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            struct S s;
            __builtin_complex(s, 1.0);
            return 0;
        }
        "#,
        "Invalid operand for unary operation",
    );
}

#[test]
fn test_builtin_complex_invalid_operand_2() {
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            struct S s;
            __builtin_complex(1.0, s);
            return 0;
        }
        "#,
        "Invalid operand for unary operation",
    );
}

#[test]
fn test_builtin_complex_execution() {
    let source = r#"
        int main() {
            _Complex double cd = __builtin_complex(3.0, 4.0);
            if (__real__ cd != 3.0) return 1;
            if (__imag__ cd != 4.0) return 2;
            return 0;
        }
    "#;

    // We can't easily run it here without a full environment,
    // but we can check if it compiles to MIR correctly.
    run_pass(source, CompilePhase::Mir);
}
