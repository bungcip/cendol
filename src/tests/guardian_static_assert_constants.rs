use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_pass, run_fail_with_message};

#[test]
fn static_assert_accepts_float_cast_to_int() {
    run_pass(
        r#"
        _Static_assert((int)1.0, "should pass");
        _Static_assert((int)0.5 == 0, "should pass (truncation)");
        _Static_assert((int)1.9 == 1, "should pass (truncation)");
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn static_assert_rejects_uncast_float() {
    run_fail_with_message(
        r#"
        _Static_assert(1.0, "should fail");
        "#,
        "expression in static assertion is not constant",
    );
}

#[test]
fn static_assert_rejects_float_expression_in_cast() {
     // C11 6.6p6: "floating constants that are the immediate operands of casts"
     // This means (int)(1.0 + 1.0) is technically invalid as an integer constant expression.
     run_fail_with_message(
        r#"
        _Static_assert((int)(1.0 + 1.0), "should fail");
        "#,
        "expression in static assertion is not constant",
    );
}

#[test]
fn constant_cast_performs_truncation() {
    run_pass(
        r#"
        _Static_assert((char)257 == 1, "should pass (assuming 8-bit char)");
        _Static_assert((unsigned char)-1 == 255, "should pass");
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}
