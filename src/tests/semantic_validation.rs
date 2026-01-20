use super::semantic_common::{setup_diagnostics_output, run_pass};
use crate::driver::artifact::CompilePhase;

#[test]
fn test_static_assert_pass() {
    run_pass(
        r#"
        int main() {
            _Static_assert(1, "This should pass");
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn rejects_modulo_on_non_integer() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            double x = 1.0;
            double y = 2.0;
            x % y;
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: Invalid operands for binary operation: have 'double' and 'double'
    Location: 5:13
    "###);
}

#[test]
fn accepts_modulo_on_integer() {
    run_pass(
        r#"
        int main() {
            int x = 1;
            int y = 2;
            x % y;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn rejects_bitnot_on_non_integer() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            double x = 1.0;
            ~x;
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: Invalid operand for unary operation: have 'double'
    Location: 4:13
    "###);
}

#[test]
fn rejects_conflicting_storage_classes() {
    let output = setup_diagnostics_output(
        r#"
        extern static int x;
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: conflicting storage class specifiers
    Location: 2:9
    "###);
}

#[test]
fn rejects_variable_as_typedef_in_cast() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int my_var = 10;
            (my_var) 1;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: Unexpected token: expected Semicolon, found IntegerConstant(1)
    Location: 4:22
    "###);
}

#[test]
fn test_static_assert_fail() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            _Static_assert(0, "This should fail");
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: static assertion failed: This should fail
    Location: 2:20
    "###);
}

#[test]
fn test_static_assert_file_scope_fail() {
    let output = setup_diagnostics_output(
        r#"
        _Static_assert(0, "This should fail");
        int main() {
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: static assertion failed: This should fail
    Location: 2:9
    "###);
}

#[test]
fn test_static_assert_non_constant() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int x = 1;
            _Static_assert(x, "error");
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: expression in static assertion is not constant
    Location: 2:20
    "###);
}

#[test]
fn test_static_assert_comparison() {
    run_pass(
        r#"
        _Static_assert(1 < 2, "This should pass");
        _Static_assert(2 > 1, "This should pass");
        _Static_assert(1 == 1, "This should pass");
        _Static_assert(1 != 2, "This should pass");
        _Static_assert(1 <= 1, "This should pass");
        _Static_assert(1 >= 1, "This should pass");
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_logical() {
    run_pass(
        r#"
        _Static_assert(1 && 1, "This should pass");
        _Static_assert(1 || 0, "This should pass");
        _Static_assert(0 || 1, "This should pass");
        _Static_assert(!(0), "This should pass");
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_const_eval_negative_numbers() {
    run_pass(
        r#"
        _Static_assert(-1 < 0, "Negative one should be less than zero");
        _Static_assert(-1 == -1, "Negative one should equal negative one");
        _Static_assert(0 - 1 == -1, "Subtraction should yield negative");
        _Static_assert(+1 == 1, "Unary plus should work");
        
        // Bitwise not: ~0 is -1 (in 2s complement)
        _Static_assert(~0 == -1, "Bitwise not of zero should be -1");
        
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}
