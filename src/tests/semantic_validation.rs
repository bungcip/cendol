use super::semantic_common::setup_diagnostics_output;

#[test]
fn test_static_assert_pass() {
    let source = r#"
        int main() {
            _Static_assert(1, "This should pass");
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn rejects_modulo_on_non_integer() {
    let source = r#"
        int main() {
            double x = 1.0;
            double y = 2.0;
            x % y;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn accepts_modulo_on_integer() {
    let source = r#"
        int main() {
            int x = 1;
            int y = 2;
            x % y;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn rejects_bitnot_on_non_integer() {
    let source = r#"
        int main() {
            double x = 1.0;
            ~x;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn rejects_conflicting_storage_classes() {
    let source = r#"
        extern static int x;
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn rejects_variable_as_typedef_in_cast() {
    let source = r#"
        int main() {
            int my_var = 10;
            (my_var) 1;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_static_assert_fail() {
    let source = r#"
        int main() {
            _Static_assert(0, "This should fail");
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_static_assert_file_scope_fail() {
    let source = r#"
        _Static_assert(0, "This should fail");
        int main() {
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_static_assert_non_constant() {
    let source = r#"
        int main() {
            int x = 1;
            _Static_assert(x, "error");
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_static_assert_comparison() {
    let source = r#"
        _Static_assert(1 < 2, "This should pass");
        _Static_assert(2 > 1, "This should pass");
        _Static_assert(1 == 1, "This should pass");
        _Static_assert(1 != 2, "This should pass");
        _Static_assert(1 <= 1, "This should pass");
        _Static_assert(1 >= 1, "This should pass");
        int main() {
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_static_assert_logical() {
    let source = r#"
        _Static_assert(1 && 1, "This should pass");
        _Static_assert(1 || 0, "This should pass");
        _Static_assert(0 || 1, "This should pass");
        _Static_assert(!(0), "This should pass");
        int main() {
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_const_eval_negative_numbers() {
    let source = r#"
        _Static_assert(-1 < 0, "Negative one should be less than zero");
        _Static_assert(-1 == -1, "Negative one should equal negative one");
        _Static_assert(0 - 1 == -1, "Subtraction should yield negative");
        _Static_assert(+1 == 1, "Unary plus should work");
        
        // Bitwise not: ~0 is -1 (in 2s complement)
        _Static_assert(~0 == -1, "Bitwise not of zero should be -1");
        
        int main() {
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
