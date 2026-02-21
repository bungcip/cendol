use crate::tests::test_utils::setup_diagnostics_output;

#[test]
fn test_shift_left_float_lhs() {
    let source = r#"
        int main() {
            float f = 1.0;
            int x = f << 1;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_shift_left_float_rhs() {
    let source = r#"
        int main() {
            int x = 1;
            float f = 1.0;
            int y = x << f;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_shift_right_float_lhs() {
    let source = r#"
        int main() {
            float f = 1.0;
            int x = f >> 1;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_shift_right_float_rhs() {
    let source = r#"
        int main() {
            int x = 1;
            float f = 1.0;
            int y = x >> f;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_compound_shift_float() {
    let source = r#"
        int main() {
            float f = 1.0;
            f <<= 1;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_compound_shift_int_float() {
    let source = r#"
        int main() {
            int x = 1;
            float f = 1.0;
            x <<= f;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
