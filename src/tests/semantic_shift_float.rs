use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_shift_left_float_lhs() {
    let source = r#"
        int main() {
            float f = 1.0;
            int x = f << 1;
            return 0;
        }
    "#;
    run_fail_with_message(source, "Invalid operands for binary operation: have 'float' and 'int'");
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
    run_fail_with_message(source, "Invalid operands for binary operation: have 'int' and 'float'");
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
    run_fail_with_message(source, "Invalid operands for binary operation: have 'float' and 'int'");
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
    run_fail_with_message(source, "Invalid operands for binary operation: have 'int' and 'float'");
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
    run_fail_with_message(source, "Invalid operands for binary operation: have 'float' and 'int'");
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
    run_fail_with_message(source, "Invalid operands for binary operation: have 'int' and 'float'");
}
