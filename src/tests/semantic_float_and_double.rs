use crate::tests::{codegen_common::run_c_code_exit_status, test_utils::run_fail_with_message};

#[test]
fn test_double_init_with_int() {
    let source = r#"
        double x = 100;
        int main() {
            if (x != 100.0) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_float_init_with_int() {
    let source = r#"
        float x = 100;
        int main() {
            if (x != 100.0f) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_float_init_with_int_neg() {
    let source = r#"
        float x = -100;
        int main() {
            if (x != -100.0f) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_float_init_with_bool() {
    // Tests implicit conversion from bool constant to float
    let source = r#"
        _Bool b = 1;
        float x = (_Bool)1;
        int main() {
            if (x != 1.0f) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_int_init_with_float() {
    let source = r#"
        int x = 100.5;
        int main() {
            if (x != 100) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_char_init_with_float_overflow() {
    // 300.0 fits in int, but truncating to char would overflow if not handled.
    // However, global vars in C must be initialized with constant expressions.
    // Conversion from float to int is allowed.
    let source = r#"
        char x = 300.0; // 300 does not fit in char. Implementation defined or modular.
        // Usually (char)300 -> 44 (if char is signed/8bit) or similar.
        // 300 = 0x12C. 0x2C = 44.
        // If char is signed, 300 -> 44.

        int main() {
            // Check if it runs without crashing at least.
            // Value depends on signedness of char.
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

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
fn test_compound_shift_left_float_lhs() {
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
fn test_compound_shift_left_float_rhs() {
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

#[test]
fn test_float_to_int_cast_precision() {
    // 16777217.0 is 2^24 + 1.
    // In IEEE 754 single precision (float), it should be rounded to 16777216.0.
    // Casting that float to int should result in 16777216.
    let source = r#"
        int fcast = (float)16777217.0;
        _Static_assert((int)(float)16777217.0 == 16777216, "Constant folding should truncate float precision");
        
        int main() {
            if (fcast != 16777216) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_float_to_int_cast_literal_precision() {
    // Same but with float literal
    let source = r#"
        int main() {
            int i = (int)16777217.0f;
            if (i != 16777216) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_fp_const_eval() {
    let source = r#"
        int fpeq = (0.1 == 0.2);
        int fpneq = (0.1 != 0.1);
        int fpnot = !0.1;
        int main() {
            if (fpeq != 0) return 1;
            if (fpneq != 0) return 2;
            if (fpnot != 0) return 3;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_nan_bool_conversion() {
    let source = r#"
        int main() {
            _Bool b = (_Bool)__builtin_nan("");
            if (!b) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
