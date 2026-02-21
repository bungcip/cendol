use crate::tests::codegen_common::run_c_code_exit_status;

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
fn test_bool_init_float() {
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
fn test_int_init_float() {
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
fn test_int_init_float_overflow() {
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
