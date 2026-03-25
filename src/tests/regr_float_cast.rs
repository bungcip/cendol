use crate::tests::codegen_common::run_c_code_exit_status;

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
