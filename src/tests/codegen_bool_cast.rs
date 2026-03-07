//! Tests for _Bool casting behavior
use crate::tests::codegen_common::run_c_code_exit_status;

/// Test that casting a non-zero integer to _Bool results in 1 (C11 6.3.1.2)
#[test]
fn test_bool_cast_nonzero_to_bool() {
    let source = r#"
        int main(void) {
            int i = (_Bool)123;
            return i;
        }
    "#;
    let exit_code = run_c_code_exit_status(source);
    assert_eq!(exit_code, 1, "Casting 123 to _Bool should result in 1");
}

/// Test that casting zero to _Bool results in 0
#[test]
fn test_bool_cast_zero_to_bool() {
    let source = r#"
        int main(void) {
            int i = (_Bool)0;
            return i;
        }
    "#;
    let exit_code = run_c_code_exit_status(source);
    assert_eq!(exit_code, 0, "Casting 0 to _Bool should result in 0");
}

/// Test that casting a negative integer to _Bool results in 1
#[test]
fn test_bool_cast_negative_to_bool() {
    let source = r#"
        int main(void) {
            int i = (_Bool)(-5);
            return i;
        }
    "#;
    let exit_code = run_c_code_exit_status(source);
    assert_eq!(exit_code, 1, "Casting -5 to _Bool should result in 1");
}

/// Test global variable initialization with _Bool cast
#[test]
fn test_bool_cast_global_init() {
    let source = r#"
        int i = (_Bool)123;
        
        int main(void) {
            return i;
        }
    "#;
    let exit_code = run_c_code_exit_status(source);
    assert_eq!(exit_code, 1, "Global _Bool cast should also result in 1");
}
