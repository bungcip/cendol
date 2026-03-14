use crate::tests::codegen_common::run_c_code_exit_status;

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
        // Simple manual NaN if math.h is not available or too complex for test
        // But we have __builtin_nan
        int main() {
            _Bool b = (_Bool)__builtin_nan("");
            if (!b) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
