//! Tests for runtime behavior integration
use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_integer_truncation_no_panic() {
    let code = r#"
        int main() {
            int a = -9223372036854775808LL;
            int b = (int)9223372036854775807LL;
            int c = (int)18446744073709551615ULL;
            unsigned int d = (unsigned int)9223372036854775807LL;
            
            if (a != 0) return 1;
            if (b != -1) return 2;
            if (c != -1) return 3;
            if (d != 4294967295U) return 4;
            
            return 0;
        }
    "#;

    let output = run_c_code_exit_status(code);
    assert_eq!(output, 0);
}
