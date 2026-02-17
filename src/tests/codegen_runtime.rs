//! Tests for runtime behavior integration
use crate::tests::codegen_common::{run_c_code_exit_status, run_c_code_with_output};

#[test]
fn test_hfa_mixed_args() {
    let code = r#"
int printf(const char *fmt, ...);

struct hfa_float2 { float a, b; } f2 = { 1.1f, 1.2f };
struct hfa_double1 { double a; } d1 = { 2.2 };
int i1 = 1;
int i2 = 2;

void mixed_args(int i1, struct hfa_float2 a, int i2, struct hfa_double1 c)
{
    printf("%d %.1f %.1f %d %.1f", i1, a.a, a.b, i2, c.a);
}

int main() {
    mixed_args(i1, f2, i2, d1);
    return 0;
}
"#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1 1.1 1.2 2 2.2");
}

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
