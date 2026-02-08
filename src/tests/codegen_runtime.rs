//! Tests for runtime behavior integration
use crate::tests::codegen_common::run_c_code_with_output;

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
