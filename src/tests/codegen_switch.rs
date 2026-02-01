//! Tests for switch statement codegen
use crate::tests::codegen_common::setup_cranelift;

#[test]
fn test_switch_unreachable_cases() {
    let source = r#"
        int printf(const char *, ...);
        int main() {
            int x = 0;
            switch (x) {
                case 1:
                    printf("case_1_marker");
                    break;
                case 2:
                    printf("case_2_marker");
                    break;
                default:
                    printf("default_marker");
                    break;
            }
            return 0;
        }
    "#;

    let clif_ir = setup_cranelift(source);
    println!("{}", clif_ir);

    // Count calls to printf.
    // There should be 3 calls (one for each case).
    // If cases are skipped, there will be fewer calls.
    let call_count = clif_ir.matches("call_indirect").count();
    assert_eq!(
        call_count, 3,
        "Expected 3 calls to printf, found {}. Missing cases?",
        call_count
    );
}
