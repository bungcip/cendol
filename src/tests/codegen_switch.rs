//! Tests for switch statement codegen
use crate::tests::codegen_common::setup_cranelift;
use crate::tests::test_utils;

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
    insta::assert_snapshot!(test_utils::sort_clif_ir(&clif_ir));
}
