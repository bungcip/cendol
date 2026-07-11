use crate::tests::codegen_common::*;
use crate::tests::test_utils::*;

#[test]
fn test_alias_and_asm_linkage() {
    let source = r#"
        int printf(const char *, ...);
        void x(void) {
            printf("OK\n");
        }
        void y(void) __attribute__((alias("x")));
        void z(void) __asm__("x");
        int main(void) {
            x();
            y();
            z();
            return 0;
        }
    "#;

    let output = run_c_code_with_output(source);
    assert_eq!(output, "OK\nOK\nOK\n");
}
