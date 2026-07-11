use crate::tests::codegen_common::*;

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

#[test]
fn test_asm_label_initialized() {
    let source = r#"
        int printf(const char *, ...);
        int x __asm__("y") = 42;
        int main() {
            printf("%d\n", x);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output, "42\n");
}
