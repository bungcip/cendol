use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_with_output;
use crate::tests::test_utils::run_pass_with_diagnostic_message;

#[test]
fn test_asm_ignored() {
    let output = run_c_code_with_output(
        r#"
        int printf(const char *, ...);
        
        double fn(void) {
          asm("fninit");
          return 2.0;
        }
        
        double fn2 (double a) {
          return a + (a + (a + (a + (a + (a + (a + (a + a)))))));
        }
        
        int main(void) {
          printf("%d\n", (int)(3.0 + fn() + 5.0));
          return 0;
        }
        "#,
    );
    assert_eq!(output.trim(), "10");
}

#[test]
fn test_asm_warning() {
    run_pass_with_diagnostic_message(
        r#"
        void fn(void) {
          asm("fninit");
        }
        "#,
        CompilePhase::Mir,
        "inline assembly is currently ignored by cendol",
    );
}
