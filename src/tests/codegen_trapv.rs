use super::codegen_common::compile_and_run_c_with_ftrapv;

#[test]
fn test_trapv_addition() {
    let source = r#"
        int main() {
            volatile int a = 2147483647;
            volatile int b = 1;
            volatile int c = a + b;
            return 0;
        }
    "#;

    // With ftrapv=false, it should wrap and exit successfully (0)
    let output_no_trap = compile_and_run_c_with_ftrapv(source, false);
    assert!(output_no_trap.status.success());

    // With ftrapv=true, it should trap (crash with non-zero exit status)
    let output_trap = compile_and_run_c_with_ftrapv(source, true);
    assert!(!output_trap.status.success());
}

#[test]
fn test_trapv_subtraction() {
    let source = r#"
        int main() {
            volatile int a = -2147483648;
            volatile int b = 1;
            volatile int c = a - b;
            return 0;
        }
    "#;

    // With ftrapv=false, it should wrap and exit successfully (0)
    let output_no_trap = compile_and_run_c_with_ftrapv(source, false);
    assert!(output_no_trap.status.success());

    // With ftrapv=true, it should trap (crash with non-zero exit status)
    let output_trap = compile_and_run_c_with_ftrapv(source, true);
    assert!(!output_trap.status.success());
}

#[test]
fn test_trapv_multiplication() {
    let source = r#"
        int main() {
            volatile int a = 1073741824;
            volatile int b = 2;
            volatile int c = a * b;
            return 0;
        }
    "#;

    // With ftrapv=false, it should wrap and exit successfully (0)
    let output_no_trap = compile_and_run_c_with_ftrapv(source, false);
    assert!(output_no_trap.status.success());

    // With ftrapv=true, it should trap (crash with non-zero exit status)
    let output_trap = compile_and_run_c_with_ftrapv(source, true);
    assert!(!output_trap.status.success());
}
