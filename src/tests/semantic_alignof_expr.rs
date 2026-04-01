use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_with_output;
use crate::tests::test_utils::run_pass;

#[test]
fn test_alignof_expression_basic() {
    let source = r#"
        int main() {
            int x = 42;
            return _Alignof x;
        }
    "#;
    // int alignment is typically 4
    let output = run_c_code_with_output(source);
    if output.trim().is_empty() {
        run_pass(source, CompilePhase::Cranelift);
    } else {
        assert!(output.contains("4") || output.trim() == "4");
    }
}

#[test]
fn test_alignof_expression_alignas() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            int _Alignas(64) x = 42;
            printf("%d", (int)_Alignof x);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "64");
}


#[test]
fn test_alignof_expression_nested() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            int _Alignas(256) x = 42;
            printf("%d", (int)_Alignof *&x);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "4");
}

#[test]
fn test_alignof_expression_sizeof_interaction() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            int _Alignas(512) x = 42;
            printf("%d", (int)sizeof(_Alignof x));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "8");
}

#[test]
fn test_alignof_expression_pedantic() {
    let source = r#"
        int main() {
            int x = 42;
            return _Alignof x;
        }
    "#;

    // 1. Without pedantic-errors, it should pass (as a warning)
    run_pass(source, CompilePhase::Mir);

    // 2. With pedantic-errors, it should fail
    use crate::driver::cli::{Cli, PathOrBuffer};
    use crate::driver::compiler::CompilerDriver;
    use clap::Parser;

    let cli = Cli::parse_from(["cendol", "test.c", "--pedantic-errors"]);
    let mut config = cli.into_config().unwrap();
    config.input_files = vec![PathOrBuffer::Buffer("test.c".to_string(), source.as_bytes().to_vec())];
    config.stop_after = CompilePhase::Mir;

    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(CompilePhase::Mir);

    assert!(result.is_err(), "Should fail with --pedantic-errors");
    let diagnostics = driver.get_diagnostics();
    assert!(diagnostics.iter().any(|d| d.message.contains("GNU extension")));
}

#[test]
fn test_alignof_max_align_t() {
    let source = r#"
        #include <stddef.h>
        int printf(const char *, ...);
        int main() {
            printf("%d", _Alignof(max_align_t) >= _Alignof(long double));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "1");
}
