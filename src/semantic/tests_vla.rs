use crate::driver::compiler::{CompilePhase, CompilerDriver};
use crate::driver::cli::CompileConfig;

fn compile_source(source: &str) -> Result<(), String> {
    let mut config = CompileConfig::default();
    config.input_files = vec![crate::driver::cli::PathOrBuffer::Buffer(
        "test.c".to_string(),
        source.as_bytes().to_vec(),
    )];
    config.stop_after = CompilePhase::Mir; // Check semantic phases up to MIR

    let mut driver = CompilerDriver::from_config(config);
    driver.run_pipeline(CompilePhase::Mir).map(|_| ()).map_err(|_| {
        // Collect errors
        let diags = driver.get_diagnostics();
        if diags.is_empty() {
            "Compilation failed without diagnostics".to_string()
        } else {
            diags[0].message.clone()
        }
    })
}

#[test]
fn test_valid_vla() {
    let source = r#"
        int main() {
            int n = 10;
            int a[n];
            return 0;
        }
    "#;
    assert!(compile_source(source).is_ok());
}

// TODO: Enable this test when function prototype scope is properly supported in symbol_resolver.
// Currently, parameters in function declarations (not definitions) do not introduce symbols,
// so `n` in `int a[n]` is unresolved.
/*
#[test]
fn test_vla_in_function_param() {
    let source = r#"
        void f(int n, int a[n]);
        int main() { return 0; }
    "#;
    assert!(compile_source(source).is_ok());
}
*/

#[test]
fn test_vla_star() {
    let source = r#"
        void f(int a[*]);
        int main() { return 0; }
    "#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_sizeof_vla() {
    let source = r#"
        int main() {
            int n = 10;
            int a[n];
            sizeof(a);
            return 0;
        }
    "#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_vla_in_struct_fail() {
    let source = r#"
        int n = 10;
        struct S {
            int a[n];
        };
        int main() { return 0; }
    "#;
    assert!(compile_source(source).is_err());
}
