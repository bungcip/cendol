//! Integration tests for the compiler driver.

use crate::driver::cli::CompileConfig;
use crate::driver::CompilerDriver;

#[test]
fn test_compile_source_valid() {
    let source = "int main() { return 0; }";
    let config = CompileConfig::new_for_test();
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.compile_source(source, "test.c");
    assert!(result.is_ok());
    assert!(!driver.has_errors());
}
