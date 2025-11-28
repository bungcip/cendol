use super::*;
use crate::driver::cli::{Cli, CompileConfig};
use clap::Parser;

#[test]
fn test_simple_compilation_succeeds() {
    let cli = Cli::parse_from(vec!["cendol", "test.c"]);
    let mut driver = CompilerDriver::from_config(cli.into_config());
    let source = "int main() { return 0; }";
    let result = driver.compile_source(source, "test.c");
    assert!(result.is_ok());
    assert!(!driver.has_errors());
}

#[test]
fn test_compilation_fails_on_syntax_error() {
    let cli = Cli::parse_from(vec!["cendol", "test.c"]);
    let mut driver = CompilerDriver::from_config(cli.into_config());
    let source = "int main() { return 0 }";
    let result = driver.compile_source(source, "test.c");
    assert!(result.is_ok());
    assert!(driver.has_errors());
}
