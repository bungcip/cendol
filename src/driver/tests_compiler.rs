use super::*;
use crate::driver::cli::{Cli, CompileConfig};
use clap::Parser;
use std::path::Path;

#[test]
fn test_simple_compilation_succeeds() {
    let cli = Cli::parse_from(vec!["cendol", "test_input.c"]);
    let mut driver = CompilerDriver::from_config(cli.into_config());
    let result = driver.compile_file(Path::new("test_input.c"));
    assert!(result.is_ok());
    assert!(!driver.has_errors());
}

#[test]
fn test_compilation_fails_on_syntax_error() {
    let cli = Cli::parse_from(vec!["cendol", "invalid_input.c"]);
    let mut driver = CompilerDriver::from_config(cli.into_config());
    let result = driver.compile_file(Path::new("invalid_input.c"));
    assert!(result.is_ok());
    assert!(driver.has_errors());
}
