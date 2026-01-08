
#![cfg(test)]
use crate::driver::{compiler::CompilerDriver, cli::CompileConfig, artifact::CompilePhase};
use std::process::Command;

#[test]
fn test_compound_assignment_add() {
    let config = CompileConfig::from_virtual_file("int main() { int x = 0; x += 5; return x; }".to_string(), CompilePhase::EmitObject);
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run();
    assert!(result.is_ok(), "Compiler run failed");

    // Execute the compiled program and check its exit code
    let output = Command::new("./a.out")
        .output()
        .expect("Failed to execute compiled program");
    assert_eq!(output.status.code(), Some(5));
}
