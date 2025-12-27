use crate::driver::compiler::CompilePhase;
use crate::driver::{cli::CompileConfig, compiler::CompilerDriver};

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that semantic lowering converts Declaration to VarDecl nodes
    #[test]
    fn test_declaration_lowering() {
        let source = r#"
            int global_var = 42;
            
            int main() {
                int local_var = 10;
                return local_var;
            }
        "#;

        let phase = CompilePhase::Mir;
        let config = CompileConfig::from_virtual_file(source.to_string(), phase);
        let mut driver = CompilerDriver::from_config(config);

        // Print diagnostics if compilation fails
        let result = driver.run_pipeline(phase);
        let mut out = match result {
            Ok(out) => out,
            Err(e) => {
                // Print diagnostics before panicking
                driver.print_diagnostics();
                panic!("Compilation failed with error: {:?}", e);
            }
        };

        let first = out.units.first_mut().unwrap();
        let artifact = first.1;

        // Get the complete semantic analysis output
        let sema_output = match artifact.sema_output.clone() {
            Some(sema_output) => sema_output,
            None => {
                panic!("No semantic output available");
            }
        };

        // Check that we have the expected globals
        let globals = sema_output.globals;
        let global_names: Vec<String> = globals.values().map(|g| g.name.to_string()).collect();

        assert!(
            global_names.contains(&"global_var".to_string()),
            "Global variable 'global_var' not found in MIR"
        );

        // Check that we have the expected functions
        let functions = sema_output.functions;
        let function_names: Vec<String> = functions.values().map(|f| f.name.to_string()).collect();

        assert!(
            function_names.contains(&"main".to_string()),
            "Function 'main' not found in MIR"
        );
    }
}
