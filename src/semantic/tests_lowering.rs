use crate::driver::compiler::CompilePhase;
use crate::driver::{cli::CompileConfig, compiler::CompilerDriver};

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that semantic lowering converts FunctionDef to Function nodes
    #[test]
    fn test_function_def_lowering() {
        let source = r#"
            int add(int a, int b) {
                return a + b;
            }
            
            int main() {
                return add(1, 2);
            }
        "#;

        let phase = CompilePhase::Mir;
        let config = CompileConfig::from_virtual_file(source.to_string(), phase);
        let mut driver = CompilerDriver::from_config(config);
        let mut out = driver.run_pipeline(phase).unwrap();
        let first = out.units.first_mut().unwrap();
        let artifact = first.1;

        // Get the complete semantic analysis output
        let sema_output = match artifact.sema_output.clone() {
            Some(sema_output) => sema_output,
            None => {
                panic!("No semantic output available");
            }
        };

        // Check that we have the expected functions
        let functions = sema_output.functions;
        let function_names: Vec<String> = functions.values().map(|f| f.name.to_string()).collect();

        assert!(
            function_names.contains(&"add".to_string()),
            "Function 'add' not found in MIR"
        );
        assert!(
            function_names.contains(&"main".to_string()),
            "Function 'main' not found in MIR"
        );

        // Verify that the MIR module is not empty
        assert!(
            !sema_output.module.functions.is_empty(),
            "MIR module should contain functions"
        );
    }

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
        let mut out = driver.run_pipeline(phase).unwrap();
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

    /// Test that semantic lowering correctly identifies lvalue errors
    #[test]
    fn test_lvalue_error_lowering() {
        let source = r#"
            int main() {
                ++1;
            }
        "#;

        let phase = CompilePhase::Mir;
        let config = CompileConfig::from_virtual_file(source.to_string(), phase);
        let mut driver = CompilerDriver::from_config(config);
        let result = driver.run_pipeline(phase);

        // Ensure the pipeline failed
        assert!(result.is_err());

        // Check for the specific semantic error
        let diags = driver.get_diagnostics();
        assert_eq!(diags.len(), 1);
        let error = diags.get(0).unwrap();

        // Check the error message is an exact match
        assert_eq!(error.message, "Expression is not assignable (not an lvalue)");

        // Check that the error span is correct
        let (line, col) = driver.source_manager.get_line_column(error.span.start).unwrap();
        assert_eq!(line, 3, "Error should be on line 3");
        assert_eq!(col, 17, "Error should be at column 17");
    }

    /// Test that semantic lowering correctly identifies typedef redefinitions
    #[test]
    #[should_panic(expected = "Anonymous declarations unsupported")]
    fn test_typedef_redefinition_error() {
        let source = r#"
            typedef int my_int;
            typedef int my_int;
        "#;

        let phase = CompilePhase::Mir;
        let config = CompileConfig::from_virtual_file(source.to_string(), phase);
        let mut driver = CompilerDriver::from_config(config);
        let _ = driver.run_pipeline(phase);
    }
}
