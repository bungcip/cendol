//! Tests for code generation functionality
//!
//! This module tests the code generation pipeline from C source code
//! to executable binaries, ensuring that the generated code produces
//! the expected results.

use std::fs;
use std::io::Write;
use std::process::Command;

use cendol::codegen::CodeGen;
use cendol::file::FileManager;
use cendol::parser::Parser;
use cendol::preprocessor::Preprocessor;

// Compiles C code through the full pipeline (preprocessor -> parser -> codegen)
fn compile_to_object_bytes(
    input: &str,
    filename: &str,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut preprocessor = Preprocessor::new(FileManager::new());
    let tokens = preprocessor.preprocess(input, filename)?;

    // Parser now handles filtering internally
    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;
    let codegen = CodeGen::new();
    let object_bytes = codegen.compile(ast)?;
    Ok(object_bytes)
}

/// Test configuration constants
mod config {
    pub const C_COMPILER: &str = "cc";
    pub const C_LIB_FLAG: &str = "-lc";
    pub const OBJ_EXTENSION: &str = ".o";
    pub const EXE_EXTENSION: &str = ".out";
    pub const TEST_FILE_PREFIX: &str = "test_";
}

/// Compiles and runs C code, returning the exit code
fn compile_and_run(input: &str, test_name: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let object_bytes = compile_to_object_bytes(input, &format!("{}.c", test_name))?;

    let obj_filename = format!(
        "{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::OBJ_EXTENSION
    );
    let exe_filename = format!(
        "./{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::EXE_EXTENSION
    );

    // Write object file
    let mut object_file = fs::File::create(&obj_filename)?;
    object_file.write_all(&object_bytes)?;
    drop(object_file); // Explicitly close the file

    // Compile object file to executable
    let compile_status = Command::new(config::C_COMPILER)
        .arg(&obj_filename)
        .arg("-o")
        .arg(&exe_filename)
        .arg(config::C_LIB_FLAG)
        .status()?;

    if !compile_status.success() {
        return Err(format!("Compilation failed for test: {}", test_name).into());
    }

    // Run executable and get exit code
    let output = Command::new(&exe_filename).status()?;
    let exit_code = output.code().unwrap_or(-1);

    // Clean up generated files
    let _ = fs::remove_file(&obj_filename);
    let _ = fs::remove_file(&exe_filename);

    Ok(exit_code)
}

/// Compiles and runs C code, capturing stdout output
fn compile_and_run_with_output(
    input: &str,
    test_name: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    let object_bytes = compile_to_object_bytes(input, &format!("{}.c", test_name))?;

    let obj_filename = format!(
        "{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::OBJ_EXTENSION
    );
    let exe_filename = format!(
        "./{}{}{}",
        config::TEST_FILE_PREFIX,
        test_name,
        config::EXE_EXTENSION
    );

    // Write object file
    let mut object_file = fs::File::create(&obj_filename)?;
    object_file.write_all(&object_bytes)?;
    drop(object_file);

    // Compile object file to executable
    let compile_status = Command::new(config::C_COMPILER)
        .arg(&obj_filename)
        .arg("-o")
        .arg(&exe_filename)
        .arg(config::C_LIB_FLAG)
        .status()?;

    if !compile_status.success() {
        return Err(format!("Compilation failed for test: {}", test_name).into());
    }

    // Run executable and capture output
    let output = Command::new(&exe_filename).output()?;
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();

    // Clean up generated files
    let _ = fs::remove_file(&obj_filename);
    let _ = fs::remove_file(&exe_filename);

    Ok(stdout)
}

#[cfg(test)]
mod tests {
    use super::{compile_and_run, compile_and_run_with_output};

    /// Test basic code generation with a simple function
    #[test]
    fn test_codegen() {
        let input = "int main() { return 0; }";
        let exit_code = compile_and_run(input, "codegen").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation with external function calls
    #[test]
    fn test_external_function_call() {
        let input = r#"
        int puts(const char *s);
        int main() {
            puts("hello world");
            return 0;
        }
        "#;
        let output = compile_and_run_with_output(input, "external_function_call").unwrap();
        assert_eq!(output.trim(), "hello world");
    }

    /// Test code generation with ternary conditional expressions
    #[test]
    fn test_ternary_true_condition() {
        let input = r#"
        int main() {
            return 1 ? 42 : 24;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_true").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation with ternary conditional expressions (false condition)
    #[test]
    fn test_ternary_false_condition() {
        let input = r#"
        int main() {
            return 0 ? 42 : 24;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_false").unwrap();
        assert_eq!(exit_code, 24);
    }

    // /// Test code generation with ternary in variable assignment
    // #[test]
    // fn test_ternary_assignment() {
    //     let input = r#"
    //     int main() {
    //         int result;
    //         result = 1 ? 100 : 200;
    //         return result;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "ternary_assignment").unwrap();
    //     assert_eq!(exit_code, 100);
    // }

    /// Test code generation with ternary using variable condition
    #[test]
    fn test_ternary_variable_condition() {
        let input = r#"
        int main() {
            int condition = 1;
            return condition ? 77 : 88;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_var_condition").unwrap();
        assert_eq!(exit_code, 77);
    }

    /// Test code generation with nested ternary expressions
    #[test]
    fn test_nested_ternary() {
        let input = r#"
        int main() {
            return 1 ? 0 ? 10 : 20 : 30;
        }
        "#;
        let exit_code = compile_and_run(input, "nested_ternary").unwrap();
        assert_eq!(exit_code, 20);
    }

    /// Test code generation with ternary in arithmetic expression
    #[test]
    fn test_ternary_arithmetic() {
        let input = r#"
        int main() {
            int x = 5;
            return x > 0 ? x + 10 : x - 10;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_arithmetic").unwrap();
        assert_eq!(exit_code, 15);
    }

    // /// Test code generation with ternary in function argument
    // #[test]
    // fn test_ternary_function_arg() {
    //     let input = r#"
    //     int printf(const char *s, int n);
    //     int main() {
    //         printf("%d\n", 1 ? 123 : 456);
    //         return 0;
    //     }
    //     "#;
    //     let output = compile_and_run_with_output(input, "ternary_function_arg").unwrap();
    //     assert_eq!(output, "123\\n");
    // }

    /// Test code generation with ternary expressions (basic functionality)
    #[test]
    fn test_ternary_basic() {
        let input = r#"
        int main() {
            return 1 ? 42 : 24;
        }
        "#;
        let exit_code = compile_and_run(input, "ternary_basic").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation with _Bool variable declarations
    #[test]
    fn test_bool_variable() {
        let input = r#"
        int main() {
            _Bool a = 1;
            if (a) {
                return 42;
            }
            return 0;
        }
        "#;
        let exit_code = compile_and_run(input, "bool_variable").unwrap();
        assert_eq!(exit_code, 42);
    }

    // /// Test code generation with designated initializers for structs
    // #[test]
    // fn test_designated_initializer() {
    //     let input = r#"
    //     int main() {
    //         struct { int x; int y; } point = { .y = 10, .x = 20 };
    //         return point.x;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "designated_initializer").unwrap();
    //     assert_eq!(exit_code, 20);
    // }

    // /// Test code generation with struct padding
    // #[test]
    // fn test_struct_padding() {
    //     let input = r#"
    //     int main() {
    //         struct { char a; int b; } s = { .a = 1, .b = 2 };
    //         return s.b;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "struct_padding").unwrap();
    //     assert_eq!(exit_code, 2);
    // }

    // /// Test code generation with pointer member access
    // #[test]
    // fn test_pointer_member_access() {
    //     let input = r#"
    //     int main() {
    //         struct { int x; int y; } point = { .x = 10, .y = 20 };
    //         struct { int x; int y; } *p = &point;
    //         return p->y;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "pointer_member_access").unwrap();
    //     assert_eq!(exit_code, 20);
    // }

    // /// Test code generation with advanced pointer member access
    // #[test]
    // fn test_advanced_pointer_member_access() {
    //     let input = r#"
    //     struct Point { int x; int y; };
    //     struct Point get_point() {
    //         struct Point p;
    //         p.y = 20;
    //         return p;
    //     }
    //     int main() {
    //         return get_point().y;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "advanced_pointer_member_access").unwrap();
    //     assert_eq!(exit_code, 20);
    // }

    /// Test code generation for type casting
    #[test]
    fn test_type_casting() {
        let input = r#"
        int main() {
            int x = 1;
            char y = (char)x;
            return y;
        }
        "#;
        let exit_code = compile_and_run(input, "type_casting").unwrap();
        assert_eq!(exit_code, 1);
    }

    // /// Test code generation for compound literals with structs
    // #[test]
    // fn test_compound_literal_struct() {
    //     let input = r#"
    //     struct Point { int x; int y; };
    //     int main() {
    //         struct Point p = (struct Point){ .x = 10, .y = 20 };
    //         return p.x;
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "compound_literal_struct").unwrap();
    //     assert_eq!(exit_code, 10);
    // }

    // /// Test code generation for compound literals with arrays
    // #[test]
    // fn test_compound_literal_array() {
    //     let input = r#"
    //     int main() {
    //         int *p = (int[]){ 1, 2, 3 };
    //         return p[1];
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "compound_literal_array").unwrap();
    //     assert_eq!(exit_code, 2);
    // }

    /// Test code generation for pointer subtraction
    #[test]
    fn test_pointer_subtraction() {
        let input = r#"
        int main() {
            int arr[5];
            int *p1 = &arr[1];
            int *p2 = &arr[4];
            return p2 - p1;
        }
        "#;
        let exit_code = compile_and_run(input, "pointer_subtraction").unwrap();
        assert_eq!(exit_code, 3);
    }

    // /// Test code generation for inline functions
    // #[test]
    // fn test_inline_function() {
    //     let input = r#"
    //     inline int add(int a, int b) {
    //         return a + b;
    //     }
    //     int main() {
    //         return add(5, 3);
    //     }
    //     "#;
    //     let exit_code = compile_and_run(input, "inline_function").unwrap();
    //     assert_eq!(exit_code, 8);
    // }

    /// Test code generation for variadic functions
    #[test]
    fn test_variadic_function() {
        let input = r#"
        int variadic_func(int a, ...);
        int main() {
            return variadic_func(42, 1, 2, 3);
        }
        int variadic_func(int a, ...) {
            return a;
        }
        "#;
        let exit_code = compile_and_run(input, "variadic_function").unwrap();
        assert_eq!(exit_code, 42);
    }

    /// Test code generation for chained assignments
    #[test]
    fn test_chained_assignment() {
        let input = r#"
        int main() {
            int x;
            int y;
            x = y = 0;
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "chained_assignment").unwrap();
        assert_eq!(exit_code, 0);
    }

    /// Test code generation for bitwise and shift assignment operators
    #[test]
    fn test_bitwise_and_shift_assignment_operators() {
        let input = r#"
        int main() {
            int x = 15;
            x &= 7;
            x |= 8;
            x ^= 12;
            x <<= 1;
            x >>= 2;
            return x;
        }
        "#;
        let exit_code = compile_and_run(input, "bitwise_and_shift_assignment_operators").unwrap();
        assert_eq!(exit_code, 1);
    }
}
