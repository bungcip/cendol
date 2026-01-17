#![cfg(test)]
use crate::ast::dumper::AstDumper;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;
use libc;
use std::io::Read;
use std::os::unix::io::FromRawFd;

/// Test helper to capture stdout output
fn capture_stdout<F: Fn()>(f: F) -> String {
    let mut output = Vec::new();

    unsafe {
        // Create a pipe
        let mut fds = [0; 2];
        assert_eq!(libc::pipe(fds.as_mut_ptr()), 0);
        let (read_fd, write_fd) = (fds[0], fds[1]);

        // Fork the process
        match libc::fork() {
            0 => {
                // Child process - redirect stdout to write end of pipe
                libc::close(read_fd);
                libc::dup2(write_fd, libc::STDOUT_FILENO);
                libc::close(write_fd);

                // Run the function
                f();
                libc::exit(0);
            }
            -1 => panic!("Fork failed"),
            pid => {
                // Parent process - read from read end of pipe
                libc::close(write_fd);
                let mut read = std::fs::File::from_raw_fd(read_fd);
                read.read_to_end(&mut output).unwrap();

                // Wait for child process to terminate
                let mut status = 0;
                libc::waitpid(pid, &mut status, 0);
            }
        }
    }

    String::from_utf8(output).unwrap()
}

#[test]
fn test_dump_parsed_ast_simple() {
    let source = "int main() { return 0; }";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_variables() {
    let source = "int x = 42; int y = x + 5;";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(
        output,
        @""
    );
}

#[test]
fn test_dump_parsed_ast_with_structs() {
    let source = "struct Point { int x; int y; } p = {1, 2};";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(
        output,
        @""
    );
}

#[test]
fn test_dump_parsed_ast_with_enums() {
    let source = "enum Color { RED, GREEN = 2, BLUE } c = RED;";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_strings() {
    let source = "char* msg = \"Hello, world!\";";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_floats() {
    let source = "float pi = 3.14159; double e = 2.71828;";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_chars() {
    let source = "char c = 'a'; signed char sc = 'b'; unsigned char uc = 'c';";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_pointers() {
    let source = "int x = 10; int* ptr = &x; int** ptr_ptr = &ptr;";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_arrays() {
    let source = "int arr[5] = {1, 2, 3, 4, 5}; int* ptr_arr[3];";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_loops() {
    let source = "int main() { int i = 0; while (i < 10) { i++; } for (int j = 0; j < 5; j++) { printf(\"%d\", j); } do { i--; } while (i > 0); return 0; }";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_conditional() {
    let source = "int main() { int x = 10; if (x > 5) { printf(\"x is greater than 5\"); } else if (x < 5) { printf(\"x is less than 5\"); } else { printf(\"x is 5\"); } return 0; }";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parsed_ast_with_switch() {
    let source = "int main() { int x = 2; switch (x) { case 1: printf(\"1\"); break; case 2: printf(\"2\"); break; default: printf(\"default\"); } return 0; }";
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.clone().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parsed_ast(&ast));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parser_ast() {
    let source = "int main() { return 0; }";
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let symbol_table = artifact.symbol_table.as_ref().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parser(ast, Some(symbol_table)));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parser_ast_with_functions() {
    let source = "int add(int a, int b) { return a + b; } int main() { return add(2, 3); }";
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let symbol_table = artifact.symbol_table.as_ref().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parser(ast, Some(symbol_table)));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_type_registry() {
    let source = "int main() { int x = 42; float y = 3.14; return x + (int)y; }";
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let type_registry = artifact.type_registry.as_ref().unwrap();

    let output = capture_stdout(|| AstDumper::dump_type_registry(ast, type_registry));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_type_registry_with_complex_types() {
    let source = "struct Point { int x; int y; }; int main() { struct Point p = {1, 2}; int *ptr = &p.x; float arr[10]; return 0; }";
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let type_registry = artifact.type_registry.as_ref().unwrap();

    let output = capture_stdout(|| AstDumper::dump_type_registry(ast, type_registry));
    insta::assert_snapshot!(output, @"");
}

#[test]
fn test_dump_parser_ast_with_designated_initializers() {
    let source = "struct Point { int x; int y; }; int main() { struct Point p = {.x = 1, .y = 2}; int arr[5] = {[1] = 10, [3] = 30}; return 0; }";
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let symbol_table = artifact.symbol_table.as_ref().unwrap();

    let output = capture_stdout(|| AstDumper::dump_parser(ast, Some(symbol_table)));
    insta::assert_snapshot!(output, @"");
}
