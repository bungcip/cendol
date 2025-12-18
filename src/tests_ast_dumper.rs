use crate::driver::cli::Cli;
use crate::driver::compiler::CompilerDriver;
use clap::Parser;
use std::fs;
use tempfile::tempdir;

fn setup() {
    // Suppress logger output during tests
    let _ = env_logger::builder().is_test(true).try_init();
}

fn run_compiler_and_dump_ast(
    input_path: &str,
    output_path: &str,
    dump_ast: bool,
) -> Result<(String, CompilerDriver), String> {
    setup();

    let cli_args = if dump_ast {
        vec!["cendol", "--dump-ast", "-o", output_path, input_path]
    } else {
        vec!["cendol", "-o", output_path, input_path]
    };

    let cli = Cli::try_parse_from(cli_args).map_err(|e| e.to_string())?;
    let mut driver = CompilerDriver::from_config(cli.into_config());
    driver.run().map_err(|e| e.to_string())?;

    let output = fs::read_to_string(output_path).map_err(|e| e.to_string())?;
    Ok((output, driver))
}

#[test]
fn test_ast_dumper_simple_expression() {
    let dir = tempdir().unwrap();
    let input_path = dir.path().join("test_simple_expression.c");
    let output_path = dir.path().join("ast_dump_simple_expression.html");
    let source_code = "int main() { return 1 + 2; }";

    fs::write(&input_path, source_code).unwrap();

    let result = run_compiler_and_dump_ast(input_path.to_str().unwrap(), output_path.to_str().unwrap(), true);

    assert!(result.is_ok(), "Compiler driver failed: {:?}", result.as_ref().err());
    let (html_output, _driver) = result.unwrap();

    // Use insta to snapshot the relevant part of the HTML output
    let relevant_html = html_output
        .split("<section id=\"ast-section\">")
        .nth(1)
        .unwrap_or("")
        .split("</section>")
        .next()
        .unwrap_or("");

    insta::assert_snapshot!(relevant_html);
}
