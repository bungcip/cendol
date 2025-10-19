use cendol::codegen::codegen::CodeGen;
use cendol::parser::parser::Parser;
use cendol::preprocessor::preprocessor::Preprocessor;
use clap::Parser as ClapParser;
use std::fs;
use std::io::Write;
use std::process::Command;

#[derive(ClapParser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// The input C file
    #[arg()]
    input_file: String,
}

fn main() {
    let cli = Cli::parse();

    let input = fs::read_to_string(&cli.input_file).expect("Failed to read input file");

    let mut preprocessor = Preprocessor::new();
    let tokens = preprocessor.preprocess(&input).unwrap();

    let mut parser = Parser::new(tokens).unwrap();
    let ast = parser.parse().unwrap();

    let codegen = CodeGen::new();
    let object_bytes = codegen.compile(ast).unwrap();

    let mut object_file = fs::File::create("a.o").expect("Failed to create object file");
    object_file
        .write_all(&object_bytes)
        .expect("Failed to write to object file");

    Command::new("cc")
        .arg("a.o")
        .arg("-o")
        .arg("a.out")
        .status()
        .expect("Failed to link");
}
