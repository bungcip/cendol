use cendol::codegen::codegen::CodeGen;
use cendol::parser::parser::Parser;
use cendol::preprocessor::preprocessor::Preprocessor;
use std::env;
use std::fs;
use std::io::Write;
use std::process::Command;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <input.c>", args[0]);
        return;
    }

    let input_filename = &args[1];
    let input = fs::read_to_string(input_filename).expect("Failed to read input file");

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
