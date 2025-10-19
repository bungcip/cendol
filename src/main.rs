use cendol::codegen::CodeGen;
use cendol::error::{Error, Report, report};
use cendol::parser::Parser;
use cendol::preprocessor::Preprocessor;
use clap::Parser as ClapParser;
use std::fs;
use std::io::Write;
use std::process::{Command, exit};

/// Command-line arguments for the C-like compiler.
#[derive(ClapParser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// The input C file
    #[arg()]
    input_file: String,

    /// Output file
    #[arg(short, long)]
    output_file: Option<String>,

    /// Compile only, do not link
    #[arg(short = 'c')]
    compile_only: bool,

    /// Preprocess only
    #[arg(short = 'E')]
    preprocess_only: bool,

    /// Define a macro
    #[arg(short = 'D', long)]
    define: Vec<String>,

    /// Add an include path
    #[arg(short = 'I', long)]
    include_path: Vec<String>,

    /// Enable all warnings
    #[arg(long)]
    wall: bool,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,
}

/// The main entry point for the application.
///
/// Parses command-line arguments and runs the compiler.
fn main() {
    if let Err(err) = run() {
        report(&Report::new(err.to_string(), None, None));
        exit(1);
    }
}

/// Runs the compiler.
///
/// This function reads the input file, preprocesses it, parses the tokens,
/// generates code, and optionally links the output.
///
/// # Returns
///
/// A `Result` which is `Ok` on success or an `Error` on failure.
fn run() -> Result<(), Error> {
    let cli = Cli::parse();

    if cli.verbose {
        todo!("Verbose output");
    }

    if cli.wall {
        todo!("Enable all warnings");
    }

    let input = fs::read_to_string(&cli.input_file).expect("Failed to read input file");

    let mut preprocessor = Preprocessor::new();

    for def in cli.define {
        preprocessor.define(&def)?;
    }

    for path in cli.include_path {
        todo!("Add include path: {}", path);
    }

    if cli.preprocess_only {
        let output = preprocessor.preprocess(&input)?;
        if let Some(output_file) = cli.output_file {
            fs::write(output_file, format!("{:?}", output))
                .expect("Failed to write to output file");
        } else {
            println!("{:?}", output);
        }
        return Ok(());
    }

    let tokens = preprocessor.preprocess(&input)?;

    let mut parser = Parser::new(tokens)?;
    let ast = parser.parse()?;

    let codegen = CodeGen::new();
    let object_bytes = codegen.compile(ast)?;

    let object_filename = if cli.compile_only {
        cli.output_file.as_deref().unwrap_or("a.o").to_string()
    } else {
        "a.o".to_string()
    };

    let mut object_file = fs::File::create(&object_filename).expect("Failed to create object file");
    object_file
        .write_all(&object_bytes)
        .expect("Failed to write to object file");

    if !cli.compile_only {
        let output_filename = cli.output_file.unwrap_or_else(|| "a.out".to_string());
        Command::new("cc")
            .arg(&object_filename)
            .arg("-o")
            .arg(&output_filename)
            .status()
            .expect("Failed to link");
    }

    Ok(())
}
