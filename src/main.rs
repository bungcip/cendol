use cendol::codegen::CodeGen;
use cendol::error::{Report, report};
use cendol::file::FileManager;
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
    if let Err(report_data) = run() {
        report(&report_data);
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
fn run() -> Result<(), Report> {
    let cli = Cli::parse();

    if cli.verbose {
        todo!("Verbose output");
    }

    if cli.wall {
        todo!("Enable all warnings");
    }

    let input = fs::read_to_string(&cli.input_file).expect("Failed to read input file");

    let mut file_manager = FileManager::new();
    file_manager.add_include_path("/usr/include");
    file_manager.add_include_path("/usr/include/x86_64-linux-gnu");
    file_manager.add_include_path("/usr/lib/gcc/x86_64-linux-gnu/11/include");

    for path in cli.include_path {
        file_manager.add_include_path(&path);
    }

    let mut preprocessor = Preprocessor::new(file_manager);

    for def in cli.define {
        if let Err(err) = preprocessor.define(&def) {
            return Err(Report::new(err.to_string(), None, None));
        }
    }

    // if cli.preprocess_only {
    if cli.preprocess_only {
        let output = match preprocessor.preprocess(&input, &cli.input_file) {
            Ok(output) => output,
            Err(err) => return Err(Report::new(err.to_string(), None, None)),
        };
        if let Some(output_file) = cli.output_file {
            fs::write(output_file, format!("{:?}", output))
                .expect("Failed to write to output file");
        } else {
            println!("{:?}", output);
        }
        return Ok(());
    }

    let tokens = match preprocessor.preprocess(&input, &cli.input_file) {
        Ok(tokens) => tokens,
        Err(err) => return Err(Report::new(err.to_string(), None, None)),
    };

    let mut parser = match Parser::new(tokens) {
        Ok(parser) => parser,
        Err(err) => return Err(Report::new(err.to_string(), Some(cli.input_file), None)),
    };
    let ast = match parser.parse() {
        Ok(ast) => ast,
        Err(err) => {
            let (msg, location) = match err {
                cendol::parser::error::ParserError::UnexpectedToken(tok) => {
                    ("Unexpected token".to_string(), Some(tok.location))
                }
                cendol::parser::error::ParserError::UnexpectedEof => {
                    ("Unexpected EOF".to_string(), None)
                }
            };

            let (path, loc) = if let Some(location) = location {
                let path = preprocessor
                    .file_manager()
                    .get_path(location.file)
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string();
                (Some(path), Some((location.line as usize, 1)))
            } else {
                (Some(cli.input_file.clone()), None)
            };

            return Err(Report::new(msg, path, loc));
        }
    };

    let codegen = CodeGen::new();
    let object_bytes = match codegen.compile(ast) {
        Ok(bytes) => bytes,
        Err(err) => return Err(Report::new(err.to_string(), None, None)),
    };

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
