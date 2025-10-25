use cendol::codegen::CodeGen;
use cendol::error::{Report, report};
use cendol::file::FileManager;
use cendol::logger::Logger;
use cendol::parser::Parser;
use cendol::preprocessor::{
    Preprocessor,
    token::{DirectiveKind, Token, TokenKind},
};
use cendol::semantic::SemanticAnalyzer;
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

/// Formats tokens for output, handling line directives specially.
fn format_tokens(tokens: &[Token]) -> String {
    let mut result = String::new();
    let mut i = 0;

    while i < tokens.len() {
        let token = &tokens[i];

        // Check if this is a line directive
        if let TokenKind::Directive(DirectiveKind::Line) = token.kind {
            // Look ahead for number and string tokens
            if i + 2 < tokens.len()
                && let (TokenKind::Number(line), TokenKind::String(filename)) =
                    (&tokens[i + 1].kind, &tokens[i + 2].kind)
            {
                result.push_str(&format!("# {} \"{}\"\n", line, filename));
                i += 3; // Skip the number and string tokens
                continue;
            }
        }

        // Handle whitespace normalization
        if let TokenKind::Whitespace(_) = token.kind {
            // Convert any whitespace to a single space
            result.push(' ');
        } else if let TokenKind::Newline = token.kind {
            result.push('\n');
        } else if let TokenKind::Comment(_) = token.kind {
            // Skip comments in output
            i += 1;
            continue;
        } else {
            result.push_str(&token.to_string());
        }

        i += 1;
    }

    result
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

    let logger = Logger::new(cli.verbose);
    logger.log("Verbose output enabled");

    if cli.wall {
        todo!("Enable all warnings");
    }

    let input = fs::read_to_string(&cli.input_file).expect("Failed to read input file");

    let mut file_manager = FileManager::new();
    file_manager.add_include_path("/usr/include");
    file_manager.add_include_path("/usr/include/x86_64-linux-gnu");
    file_manager.add_include_path("/usr/lib/gcc/x86_64-linux-gnu/11/include");
    file_manager.add_include_path("/usr/local/include");

    for path in cli.include_path {
        file_manager.add_include_path(&path);
    }

    let mut preprocessor = Preprocessor::new(file_manager);

    for def in cli.define {
        if let Err(err) = preprocessor.define(&def) {
            let mut report = Report::new(err.to_string(), None, None);
            report.verbose = cli.verbose;
            return Err(report);
        }
    }

    // if cli.preprocess_only {
    if cli.preprocess_only {
        let output = match preprocessor.preprocess(&input, &cli.input_file) {
            Ok(output) => output,
            Err(err) => {
                let mut report = Report::new(err.to_string(), None, None);
                report.verbose = cli.verbose;
                return Err(report);
            }
        };

        if let Some(output_file) = cli.output_file {
            let formatted_output = format_tokens(&output);
            fs::write(output_file, formatted_output).expect("Failed to write to output file");
        } else {
            let formatted_output = format_tokens(&output);
            print!("{}", formatted_output);
        }
        return Ok(());
    }

    let tokens = match preprocessor.preprocess(&input, &cli.input_file) {
        Ok(tokens) => tokens,
        Err(err) => {
            let mut report = Report::new(err.to_string(), None, None);
            report.verbose = cli.verbose;
            return Err(report);
        }
    };

    let mut parser = match Parser::new(tokens, logger) {
        Ok(parser) => parser,
        Err(err) => {
            let mut report = Report::new(err.to_string(), Some(cli.input_file), None);
            report.verbose = cli.verbose;
            return Err(report);
        }
    };
    let ast = match parser.parse() {
        Ok(ast) => ast,
        Err(err) => {
            let (msg, location) = match err {
                cendol::parser::error::ParserError::UnexpectedToken(tok) => {
                    ("Unexpected token".to_string(), Some(tok.span))
                }
                cendol::parser::error::ParserError::UnexpectedEof => {
                    ("Unexpected EOF".to_string(), None)
                }
            };

            let (path, span) = if let Some(location) = location {
                let path = preprocessor
                    .file_manager()
                    .get_path(location.start.file)
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string();
                (Some(path), Some(location))
            } else {
                (Some(cli.input_file.clone()), None)
            };

            let mut report = Report::new(msg, path, span);
            report.verbose = cli.verbose;
            return Err(report);
        }
    };

    // Perform semantic analysis
    let semantic_analyzer = SemanticAnalyzer::new();
    match semantic_analyzer.analyze(ast.clone(), &cli.input_file) {
        Ok(_) => {
            logger.log("Semantic analysis passed");
        }
        Err(errors) => {
            for (error, file, span) in errors {
                let mut report_data =
                    Report::new(error.to_string(), Some(file.clone()), Some(span));
                report_data.verbose = cli.verbose;
                report(&report_data);
            }
            return Err(Report::new(
                "Semantic errors found".to_string(),
                Some(cli.input_file),
                None,
            ));
        }
    }

    let codegen = CodeGen::new();
    let object_bytes = match codegen.compile(ast) {
        Ok(bytes) => bytes,
        Err(err) => {
            let mut report = Report::new(err.to_string(), Some(cli.input_file.clone()), None);
            report.verbose = cli.verbose;
            return Err(report);
        }
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
