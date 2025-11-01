use crate::error::Report;
use crate::file::FileManager;
use crate::preprocessor::Preprocessor;
use clap::Parser as ClapParser;

/// Command-line arguments for the C-like compiler.
#[derive(ClapParser, Default)]
#[command(version, about, long_about = None)]
pub struct Cli {
    /// The input C file
    #[arg()]
    pub input_file: String,

    /// Output file
    #[arg(short, long)]
    pub output_file: Option<String>,

    /// Compile only, do not link
    #[arg(short = 'c')]
    pub compile_only: bool,

    /// Preprocess only
    #[arg(short = 'E')]
    pub preprocess_only: bool,

    /// Define a macro
    #[arg(short = 'D', long)]
    pub define: Vec<String>,

    /// Add an include path
    #[arg(short = 'I', long)]
    pub include_path: Vec<String>,

    /// Enable all warnings
    #[arg(long)]
    pub wall: bool,

    /// Verbose output
    #[arg(short, long)]
    pub verbose: bool,
}

use crate::codegen::CodeGen;
use crate::logger::Logger;
use crate::parser::Parser;
use crate::parser::error::ParserError;
use crate::preprocessor::token::{DirectiveKind, Token, TokenKind};
use crate::semantic::SemanticAnalyzer;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

pub struct Compiler {
    preprocessor: Preprocessor,
    logger: Logger,
    cli: Cli,
    working_dir: PathBuf,
}

impl Compiler {
    pub fn new(cli: Cli, working_dir: Option<PathBuf>) -> Self {
        let logger = Logger::new(cli.verbose);
        let mut file_manager = FileManager::new();
        let working_dir = working_dir.unwrap_or_else(|| std::env::current_dir().unwrap());

        file_manager.add_include_path("/usr/include");
        file_manager.add_include_path("/usr/include/x86_64-linux-gnu");
        file_manager.add_include_path("/usr/lib/gcc/x86_64-linux-gnu/11/include");
        file_manager.add_include_path("/usr/local/include");

        for path in &cli.include_path {
            file_manager.add_include_path(path);
        }

        let preprocessor = Preprocessor::new(file_manager);

        Self {
            preprocessor,
            logger,
            cli,
            working_dir,
        }
    }

    pub fn compile(&mut self) -> Result<(), Report> {
        self.logger.log("Verbose output enabled");

        let (input, filename) = if self.cli.input_file == "-" {
            (
                std::io::read_to_string(std::io::stdin()).expect("Failed to read from stdin"),
                "<stdin>",
            )
        } else {
            (
                fs::read_to_string(&self.cli.input_file).expect("Failed to read input file"),
                self.cli.input_file.as_str(),
            )
        };

        for def in &self.cli.define {
            if let Err(err) = self.preprocessor.define(def) {
                let report = Report::new(err.to_string(), None, None, self.cli.verbose, false);
                return Err(report);
            }
        }

        if self.cli.preprocess_only {
            let output = match self.preprocessor.preprocess(&input, filename) {
                Ok(output) => output,
                Err(err) => {
                    let report = Report::new(err.to_string(), None, None, self.cli.verbose, false);
                    return Err(report);
                }
            };

            if let Some(output_file) = &self.cli.output_file {
                let formatted_output = self.format_tokens(&output);
                fs::write(output_file, formatted_output).expect("Failed to write to output file");
            } else {
                let formatted_output = self.format_tokens(&output);
                print!("{}", formatted_output);
            }
            return Ok(());
        }

        let tokens = match self.preprocessor.preprocess(&input, filename) {
            Ok(tokens) => tokens,
            Err(err) => {
                let report = Report::new(err.to_string(), None, None, self.cli.verbose, false);
                return Err(report);
            }
        };

        let mut parser = match Parser::new(tokens) {
            Ok(parser) => parser,
            Err(err) => {
                let report = Report::new(err.to_string(), None, None, self.cli.verbose, false);
                return Err(report);
            }
        };
        let ast = match parser.parse() {
            Ok(ast) => ast,
            Err(err) => {
                let (msg, location) = match err {
                    ParserError::UnexpectedToken(tok) => {
                        ("Unexpected token".to_string(), Some(tok.span))
                    }
                    ParserError::UnexpectedEof => ("Unexpected EOF".to_string(), None),
                };

                let (path, span) = if let Some(location) = location {
                    let path = self
                        .preprocessor
                        .file_manager()
                        .get_path(location.file_id)
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .to_string();
                    (Some(path), Some(location))
                } else {
                    (Some(filename.to_string()), None)
                };

                let report = Report::new(msg, path, span, self.cli.verbose, false);
                return Err(report);
            }
        };

        // Perform semantic analysis
        let semantic_analyzer = SemanticAnalyzer::with_builtins();
        let (typed_ast, warnings, semantic_analyzer) =
            match semantic_analyzer.analyze(ast.clone(), filename) {
                Ok((typed_ast, warnings, semantic_analyzer)) => {
                    self.logger.log("Semantic analysis passed");
                    (typed_ast, warnings, semantic_analyzer)
                }
                Err(errors) => {
                    for (error, file, span) in errors {
                        let report_data = Report::new(
                            error.to_string(),
                            Some(file.clone()),
                            Some(span),
                            self.cli.verbose,
                            false,
                        );
                        crate::error::report(&report_data);
                    }
                    return Err(Report::new(
                        "Semantic errors found".to_string(),
                        Some(filename.to_string()),
                        None,
                        self.cli.verbose,
                        false,
                    ));
                }
            };

        for (warning, file, span) in &warnings {
            let report_data = Report::new(
                warning.to_string(),
                Some(file.clone()),
                Some(*span),
                self.cli.verbose,
                true,
            );
            crate::error::report(&report_data);
        }

        if self.cli.wall && !warnings.is_empty() {
            return Err(Report::new(
                "Warnings treated as errors".to_string(),
                Some(filename.to_string()),
                None,
                self.cli.verbose,
                false,
            ));
        }

        let mut codegen = CodeGen::new();
        codegen.enum_constants = semantic_analyzer.enum_constants;
        let object_bytes = match codegen.compile(typed_ast) {
            Ok(bytes) => bytes,
            Err(err) => {
                let mut report = Report::new(
                    err.to_string(),
                    Some(filename.to_string()),
                    None,
                    self.cli.verbose,
                    false,
                );
                report.verbose = self.cli.verbose;
                return Err(report);
            }
        };

        let object_filename = if self.cli.compile_only {
            self.cli.output_file.as_deref().unwrap_or("a.o").to_string()
        } else {
            "a.o".to_string()
        };

        let mut object_file = fs::File::create(self.working_dir.join(&object_filename))
            .expect("Failed to create object file");
        object_file
            .write_all(&object_bytes)
            .expect("Failed to write to object file");

        if !self.cli.compile_only {
            let output_filename = self
                .cli
                .output_file
                .clone()
                .unwrap_or_else(|| "a.out".to_string());
            Command::new("cc")
                .current_dir(&self.working_dir)
                .arg(&object_filename)
                .arg("-o")
                .arg(&output_filename)
                .status()
                .expect("Failed to link");
        }

        Ok(())
    }

    /// Formats tokens for output, handling line directives specially.
    fn format_tokens(&self, tokens: &[Token]) -> String {
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
}
