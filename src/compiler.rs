use crate::error::Report;
use crate::file::{self, FileId, FileManager};
use crate::preprocessor::Preprocessor;
use crate::source::SourceSpan;
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

    /// Dump untyped AST
    #[arg(long)]
    pub dump_untyped_ast: bool,
}

use crate::codegen::CodeGen;
use crate::dumper::Dumper;
use crate::logger::Logger;
use crate::parser::Parser;
use crate::parser::error::ParserError;
use crate::preprocessor::token::{DirectiveKind, Token, TokenKind};
use crate::semantic::{SemaOutput, SemanticAnalyzer};
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

pub struct Compiler {
    fm: FileManager,
    logger: Logger,
    cli: Cli,
    working_dir: PathBuf,
}

#[derive(Debug)]
pub struct CompilerError {
    pub reports: Vec<Report>,
}

impl CompilerError {
    pub fn new(reports: Vec<Report>) -> Self {
        Self { reports }
    }
    pub fn semantic_error() -> Self { // Add this associated function
        Self { reports: vec![] }
    }
}

impl Compiler {
    pub fn new(cli: Cli, working_dir: Option<PathBuf>) -> Self {
        let logger = Logger::new(cli.verbose);
        let mut fm = FileManager::new();
        let working_dir = working_dir.unwrap_or_else(|| std::env::current_dir().unwrap());

        fm.add_include_path("/usr/include");
        fm.add_include_path("/usr/include/x86_64-linux-gnu");
        fm.add_include_path("/usr/lib/gcc/x86_64-linux-gnu/11/include");
        fm.add_include_path("/usr/local/include");

        for path in &cli.include_path {
            fm.add_include_path(path);
        }

        Self {
            fm,
            logger,
            cli,
            working_dir,
        }
    }

    pub fn print_diagnostic(&self, reports: &[Report]) {
        for r in reports {
            crate::error::report(r, &self.fm);
        }
    }

    /// ignore input file from CLI and use this filename & content
    pub fn run_virtual_file(&mut self, path: &str, content: &str) -> Result<(), CompilerError> {
        let file_id = match self.fm.register_file(path, content) {
            Ok(file_id) => file_id,
            Err(err) => {
                let report = Report::err(err.to_string(), None);
                return Err(CompilerError::new(vec![report]));
            }
        };

        self.compile(file_id)
    }

    /// drive compiler proses from cli
    pub fn run(&mut self) -> Result<(), CompilerError> {
        self.logger.log("Verbose output enabled");

        let result = if self.cli.input_file == "-" {
            self.fm.open("<stdin>")
        } else {
            self.fm.open(&self.cli.input_file)
        };

        let file_id = match result {
            Ok(file_id) => file_id,
            Err(err) => {
                let report = Report::err(err.to_string(), None);
                return Err(CompilerError::new(vec![report]));
            }
        };

        self.compile(file_id)
    }

    /// drive compiler proses from cli
    fn compile(&mut self, file_id: FileId) -> Result<(), CompilerError> {
        self.logger.log("Verbose output enabled");

        let mut preprocessor = Preprocessor::new();

        for def in &self.cli.define {
            if let Err(err) = preprocessor.define(&mut self.fm, def) {
                let span = err.span();
                let report = Report::err(err.to_string(), span);
                return Err(CompilerError::new(vec![report]));
            }
        }

        if self.cli.preprocess_only {
            let output = match preprocessor.preprocess(&mut self.fm, file_id) {
                Ok(output) => output,
                Err(err) => {
                    let span = err.span();
                    let report = Report::err(err.to_string(), span);
                    return Err(CompilerError::new(vec![report]));
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

        let tokens = match preprocessor.preprocess(&mut self.fm, file_id) {
            Ok(tokens) => tokens,
            Err(err) => {
                let span = err.span();
                let report = Report::err(err.to_string(), span);
                return Err(CompilerError::new(vec![report]));
            }
        };

        let mut parser = match Parser::new(tokens) {
            Ok(parser) => parser,
            Err(err) => {
                let report = Report::err(err.to_string(), Some(err.span()));
                return Err(CompilerError::new(vec![report]));
            }
        };
        let (ast, scopes) = match parser.parse() {
            Ok(result) => result,
            Err(err) => {
                let span = err.span();
                let msg = err.to_string();
                let report = Report::err(msg, Some(span));
                return Err(CompilerError::new(vec![report]));
            }
        };

        if self.cli.dump_untyped_ast {
            let mut dumper = Dumper::new();
            dumper.dump(&ast);
            return Ok(());
        }

        // Perform semantic analysis
        let semantic_analyzer_instance = SemanticAnalyzer::with_builtins();
        let SemaOutput(typed_ast, warnings, semantic_analyzer) =
            match semantic_analyzer_instance.analyze(ast, scopes) {
                Ok(output) => {
                    self.logger.log("Semantic analysis passed");
                    output
                }
                Err(errors) => {
                    let mut reports = vec![];
                    for (error, span) in errors {
                        let report_data = Report::err(error.to_string(), Some(span));
                        reports.push(report_data);
                    }
                    self.print_diagnostic(&reports);
                    return Err(CompilerError::new(reports));
                }
            };

        for (warning, span) in &warnings {
            // TODO: return it as Compiler Output
            let report_data = Report::warn(warning.to_string(), Some(*span));
            crate::error::report(&report_data, &self.fm);
        }

        if self.cli.wall && !warnings.is_empty() {
            let report = Report::err("Warnings treated as errors".to_string(), None);
            return Err(CompilerError::new(vec![report]));
        }

        let codegen = CodeGen::new(semantic_analyzer); // Remove mut, as codegen is moved into compile
        let object_bytes = match codegen.compile(typed_ast) { // Call compile with updated signature
            Ok(bytes) => bytes,
            Err(err) => {
                let report = Report::err(err.to_string(), None);
                return Err(CompilerError::new(vec![report]));
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

        if self.cli.compile_only == false {
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
            } else if let TokenKind::String(s) = &token.kind {
                result.push('"');
                result.push_str(s);
                result.push('"');
            } else {
                result.push_str(&token.to_string());
            }

            i += 1;
        }

        result
    }
}
