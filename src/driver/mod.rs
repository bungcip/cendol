// Compiler driver module

use std::path::{Path, PathBuf};
use std::fs;
use clap::{Parser as CliParser, Args};
use symbol_table::GlobalSymbol as Symbol;

use crate::ast::{Ast, Node, NodeKind, FunctionDefData, Declarator, TypeQualifiers};
use crate::semantic::SemanticAnalyzer;
use crate::diagnostic::{DiagnosticEngine, SemanticOutput};
use crate::ast_dumper::{AstDumper, DumpConfig};
use crate::source_manager::{SourceManager, SourceId, SourceSpan, SourceLoc};
use crate::lang_options::LangOptions;
use crate::preprocessor::{Preprocessor, PreprocessorConfig, PreprocessorError};
use crate::parser::Parser;

// Remove duplicate PreprocessorConfig definition
use std::cell::Cell;

/// CLI interface using clap
#[derive(CliParser, Debug)]
#[clap(name = "cendol", about = "C11 Compiler written in Rust")]
pub struct Cli {
    /// Input C source files
    #[clap(value_parser, required = true)]
    pub input_files: Vec<PathBuf>,

    /// Output file for AST dump
    #[clap(short, long, value_name = "FILE")]
    pub output: Option<PathBuf>,

    /// Enable verbose diagnostic output
    #[clap(short, long)]
    pub verbose: bool,

    /// Generate HTML AST dump
    #[clap(long)]
    pub dump_ast: bool,

    /// Preprocessor options
    #[clap(flatten)]
    pub preprocessor: PreprocessorOptions,

    /// Include search paths
    #[clap(short = 'I', long = "include-path", value_name = "DIR", action = clap::ArgAction::Append)]
    pub include_paths: Vec<PathBuf>,

    /// Preprocessor macro definitions
    #[clap(short = 'D', long = "define", value_name = "NAME[=VALUE]", action = clap::ArgAction::Append)]
    pub defines: Vec<String>,
}

#[derive(Args, Debug)]
pub struct PreprocessorOptions {
    /// Maximum include depth
    #[clap(long, default_value = "100")]
    pub max_include_depth: usize,
}

/// Configuration for compilation
#[derive(Debug)]
pub struct CompileConfig {
    pub input_files: Vec<PathBuf>,
    pub output_path: Option<PathBuf>,
    pub dump_ast: bool,
    pub verbose: bool,
    pub preprocessor: PreprocessorConfig,
    pub include_paths: Vec<PathBuf>,
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
}

// Use the PreprocessorConfig from the preprocessor module

/// Main compiler driver
pub struct CompilerDriver {
    config: CompileConfig,
    diagnostics: DiagnosticEngine,
    source_manager: SourceManager,
}

impl CompilerDriver {
    pub fn new(cli: Cli) -> Result<Self, String> {
        // Parse defines
        let defines = cli.defines.iter()
            .map(|def| {
                if let Some(eq_pos) = def.find('=') {
                    let name = def[..eq_pos].to_string();
                    let value = Some(def[eq_pos + 1..].to_string());
                    (name, value)
                } else {
                    (def.clone(), None)
                }
            })
            .collect();

        let config = CompileConfig {
            input_files: cli.input_files,
            output_path: cli.output,
            dump_ast: cli.dump_ast,
            verbose: cli.verbose,
            include_paths: cli.include_paths,
            defines,
            preprocessor: PreprocessorConfig {
                max_include_depth: cli.preprocessor.max_include_depth,
                system_include_paths: Vec::new(), // TODO: Add system include paths
            },
        };

        Ok(CompilerDriver {
            config,
            diagnostics: DiagnosticEngine::new(),
            source_manager: SourceManager::new(),
        })
    }

    pub fn run(&mut self) -> Result<(), CompilerError> {
        // Process each input file
        for input_file in self.config.input_files.clone() {
            self.compile_file(&input_file)?;
        }

        // Report errors if any
        self.report_errors()?;

        Ok(())
    }

    fn compile_file(&mut self, source_path: &Path) -> Result<(), CompilerError> {
        // 1. Read source file
        let content = fs::read_to_string(source_path)
            .map_err(|e| CompilerError::IoError(format!("Failed to read {}: {}", source_path.display(), e)))?;

        let source_id = self.source_manager.add_file(source_path.to_str().unwrap(), &content);

        // 2. Preprocessing phase
        let mut preprocessor = Preprocessor::new(
            &mut self.source_manager,
            &self.diagnostics,
            LangOptions { c11: true, gnu_mode: false, ms_extensions: false },
            target_lexicon::Triple::host(),
            &self.config.preprocessor,
        );
        let pp_tokens = preprocessor.process(source_id, &self.config.preprocessor)
            .map_err(|e| CompilerError::PreprocessorError(format!("Preprocessing failed: {:?}", e)))?;

        // 3. Lexing phase
        let lexer_diag = DiagnosticEngine::new();
        let target_triple = target_lexicon::Triple::host();
        let mut lexer = crate::lexer::Lexer::new(
            &self.source_manager,
            &lexer_diag,
            &LangOptions { c11: true, gnu_mode: false, ms_extensions: false },
            &target_triple,
            &pp_tokens,
        );
        let tokens = lexer.tokenize_all();

        // 4. Parsing phase
        let mut ast = Ast::new();
        let mut compiler_diag = DiagnosticEngine::new();
        let mut parser = Parser::new(&tokens, &mut ast, &mut compiler_diag);
        let translation_unit = parser.parse_translation_unit()
            .map_err(|e| CompilerError::ParserError(format!("Parsing failed: {:?}", e)))?;

        // Check for parser errors and merge them into main diagnostics
        for diag in compiler_diag.diagnostics() {
            self.diagnostics.report_diagnostic(diag.clone());
        }

        // 5. Semantic analysis phase
        let mut analyzer = SemanticAnalyzer::new(&mut ast, &mut compiler_diag);
        let semantic_output = analyzer.analyze();

        // Merge semantic diagnostics into main diagnostics
        for diag in semantic_output.diagnostics {
            self.diagnostics.report_diagnostic(diag);
        }

        // 6. AST dumping (if requested)
        if self.config.dump_ast {
            let output_path = self.config.output_path.clone()
                .unwrap_or_else(|| PathBuf::from("ast_dump.html"));
            let dump_config = DumpConfig {
                pretty_print: true,
                include_source: true,
                max_depth: None,
                output_path: output_path.clone(),
            };
            let symbol_table = &analyzer.symbol_table;
            let dumper = AstDumper::new(&ast, symbol_table, &self.diagnostics, dump_config);
            let html = dumper.generate_html()
                .map_err(|e| CompilerError::AstDumpError(format!("HTML generation error: {:?}", e)))?;

            fs::write(&output_path, html)
                .map_err(|e| CompilerError::IoError(format!("Failed to write AST dump: {}", e)))?;
        }

        Ok(())
    }

    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            let formatter = crate::diagnostic::ErrorFormatter::default();

            for diag in self.diagnostics.diagnostics() {
                if diag.level == crate::diagnostic::DiagnosticLevel::Error {
                    let formatted = formatter.format_diagnostic(diag, &self.source_manager);
                    eprintln!("{}", formatted);
                }
            }

            return Err(CompilerError::CompilationFailed);
        }

        Ok(())
    }
}

/// Error types for the compiler driver
#[derive(Debug, thiserror::Error)]
pub enum CompilerError {
    #[error("I/O error: {0}")]
    IoError(String),
    #[error("Preprocessing failed: {0}")]
    PreprocessorError(String),
    #[error("Lexing failed: {0}")]
    LexerError(String),
    #[error("Parsing failed: {0}")]
    ParserError(String),
    #[error("Semantic analysis failed: {0}")]
    SemanticError(String),
    #[error("AST dump failed: {0}")]
    AstDumpError(String),
    #[error("Compilation failed due to errors")]
    CompilationFailed,
}
