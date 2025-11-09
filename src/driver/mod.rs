// Compiler driver module

use clap::{Args, Parser as CliParser};
use target_lexicon::Triple;
use std::fs;
use std::path::{Path, PathBuf};
use symbol_table::GlobalSymbol as Symbol;

use crate::ast::{Ast, Declarator, FunctionDefData, Node, NodeKind, TypeQualifiers};
use crate::ast_dumper::{AstDumper, DumpConfig};
use crate::diagnostic::{DiagnosticEngine, SemanticOutput};
use crate::lang_options::LangOptions;
use crate::parser::Parser;
use crate::preprocessor::{Preprocessor, PreprocessorConfig, PreprocessorError};
use crate::semantic::{SemanticAnalyzer, SymbolTable};
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};

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

    /// Preprocess only, output preprocessed source to stdout
    #[clap(short = 'E')]
    pub preprocess_only: bool,

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
    pub preprocess_only: bool,
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
        let defines = cli
            .defines
            .iter()
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
            preprocess_only: cli.preprocess_only,
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
        let lang_options = LangOptions {
            c11: true,
            gnu_mode: false,
            ms_extensions: false,
        };
        let target_triple = Triple::host();

        // 1. Load source file through SourceManager
        let source_id = self
            .source_manager
            .add_file_from_path(source_path)
            .map_err(|e| {
                CompilerError::IoError(format!("Failed to read {}: {}", source_path.display(), e))
            })?;

        // 2. Preprocessing phase
        let pp_tokens = {
            let mut preprocessor = Preprocessor::new(
                &mut self.source_manager,
                &mut self.diagnostics,
                lang_options.clone(), // TODO: make it to just borrow
                target_triple.clone(), // TODO: make it to just borrow
                &self.config.preprocessor,
            );
            let result = preprocessor
                .process(source_id, &self.config.preprocessor)
                .map_err(|e| {
                    CompilerError::PreprocessorError(format!("Preprocessing failed: {:?}", e))
                })?;
            // Preprocessor is dropped here, releasing the borrow on diagnostics
            result
        };

        // Check for preprocessing errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // If preprocess only, dump the preprocessed output
        if self.config.preprocess_only {
            self.dump_preprocessed_output(&pp_tokens)?;
            return Ok(());
        }

        // 3. Lexing phase
        let tokens = {
            let mut lexer = crate::lexer::Lexer::new(
                &self.source_manager,
                &mut self.diagnostics,
                &lang_options,
                &target_triple,
                &pp_tokens,
            );
            let result = lexer.tokenize_all();
            // Lexer is dropped here, releasing the borrow on diagnostics
            result
        };

        // Check for lexing errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // 4. Parsing phase
        let mut ast = {
            let mut temp_ast = Ast::new();
            {
                let mut parser = Parser::new(&tokens, &mut temp_ast, &mut self.diagnostics);
                let _translation_unit = parser
                    .parse_translation_unit()
                    .map_err(|e| CompilerError::ParserError(format!("Parsing failed: {:?}", e)))?;
                // Parser is dropped here, releasing the borrow on diagnostics
            }
            // Return the AST for use in next phases
            temp_ast
        };

        // Check for parsing errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // 5. Semantic analysis phase
        let symbol_table = {
            let mut analyzer = SemanticAnalyzer::new(&mut ast, &mut self.diagnostics);
            let _semantic_output = analyzer.analyze();
            // Analyzer is dropped here, releasing the borrow on diagnostics
            // We need to restructure to get the symbol table out
            // For now, we'll create a new empty one and move the data
            let mut new_table = SymbolTable::new();
            std::mem::swap(&mut new_table, &mut analyzer.symbol_table);
            new_table
        };

        // Check for semantic analysis errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // 6. AST dumping (if requested)
        if self.config.dump_ast {
            let output_path = self
                .config
                .output_path
                .clone()
                .unwrap_or_else(|| PathBuf::from("ast_dump.html"));
            let dump_config = DumpConfig {
                pretty_print: true,
                include_source: true,
                max_depth: None,
                output_path: output_path.clone(),
            };
            let dumper = AstDumper::new(
                &ast,
                &symbol_table,
                &self.diagnostics,
                &self.source_manager,
                dump_config,
            );
            let html = dumper.generate_html().map_err(|e| {
                CompilerError::AstDumpError(format!("HTML generation error: {:?}", e))
            })?;

            fs::write(&output_path, html)
                .map_err(|e| CompilerError::IoError(format!("Failed to write AST dump: {}", e)))?;
        }

        Ok(())
    }

    fn dump_preprocessed_output(
        &self,
        pp_tokens: &[crate::preprocessor::PPToken],
    ) -> Result<(), CompilerError> {
        use std::io::Write;

        for i in 0..pp_tokens.len() {
            let token = &pp_tokens[i];
            if token.kind == crate::preprocessor::PPTokenKind::Eof {
                break;
            }

            // Get token text from source manager
            let buffer = self.source_manager.get_buffer(token.location.source_id());
            let start = token.location.offset() as usize;
            let end = start + token.length as usize;
            if end <= buffer.len() {
                let text = unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) };
                print!("{}", text);
            }

            // Print gap to next token, preserving newlines and whitespace
            if i + 1 < pp_tokens.len() {
                let next_token = &pp_tokens[i + 1];
                let next_start = if next_token.kind == crate::preprocessor::PPTokenKind::Eof {
                    buffer.len()
                } else {
                    next_token.location.offset() as usize
                };
                let gap_start = end;
                if next_start > gap_start {
                    let gap = &buffer[gap_start..next_start];
                    let gap_str = unsafe { std::str::from_utf8_unchecked(gap) };
                    print!("{}", gap_str);
                }
            }
        }
        Ok(())
    }

    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            let formatter = crate::diagnostic::ErrorFormatter::default();
            formatter.print_diagnostics(self.diagnostics.diagnostics(), &self.source_manager);
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
