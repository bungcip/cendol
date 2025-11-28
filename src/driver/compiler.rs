//! Core compilation pipeline orchestration module
//!
//! This module contains the main compiler driver that orchestrates
//! the compilation pipeline including preprocessing, lexing, parsing,
//! semantic analysis, and output generation.

use std::path::Path;

use crate::ast::Ast;
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::parser::Parser;
use crate::pp::Preprocessor;
use crate::semantic::{SemanticAnalyzer, SymbolTable};
use crate::source_manager::{SourceManager, SourceId};
use target_lexicon::Triple;

use super::cli::CompileConfig;
use super::output::OutputHandler;

/// Main compiler driver
pub struct CompilerDriver {
    config: CompileConfig,
    diagnostics: DiagnosticEngine,
    source_manager: SourceManager,
    output_handler: OutputHandler,
}

impl CompilerDriver {
    /// Create a new compiler driver from CLI arguments
    pub fn new(cli: super::cli::Cli) -> Result<Self, String> {
        Ok(Self::from_config(cli.into_config()))
    }

    /// Create a new compiler driver from configuration
    pub fn from_config(config: CompileConfig) -> Self {
        CompilerDriver {
            diagnostics: DiagnosticEngine::new(),
            source_manager: SourceManager::new(),
            output_handler: OutputHandler::new(),
            config,
        }
    }

    /// Run the compilation process for all input files
    pub fn run(&mut self) -> Result<(), CompilerError> {
        // Process each input file
        for input_file in self.config.input_files.clone() {
            self.compile_file(&input_file)?;
        }

        // Report errors if any
        self.report_errors()?;

        Ok(())
    }

    /// Compile a single file through the full pipeline
    pub fn compile_file(&mut self, source_path: &Path) -> Result<(), CompilerError> {
        let source_id = self
            .source_manager
            .add_file_from_path(source_path)
            .map_err(|e| {
                CompilerError::IoError(format!("Failed to read {}: {}", source_path.display(), e))
            })?;
        self.compile_source_id(source_id)
    }

    #[cfg(test)]
    /// Compile a string of source code
    pub fn compile_source(&mut self, source: &str, filename: &str) -> Result<(), CompilerError> {
        let source_id = self.source_manager.add_file(filename, source);
        self.compile_source_id(source_id)
    }

    /// Compile a single source file, identified by its SourceId
    fn compile_source_id(&mut self, source_id: SourceId) -> Result<(), CompilerError> {
        log::debug!("Starting compilation of source_id: {}", source_id.as_u32());
        let lang_options = LangOptions {
            c11: true,
            gnu_mode: false,
            ms_extensions: false,
        };
        let target_triple = Triple::host();

        // 2. Preprocessing phase
        let pp_tokens = {
            let mut preprocessor = Preprocessor::new(
                &mut self.source_manager,
                &mut self.diagnostics,
                lang_options.clone(),
                target_triple.clone(),
                &self.config.preprocessor,
            );
            match preprocessor.process(source_id, &self.config.preprocessor) {
                Ok(t) => t,
                Err(e) => {
                    if self.diagnostics.has_errors() {
                        return Ok(());
                    } else {
                        return Err(CompilerError::PreprocessorError(format!("Preprocessing failed: {:?}", e)));
                    }
                }
            }
        };
        if self.diagnostics.has_errors() {
            return Ok(());
        }
        if self.config.preprocess_only {
            self.output_handler.dump_preprocessed_output(&pp_tokens, self.config.suppress_line_markers, &self.source_manager)?;
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
            lexer.tokenize_all()
        };
        if self.diagnostics.has_errors() {
            return Ok(());
        }

        // 4. Parsing phase
        let mut ast = {
            let mut temp_ast = Ast::new();
            {
                let mut parser = Parser::new(&tokens, &mut temp_ast, &mut self.diagnostics);
                if let Err(e) = parser.parse_translation_unit() {
                    self.diagnostics.report_parse_error(e);
                }
            }
            temp_ast
        };
        if self.diagnostics.has_errors() {
            return Ok(());
        }
        if self.config.dump_parser {
            self.output_handler.dump_parser(&ast);
            return Ok(());
        }

        // 5. Semantic analysis phase
        let symbol_table = {
            let mut analyzer = SemanticAnalyzer::new(&mut ast, &mut self.diagnostics);
            let _semantic_output = analyzer.analyze();
            let mut new_table = SymbolTable::new();
            std::mem::swap(&mut new_table, &mut analyzer.symbol_table);
            new_table
        };
        if self.diagnostics.has_errors() {
            return Ok(());
        }

        // 6. AST dumping (if requested)
        if self.config.dump_ast {
            self.output_handler.dump_ast(
                &ast,
                &symbol_table,
                &mut self.diagnostics,
                &mut self.source_manager,
                &lang_options,
                &target_triple,
                &self.config,
            )?;
        }

        Ok(())
    }

    /// Report any accumulated errors
    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            let formatter = crate::diagnostic::ErrorFormatter::default();
            formatter.print_diagnostics(self.diagnostics.diagnostics(), &self.source_manager);
        }
        Ok(())
    }

    /// Check if any errors were reported
    pub fn has_errors(&self) -> bool {
        self.diagnostics.has_errors()
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