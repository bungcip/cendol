//! Core compilation pipeline orchestration module
//!
//! This module contains the main compiler driver that orchestrates
//! the compilation pipeline including preprocessing, lexing, parsing,
//! semantic analysis, and output generation.

use std::path::Path;

use crate::ast::Ast;
use crate::codegen::CodeGenerator;
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::pp::Preprocessor;
use crate::semantic::{SemanticAnalyzer, SymbolTable};
use crate::source_manager::SourceManager;
use target_lexicon::Triple;

use super::cli::CompileConfig;
use super::output::{AstDumpArgs, OutputHandler};

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
        let diagnostics = DiagnosticEngine::from_warnings(&config.warnings);
        CompilerDriver {
            diagnostics,
            source_manager: SourceManager::new(),
            output_handler: OutputHandler::new(),
            config,
        }
    }

    /// Run the compilation process for all input files
    pub fn run(&mut self) -> Result<(), CompilerError> {
        // Process each input file
        for input_file in self.config.input_files.clone() {
            let (ast, _symbol_table) = self.compile_file(&input_file)?;
            if let Some(output_path) = &self.config.output_path
                && !self.config.dump_ast
            {
                let codegen = CodeGenerator::new(&ast);
                let object_file = codegen.compile().unwrap();
                
                // Write the object file to a temporary file
                let temp_object_path = format!("{}.o", output_path.display());
                std::fs::write(&temp_object_path, object_file).unwrap();
                
                // Link the object file into an executable using clang
                let status = std::process::Command::new("clang")
                    .arg(&temp_object_path)
                    .arg("-o")
                    .arg(output_path)
                    .status()
                    .expect("Failed to execute clang for linking");
                
                if !status.success() {
                    return Err(CompilerError::IoError(
                        "Failed to link object file into executable".to_string(),
                    ));
                }
                
                // Remove the temporary object file
                std::fs::remove_file(&temp_object_path).unwrap();
                
                // Set executable permissions on the output file
                use std::os::unix::fs::PermissionsExt;
                if let Ok(metadata) = std::fs::metadata(output_path) {
                    let mut permissions = metadata.permissions();
                    permissions.set_mode(0o755); // rwxr-xr-x
                    if let Err(e) = std::fs::set_permissions(output_path, permissions) {
                        eprintln!("Warning: Failed to set executable permissions: {}", e);
                    }
                }
            }
        }

        // Report errors if any
        self.report_errors()?;

        Ok(())
    }

    pub fn compile_to_ast(&mut self) -> Result<Ast, CompilerError> {
        let input_file = self.config.input_files[0].clone();
        let (ast, _) = self.compile_file(&input_file)?;
        self.report_errors()?;
        Ok(ast)
    }

    /// Compile a single file through the full pipeline
    fn compile_file(&mut self, source_path: &Path) -> Result<(Ast, SymbolTable), CompilerError> {
        log::debug!("Starting compilation of file: {}", source_path.display());
        let lang_options = LangOptions::c11();
        let target_triple = Triple::host();

        // 1. Load source file through SourceManager
        let source_id = self
            .source_manager
            .add_file_from_path(source_path)
            .map_err(|e| CompilerError::IoError(format!("Failed to read {}: {}", source_path.display(), e)))?;

        // 2. Preprocessing phase
        let pp_tokens = {
            let mut preprocessor = Preprocessor::new(
                &mut self.source_manager,
                &mut self.diagnostics,
                lang_options.clone(),  // TODO: make it to just borrow
                target_triple.clone(), // TODO: make it to just borrow
                &self.config.preprocessor,
            );

            // Preprocessor is dropped here, releasing the borrow on diagnostics
            match preprocessor.process(source_id, &self.config.preprocessor) {
                Ok(t) => t,
                Err(e) => {
                    if self.diagnostics.has_errors() {
                        return Err(CompilerError::CompilationFailed);
                    } else {
                        return Err(CompilerError::PreprocessorError(format!(
                            "Preprocessing failed: {:?}",
                            e
                        )));
                    }
                }
            }
        };

        // Check for preprocessing errors and stop if any
        if self.diagnostics.has_errors() {
            return Err(CompilerError::CompilationFailed);
        }

        // If preprocess only, dump the preprocessed output
        if self.config.preprocess_only {
            self.output_handler.dump_preprocessed_output(
                &pp_tokens,
                self.config.suppress_line_markers,
                &self.source_manager,
            )?;
            return Ok((Ast::new(), SymbolTable::new()));
        }

        // 3. Lexing phase
        let tokens = {
            let mut lexer = Lexer::new(&pp_tokens);

            // Lexer is dropped here, releasing the borrow on diagnostics
            lexer.tokenize_all()
        };

        // Check for lexing errors and stop if any
        if self.diagnostics.has_errors() {
            return Err(CompilerError::CompilationFailed);
        }

        // 4. Parsing phase
        let mut ast = {
            let mut temp_ast = Ast::new();
            {
                let mut parser = Parser::new(&tokens, &mut temp_ast, &mut self.diagnostics);
                if let Err(e) = parser.parse_translation_unit() {
                    // Report the error but continue with empty AST
                    self.diagnostics.report_parse_error(e);
                }
                // Parser is dropped here, releasing the borrow on diagnostics
            }
            // Return the AST for use in next phases
            temp_ast
        };

        // Check for parsing errors and stop if any
        if self.diagnostics.has_errors() {
            return Err(CompilerError::CompilationFailed);
        }

        // print parser AST to check
        if self.config.dump_parser {
            self.output_handler.dump_parser(&ast);
            // This is a special case. We want to stop after dumping the parser output.
            // We'll return an empty symbol table.
            return Ok((ast, SymbolTable::new()));
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
            return Err(CompilerError::CompilationFailed);
        }

        // 6. AST dumping (if requested)
        if self.config.dump_ast {
            let mut args = AstDumpArgs {
                ast: &ast,
                symbol_table: &symbol_table,
                diagnostics: &mut self.diagnostics,
                source_manager: &mut self.source_manager,
                lang_options: &lang_options,
                target_triple: &target_triple,
            };
            self.output_handler.dump_ast(&mut args, &self.config)?;
        }

        Ok((ast, symbol_table))
    }

    /// Report any accumulated errors
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
