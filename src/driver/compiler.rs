//! Core compilation pipeline orchestration module
//!
//! This module contains the main compiler driver that orchestrates
//! the compilation pipeline including preprocessing, lexing, parsing,
//! semantic analysis, and output generation.

use hashbrown::HashMap;
use std::path::Path;

use crate::ast::Ast;
use crate::diagnostic::DiagnosticEngine;
use crate::lexer::Lexer;
use crate::mir::codegen::MirToCraneliftLowerer;
use crate::mir::validation::MirValidator;
use crate::mir::{
    ConstValue, ConstValueId, Global, GlobalId, Local, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId,
    MirModule, MirStmt, MirStmtId, MirType, TypeId,
};
use crate::mir_dumper::{MirDumpConfig, MirDumper};
use crate::parser::Parser;
use crate::pp::Preprocessor;
use crate::semantic::SymbolTable;
use crate::source_manager::SourceManager;
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

type CompileOutput = (
    MirModule,
    HashMap<MirFunctionId, MirFunction>,
    HashMap<MirBlockId, MirBlock>,
    HashMap<LocalId, Local>,
    HashMap<GlobalId, Global>,
    HashMap<TypeId, MirType>,
    HashMap<MirStmtId, MirStmt>,
    HashMap<ConstValueId, ConstValue>,
);

impl CompilerDriver {
    /// Create a new compiler driver from CLI arguments
    pub fn new(cli: super::cli::Cli) -> Result<Self, String> {
        let config = cli.into_config()?;
        Ok(Self::from_config(config))
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
            let (mir_module, functions, blocks, locals, globals, types, statements, _constants) =
                self.compile_file(&input_file)?;

            // Skip code generation if dumping MIR
            if self.config.dump_mir {
                // MIR has already been dumped during compilation
                continue;
            }

            // Determine the output path
            let output_path = if let Some(output_path) = &self.config.output_path {
                output_path.clone()
            } else {
                // Default to a.out if no output path is specified
                Path::new("a.out").to_path_buf()
            };

            // Use MIR codegen instead of AST codegen
            let mir_codegen = MirToCraneliftLowerer::new(
                mir_module.clone(),
                functions.clone(),
                blocks.clone(),
                locals.clone(),
                globals.clone(),
                types.clone(),
                statements.clone(),
            );
            let object_file = mir_codegen.compile().unwrap();

            // Write the object file to a temporary file
            let temp_object_path = format!("{}.o", output_path.display());
            std::fs::write(&temp_object_path, object_file).unwrap();

            // Link the object file into an executable using clang
            let status = std::process::Command::new("clang")
                .arg(&temp_object_path)
                .arg("-o")
                .arg(&output_path)
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
            if let Ok(metadata) = std::fs::metadata(&output_path) {
                let mut permissions = metadata.permissions();
                permissions.set_mode(0o755); // rwxr-xr-x
                if let Err(e) = std::fs::set_permissions(&output_path, permissions) {
                    eprintln!("Warning: Failed to set executable permissions: {}", e);
                }
            }
        }

        // Report errors if any
        self.report_errors()?;

        Ok(())
    }

    /// Compile a single file through the full pipeline
    fn compile_file(&mut self, source_path: &Path) -> Result<CompileOutput, CompilerError> {
        log::debug!("Starting compilation of file: {}", source_path.display());
        let lang_options = self.config.lang_options.clone();
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
                        self.print_diagnostics();
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
            self.print_diagnostics();
            return Err(CompilerError::CompilationFailed);
        }

        // If preprocess only, dump the preprocessed output
        if self.config.preprocess_only {
            self.output_handler.dump_preprocessed_output(
                &pp_tokens,
                self.config.suppress_line_markers,
                &self.source_manager,
            )?;
            return Ok((
                MirModule::new(crate::mir::MirModuleId::new(1).unwrap()),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
            ));
        }

        // 3. Lexing phase
        let tokens = {
            let mut lexer = Lexer::new(&pp_tokens);

            // Lexer is dropped here, releasing the borrow on diagnostics
            lexer.tokenize_all()
        };

        // Check for lexing errors and stop if any
        if self.diagnostics.has_errors() {
            self.print_diagnostics();
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
            self.print_diagnostics();
            return Err(CompilerError::CompilationFailed);
        }

        // print parser AST to check
        if self.config.dump_parser {
            self.output_handler.dump_parser(&ast);
            // This is a special case. We want to stop after dumping the parser output.
            // We'll return an empty symbol table and MIR module.
            return Ok((
                MirModule::new(crate::mir::MirModuleId::new(1).unwrap()),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
            ));
        }

        // 5. Semantic lowering phase - transform declarations to concrete types
        let mut symbol_table = SymbolTable::new();
        {
            use crate::semantic::lower::run_semantic_lowering;
            run_semantic_lowering(&mut ast, &mut self.diagnostics, &mut symbol_table);
        }

        // Check for semantic lowering errors and stop if any
        if self.diagnostics.has_errors() {
            self.print_diagnostics();
            return Err(CompilerError::CompilationFailed);
        }

        // 5. Generate MIR from the AST using the new semantic analyzer
        let (mir_module, functions, blocks, locals, globals, types, statements, constants) = {
            let mut semantic_analyzer =
                crate::semantic::SemanticAnalyzer::new(&mut ast, &mut self.diagnostics, &mut symbol_table);
            let mir_module = semantic_analyzer.lower_module();
            let functions = semantic_analyzer.get_functions().clone();
            let blocks = semantic_analyzer.get_blocks().clone();
            let locals = semantic_analyzer.get_locals().clone();
            let globals = semantic_analyzer.get_globals().clone();
            let types = semantic_analyzer.get_types().clone();
            let statements = semantic_analyzer.get_statements().clone();
            let constants = semantic_analyzer.get_constants().clone();
            (
                mir_module, functions, blocks, locals, globals, types, statements, constants,
            )
        };

        // Check for semantic analysis errors and stop if any
        if self.diagnostics.has_errors() {
            self.print_diagnostics();
            return Err(CompilerError::CompilationFailed);
        }

        // 6. Validate MIR before code generation (skip if dumping MIR or testing)
        log::debug!("dump_mir config: {}", self.config.dump_mir);
        log::debug!("skip_validation config: {}", self.config.skip_validation);
        if !self.config.dump_mir && !self.config.skip_validation {
            log::debug!("Running MIR validation");
            let mut validator = MirValidator::new();
            match validator.validate(&mir_module, &functions, &blocks, &locals, &globals, &types) {
                Ok(()) => {
                    log::debug!("MIR validation passed");
                }
                Err(errors) => {
                    for error in errors {
                        self.diagnostics
                            .report_error(crate::diagnostic::SemanticError::InvalidOperands {
                                message: format!("MIR validation failed: {}", error),
                                location: crate::source_manager::SourceSpan::empty(),
                            });
                    }
                    return Err(CompilerError::SemanticError("MIR validation failed".to_string()));
                }
            }
        } else {
            log::debug!("Skipping MIR validation due to dump_mir or skip_validation flag");
        }

        // 7. Dump MIR if requested
        if self.config.dump_mir {
            log::debug!("Dumping MIR to file");
            self.dump_mir(
                &mir_module,
                &functions,
                &blocks,
                &locals,
                &globals,
                &types,
                &statements,
                &constants,
            )?;
            // Don't continue with code generation if dumping MIR
            return Ok((
                mir_module, functions, blocks, locals, globals, types, statements, constants,
            ));
        }

        // 8. Dump Cranelift IR if requested
        if self.config.dump_cranelift {
            log::debug!("Dumping Cranelift IR to console");
            self.dump_cranelift(&mir_module, &functions, &blocks, &locals, &globals, &types, &statements)?;
            // Don't continue with code generation if dumping Cranelift IR
            return Ok((
                mir_module, functions, blocks, locals, globals, types, statements, constants,
            ));
        }

        Ok((
            mir_module, functions, blocks, locals, globals, types, statements, constants,
        ))
    }

    /// Print accumulated diagnostics without returning an error
    fn print_diagnostics(&self) {
        if self.diagnostics.has_errors() {
            let formatter = crate::diagnostic::ErrorFormatter::default();
            formatter.print_diagnostics(self.diagnostics.diagnostics(), &self.source_manager);
        }
    }

    /// Report any accumulated errors
    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            self.print_diagnostics();
            return Err(CompilerError::CompilationFailed);
        }

        Ok(())
    }

    /// Dump MIR to console
    fn dump_mir(
        &mut self,
        mir_module: &MirModule,
        functions: &HashMap<MirFunctionId, MirFunction>,
        blocks: &HashMap<MirBlockId, MirBlock>,
        locals: &HashMap<LocalId, Local>,
        globals: &HashMap<GlobalId, Global>,
        types: &HashMap<TypeId, MirType>,
        statements: &HashMap<MirStmtId, MirStmt>,
        constants: &HashMap<ConstValueId, ConstValue>,
    ) -> Result<(), CompilerError> {
        // Create MIR dumper config for console output
        let dump_config = MirDumpConfig { include_header: true };

        // Create MIR dumper
        let dumper = MirDumper::new(
            mir_module,
            functions,
            blocks,
            locals,
            globals,
            types,
            constants,
            statements,
            &dump_config,
        );

        // Generate MIR dump
        let mir_dump = dumper
            .generate_mir_dump()
            .map_err(|e| CompilerError::MirDumpError(format!("Failed to generate MIR dump: {}", e)))?;

        // Output to console
        print!("{}", mir_dump);
        Ok(())
    }

    /// Dump Cranelift IR to console
    fn dump_cranelift(
        &mut self,
        mir_module: &MirModule,
        functions: &HashMap<MirFunctionId, MirFunction>,
        blocks: &HashMap<MirBlockId, MirBlock>,
        locals: &HashMap<LocalId, Local>,
        globals: &HashMap<GlobalId, Global>,
        types: &HashMap<TypeId, MirType>,
        statements: &HashMap<MirStmtId, MirStmt>,
    ) -> Result<(), CompilerError> {
        // Create a temporary MIR to Cranelift lowerer just for dumping
        let mut mir_codegen = MirToCraneliftLowerer::new(
            mir_module.clone(),
            functions.clone(),
            blocks.clone(),
            locals.clone(),
            globals.clone(),
            types.clone(),
            statements.clone(),
        );

        // Get the compiled functions (this triggers the compilation process)
        let compiled_functions = mir_codegen.get_compiled_functions_for_dump();

        // Dump each function
        for (func_name, func_ir) in compiled_functions {
            println!("; Function: {}", func_name);
            println!("{}", func_ir);
            println!();
        }

        if compiled_functions.is_empty() {
            println!("; No compiled functions found");
        }

        Ok(())
    }

    /// Get MIR dump as string for testing (with optional header)
    pub fn get_mir_dump_string(&mut self, include_header: bool) -> Result<String, CompilerError> {
        // Temporarily enable skip_validation for testing
        let original_skip_validation = self.config.skip_validation;
        self.config.skip_validation = true;

        let result = self.get_mir_dump_string_internal(include_header);

        // Restore original value
        self.config.skip_validation = original_skip_validation;

        result
    }

    /// Get MIR dump for single function as string for testing (no header)
    pub fn get_function_mir_dump_string(&mut self, include_header: bool) -> Result<String, CompilerError> {
        // Temporarily enable skip_validation for testing
        let original_skip_validation = self.config.skip_validation;
        self.config.skip_validation = true;

        let result = self.get_function_mir_dump_string_internal(include_header);

        // Restore original value
        self.config.skip_validation = original_skip_validation;

        result
    }

    /// Internal implementation for getting MIR dump as string
    fn get_mir_dump_string_internal(&mut self, include_header: bool) -> Result<String, CompilerError> {
        let input_file = self.config.input_files[0].clone();
        let (mir_module, functions, blocks, locals, globals, types, statements, constants) =
            self.compile_file(&input_file)?;

        // Create MIR dumper config for string output
        let dump_config = MirDumpConfig { include_header };

        // Create MIR dumper
        let dumper = MirDumper::new(
            &mir_module,
            &functions,
            &blocks,
            &locals,
            &globals,
            &types,
            &constants,
            &statements,
            &dump_config,
        );

        // Generate MIR dump
        let mir_dump = dumper
            .generate_mir_dump_string()
            .map_err(|e| CompilerError::MirDumpError(format!("Failed to generate MIR dump: {}", e)))?;

        Ok(mir_dump)
    }

    /// Internal implementation for getting single function MIR dump as string
    fn get_function_mir_dump_string_internal(&mut self, include_header: bool) -> Result<String, CompilerError> {
        let input_file = self.config.input_files[0].clone();
        let (mir_module, functions, blocks, locals, globals, types, statements, constants) =
            self.compile_file(&input_file)?;

        // Create MIR dumper config for string output
        let dump_config = MirDumpConfig {
            // output_path: std::path::PathBuf::from("dummy.mir"), // Not used for string output
            include_header,
        };
        // Create MIR dumper (we don't need all parameters for function-only dump)
        let dumper = MirDumper::new(
            &mir_module,
            &functions,
            &blocks,
            &locals,
            &globals,
            &types,
            &constants,
            &statements,
            &dump_config,
        );

        // Get the first function ID
        if let Some(&func_id) = functions.keys().next() {
            let mir_dump = dumper
                .generate_function_mir_dump(func_id)
                .map_err(|e| CompilerError::MirDumpError(format!("Failed to generate MIR dump: {}", e)))?;
            Ok(mir_dump)
        } else {
            Ok(String::new())
        }
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
    #[error("MIR dump failed: {0}")]
    MirDumpError(String),
    #[error("Compilation failed due to errors")]
    CompilationFailed,
}
