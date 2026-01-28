//! Core compilation pipeline orchestration module
//!
//! This module contains the main compiler driver that orchestrates
//! the compilation pipeline including preprocessing, lexing, parsing,
//! semantic analysis, and output generation.

use indexmap::IndexMap;

use crate::ast::dumper::AstDumper;
use crate::ast::{Ast, NodeKind, NodeRef, ParsedAst, SourceId};
use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
use crate::driver::cli::PathOrBuffer;
use crate::lexer::{Lexer, Token};
use crate::mir::codegen::{ClifOutput, EmitKind, MirToCraneliftLowerer};
use crate::mir::validation::MirValidator;

use super::artifact::{CompileArtifact, CompilePhase, PipelineOutputs};
use crate::mir::MirProgram;
use crate::mir::dumper::{MirDumpConfig, MirDumper};
use crate::parser::Parser;
use crate::pp::{PPToken, Preprocessor};
use crate::semantic::{AstToMirLowerer, SymbolTable, TypeRegistry};
use crate::source_manager::SourceManager;

use super::cli::CompileConfig;
use super::output::OutputHandler;

/// Main compiler driver
pub struct CompilerDriver {
    config: CompileConfig,
    diagnostics: DiagnosticEngine,
    pub(crate) source_manager: SourceManager,
    output_handler: OutputHandler,
}

impl CompilerDriver {
    /// Create a new compiler driver from CLI arguments
    pub fn new(cli: super::cli::Cli) -> Result<Self, String> {
        let config = cli.into_config()?;
        Ok(Self::from_config(config))
    }

    /// Create a new compiler driver from configuration
    pub(crate) fn from_config(config: CompileConfig) -> Self {
        let diagnostics = DiagnosticEngine::from_warnings(&config.warnings);
        CompilerDriver {
            diagnostics,
            source_manager: SourceManager::new(),
            output_handler: OutputHandler::new(),
            config,
        }
    }

    pub(crate) fn run_pipeline(&mut self, stop_after: CompilePhase) -> Result<PipelineOutputs, PipelineError> {
        let mut outputs = PipelineOutputs { units: IndexMap::new() };

        // Process each input file
        let input_files = std::mem::take(&mut self.config.input_files);
        for input_file in input_files {
            let source_id = match input_file {
                PathOrBuffer::Path(path) => match self.source_manager.add_file_from_path(&path, None) {
                    Ok(id) => id,
                    Err(e) => return Err(PipelineError::IoError(e)),
                },
                PathOrBuffer::Buffer(path, buffer) => self.source_manager.add_buffer(buffer, &path, None),
            };

            let unit_output = self.run_translation_unit(source_id, stop_after)?;
            outputs.units.insert(source_id, unit_output);
        }

        Ok(outputs)
    }

    fn run_translation_unit(
        &mut self,
        source_id: SourceId,
        stop_after: CompilePhase,
    ) -> Result<CompileArtifact, PipelineError> {
        let mut out = CompileArtifact::default();

        // Preprocessing phase
        let pp_tokens = self.run_preprocessor(source_id)?;
        if stop_after == CompilePhase::Preprocess {
            out.preprocessed = Some(pp_tokens);
            return Ok(out);
        }

        // Lexing phase
        let tokens = self.run_lexer(&pp_tokens)?;
        if stop_after == CompilePhase::Lex {
            out.lexed = Some(tokens);
            return Ok(out);
        }

        // parsing phase
        let parsed_ast = self.run_parser(&tokens)?;
        if stop_after == CompilePhase::Parse {
            out.parsed_ast = Some(parsed_ast);
            return Ok(out);
        }

        // semantic lowering (Symbol Resolution & AST Construction)
        let (ast, symbol_table, registry) = self.run_semantic_lowering(parsed_ast)?;
        if stop_after == CompilePhase::SemanticLowering {
            out.ast = Some(ast);
            out.type_registry = Some(registry);
            out.symbol_table = Some(symbol_table);
            return Ok(out);
        }

        // semantic analyzer & MIR generation phase
        let mir_program = self.run_semantic_analyzer(ast, symbol_table, registry)?;
        if stop_after == CompilePhase::Mir {
            out.mir_program = Some(mir_program);
            return Ok(out);
        }

        // Cranelift code generation phase
        let emit_kind = if stop_after == CompilePhase::Cranelift {
            EmitKind::Clif
        } else {
            EmitKind::Object
        };
        let cl_output = self.run_codegen(mir_program, emit_kind)?;

        match cl_output {
            ClifOutput::ClifDump(dump) => {
                out.clif_dump = Some(dump);
            }
            ClifOutput::ObjectFile(obj) => {
                out.object_file = Some(obj);
            }
        }

        Ok(out)
    }

    fn run_preprocessor(&mut self, source_id: SourceId) -> Result<Vec<PPToken>, PipelineError> {
        let mut preprocessor = Preprocessor::new(
            &mut self.source_manager,
            &mut self.diagnostics,
            &self.config.preprocessor,
        );

        // Preprocessor is dropped here, releasing the borrow on diagnostics
        match preprocessor.process(source_id, &self.config.preprocessor) {
            Ok(t) => Ok(t),
            Err(e) => {
                // Report the specific preprocessor error
                self.diagnostics.report_diagnostic(e.into());
                Err(PipelineError::Fatal)
            }
        }
    }

    fn run_lexer(&mut self, pp_tokens: &[PPToken]) -> Result<Vec<Token>, PipelineError> {
        let tokens = {
            let mut lexer = Lexer::new(pp_tokens);
            lexer.tokenize_all()
        };

        // Check for lexing errors and stop if any
        self.check_diagnostics_and_return_if_error()?;

        Ok(tokens)
    }

    fn run_parser(&mut self, tokens: &[Token]) -> Result<ParsedAst, PipelineError> {
        // Parsing phase
        let mut parsed_ast = ParsedAst::new();
        let mut parser = Parser::new(tokens, &mut parsed_ast, &mut self.diagnostics);
        match parser.parse_translation_unit() {
            Ok(_) => Ok(parsed_ast),
            Err(e) => {
                self.diagnostics.report(e);
                Err(PipelineError::Fatal)
            }
        }
    }

    fn run_semantic_lowering(
        &mut self,
        parsed_ast: ParsedAst,
    ) -> Result<(Ast, SymbolTable, TypeRegistry), PipelineError> {
        let mut symbol_table = SymbolTable::new();
        // Use the target triple from configuration to initialize TypeRegistry
        let mut registry = TypeRegistry::new(self.config.target.clone());
        let mut ast = Ast::new();

        use crate::semantic::lowering::run_semantic_lowering;
        run_semantic_lowering(
            &parsed_ast,
            &mut ast,
            &mut self.diagnostics,
            &mut symbol_table,
            &mut registry,
        );

        self.check_diagnostics_and_return_if_error()?;

        // Validate that parsing-only node kinds have been lowered (actually they shouldn't exist in Ast now)
        // But for safety/debugging:
        #[cfg(debug_assertions)]
        for kind in &ast.kinds {
            match kind {
                NodeKind::BinaryOp(op, ..) if op.is_assignment() => {
                    panic!(
                        "ICE: NodeKind::BinaryOp with assignment operator {:?}, use NodeKind::Assignment instead",
                        op
                    );
                }
                NodeKind::Assignment(op, ..) if !op.is_assignment() => {
                    panic!(
                        "ICE: NodeKind::Assignment with non-assignment operator {:?}, use NodeKind::BinaryOp instead",
                        op
                    );
                }
                // Check if any legacy variants slipped in (NodeKind shouldn't have them anymore so compile error if we match them)
                _ => {}
            }
        }

        #[cfg(debug_assertions)]
        for (i, kind) in ast.kinds.iter().enumerate() {
            let parent_idx = i + 1;
            kind.visit_children(|child| {
                let child_idx = child.get() as usize;
                if child_idx <= parent_idx {
                    panic!(
                        "ICE: AST invariant violation: parent index ({}) >= child index ({}) for node {:?}",
                        parent_idx, child_idx, kind
                    );
                }
            });
        }

        Ok((ast, symbol_table, registry))
    }

    fn run_semantic_analyzer(
        &mut self,
        mut ast: Ast,
        symbol_table: SymbolTable,
        mut registry: TypeRegistry,
    ) -> Result<MirProgram, PipelineError> {
        use crate::semantic::analyzer::run_semantic_analyzer;
        let semantic_info = run_semantic_analyzer(&ast, &mut self.diagnostics, &symbol_table, &mut registry);
        self.check_diagnostics_and_return_if_error()?;

        // Attach semantic info to AST (like scope_map)
        ast.attach_semantic_info(semantic_info);

        // invariant validations
        // all expression must have resolved_type set
        for (i, kind) in ast.kinds.iter().enumerate() {
            let node_ref = NodeRef::new((i as u32) + 1).unwrap();
            match kind {
                NodeKind::Ident(name, ..) if ast.get_resolved_type(node_ref).is_none() => {
                    let span = ast.get_span(node_ref);
                    panic!(
                        "ICE: ident '{}' still not have resolved type: {:?}",
                        name,
                        self.source_manager.get_line_column(span.start())
                    );
                }
                _ => {}
            }
        }

        let mut sema = AstToMirLowerer::new(&ast, &symbol_table, &mut registry);
        let mir_program = sema.lower_module_complete();
        self.check_diagnostics_and_return_if_error()?;

        Ok(mir_program)
    }

    fn run_codegen(&mut self, mir_program: MirProgram, emit_kind: EmitKind) -> Result<ClifOutput, PipelineError> {
        // Validate MIR before code generation
        log::debug!("Running MIR validation");
        let validator = MirValidator::new(&mir_program);
        if let Err(errors) = validator.validate() {
            panic!("MIR validation failed: {:?}", errors);
        }

        // Use MIR codegen instead of AST codegen
        let mir_codegen = MirToCraneliftLowerer::new(mir_program);
        match mir_codegen.compile_module(emit_kind) {
            Ok(output) => Ok(output),
            Err(e) => {
                self.diagnostics.report_diagnostic(Diagnostic {
                    level: DiagnosticLevel::Error,
                    message: e.to_string(),
                    ..Default::default()
                });
                Err(PipelineError::Fatal)
            }
        }
    }

    /// Check if there are any diagnostics errors and return PipelineError::Fatal if there are
    fn check_diagnostics_and_return_if_error(&self) -> Result<(), PipelineError> {
        if self.diagnostics.has_errors() {
            Err(PipelineError::Fatal)
        } else {
            Ok(())
        }
    }

    /// Run the compilation process for all input files
    /// this function handles the full pipeline from source to executable
    /// and emit diagnostics if any error occurs
    pub fn run(&mut self) -> Result<(), DriverError> {
        let result = self.run_pipeline(self.config.stop_after);
        match result {
            Ok(outputs) => {
                self.print_diagnostics();
                let mut object_files_to_link = Vec::new();
                // We need to keep the temp files alive until the linking process is complete
                let mut temp_files = Vec::new();

                // Process outputs if needed
                for (_source_id, artifact) in outputs.units {
                    if let Some(object_file) = artifact.object_file {
                        // Write the object file to a temporary file
                        let mut temp_file = tempfile::Builder::new()
                            .suffix(".o")
                            .tempfile()
                            .map_err(|e| DriverError::IoError(format!("Failed to create temp file: {}", e)))?;

                        use std::io::Write;
                        temp_file
                            .write_all(&object_file)
                            .map_err(|e| DriverError::IoError(format!("Failed to write object file: {}", e)))?;

                        object_files_to_link.push(temp_file.path().to_path_buf());
                        temp_files.push(temp_file);
                    } else if let Some(clif_dump) = artifact.clif_dump {
                        // Output Cranelift IR dump to console
                        println!("{}", clif_dump);
                    } else if let Some(mir_program) = artifact.mir_program {
                        // Output MIR dump to console
                        let dump_config = MirDumpConfig { include_header: true };

                        let dumper = MirDumper::new(&mir_program, &dump_config);
                        match dumper.generate_mir_dump() {
                            Ok(mir_dump) => {
                                println!("{}", mir_dump);
                            }
                            Err(_e) => {
                                self.print_diagnostics();
                                return Err(DriverError::CompilationFailed);
                            }
                        }
                    } else if let Some(ast) = artifact.ast {
                        AstDumper::dump_parser(&ast, artifact.symbol_table.as_ref());
                        if let Some(registry) = artifact.type_registry {
                            AstDumper::dump_type_registry(&ast, &registry);
                        }
                    } else if let Some(parsed_ast) = artifact.parsed_ast {
                        AstDumper::dump_parsed_ast(&parsed_ast);
                    } else if let Some(preprocessed) = artifact.preprocessed {
                        self.output_handler.dump_preprocessed_output(
                            &preprocessed,
                            self.config.suppress_line_markers,
                            &self.source_manager,
                        )?;
                    }
                }

                // Link if we have object files and NOT compile_only
                if !object_files_to_link.is_empty() && !self.config.compile_only {
                    // Determine the output path
                    let output_path = if let Some(output_path) = &self.config.output_path {
                        output_path.clone()
                    } else {
                        // Default to a.out if no output path is specified
                        "a.out".into()
                    };

                    // Link the object file into an executable using clang
                    let mut clang_cmd = std::process::Command::new("clang");
                    clang_cmd.args(&object_files_to_link);

                    // Add library paths
                    for path in &self.config.library_paths {
                        clang_cmd.arg("-L").arg(path);
                    }

                    // Add libraries
                    for lib in &self.config.libraries {
                        clang_cmd.arg(format!("-l{}", lib));
                    }

                    // Add optimization flags if present
                    if let Some(opt) = &self.config.optimization {
                        clang_cmd.arg(format!("-O{}", opt));
                    }

                    // Add debug info if requested
                    if self.config.debug_info {
                        clang_cmd.arg("-g");
                    }

                    // Default to linking math library for now as it was before,
                    // but we might want to let the user specify it via -lm
                    if !self.config.libraries.contains(&"m".to_string()) {
                        clang_cmd.arg("-lm");
                    }

                    if self.config.verbose {
                        println!("Executing linker: {:?}", clang_cmd);
                    }

                    let status = clang_cmd
                        .arg("-o")
                        .arg(&output_path)
                        .status()
                        .map_err(|e| DriverError::IoError(format!("Failed to execute clang for linking: {}", e)))?;

                    if !status.success() {
                        return Err(DriverError::CompilationFailed);
                    }

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
            }
            Err(e) => match e {
                PipelineError::IoError(io_err) => {
                    let message = format!("I/O Error: {}", io_err);
                    return Err(DriverError::IoError(message));
                }
                PipelineError::Fatal => {
                    self.print_diagnostics();
                    return Err(DriverError::CompilationFailed);
                }
            },
        }

        Ok(())
    }

    /// Get diagnostics for testing
    #[cfg(test)]
    pub(crate) fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.diagnostics().to_vec()
    }

    /// Print accumulated diagnostics without returning an error
    pub(crate) fn print_diagnostics(&self) {
        let formatter = crate::diagnostic::ErrorFormatter::default();
        formatter.print_diagnostics(self.diagnostics.diagnostics(), &self.source_manager);
    }
}

/// Error types for the compiler driver
#[derive(Debug, thiserror::Error)]
pub enum DriverError {
    #[error("I/O error: {0}")]
    IoError(String),

    #[error("Compilation failed due to errors")]
    CompilationFailed,
}

/// Error that will stop the compilation pipeline
#[derive(Debug)]
pub enum PipelineError {
    Fatal,
    IoError(std::io::Error),
}
