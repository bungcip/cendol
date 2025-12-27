//! Core compilation pipeline orchestration module
//!
//! This module contains the main compiler driver that orchestrates
//! the compilation pipeline including preprocessing, lexing, parsing,
//! semantic analysis, and output generation.

use hashbrown::HashMap;
use indexmap::IndexMap;

use crate::ast::{Ast, NodeKind, SourceId};
use crate::diagnostic::{Diagnostic, DiagnosticEngine, DiagnosticLevel};
use crate::driver::cli::PathOrBuffer;
use crate::lexer::{Lexer, Token};
use crate::mir::codegen::{ClifOutput, EmitKind, MirToCraneliftLowerer};
use crate::mir::validation::MirValidator;
use crate::mir::{
    ConstValue, ConstValueId, Global, GlobalId, Local, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId,
    MirModule, MirStmt, MirStmtId, MirType, TypeId,
};
use crate::mir_dumper::{MirDumpConfig, MirDumper};
use crate::parser::Parser;
use crate::pp::{PPToken, Preprocessor};
use crate::semantic::{AstToMirLowerer, SymbolTable};
use crate::source_manager::SourceManager;

use super::cli::CompileConfig;
use super::output::OutputHandler;

/// Main compiler driver
pub struct CompilerDriver {
    config: CompileConfig,
    diagnostics: DiagnosticEngine,
    source_manager: SourceManager,
    output_handler: OutputHandler,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub enum CompilePhase {
    Preprocess,
    Lex,
    Parse,
    Mir,
    Cranelift,
    #[default]
    EmitObject,
}

/// compilation outputs for all source files
pub struct PipelineOutputs {
    pub units: indexmap::IndexMap<SourceId, CompileArtifact>,
}

/// outputs for a single compilation unit
pub struct CompileArtifact {
    pub preprocessed: Option<Vec<PPToken>>,
    pub lexed: Option<Vec<Token>>,
    pub ast: Option<Ast>,
    pub mir: Option<MirModule>,
    pub sema_output: Option<SemaOutput>,
    pub clif_dump: Option<String>,
    pub object_file: Option<Vec<u8>>,
}

/// Complete semantic analysis output containing all MIR data structures
#[derive(Clone)]
pub struct SemaOutput {
    pub module: MirModule,
    pub functions: HashMap<MirFunctionId, MirFunction>,
    pub blocks: HashMap<MirBlockId, MirBlock>,
    pub locals: HashMap<LocalId, Local>,
    pub globals: HashMap<GlobalId, Global>,
    pub types: HashMap<TypeId, MirType>,
    pub constants: HashMap<ConstValueId, ConstValue>,
    pub statements: HashMap<MirStmtId, MirStmt>,
}

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

    pub fn run_pipeline(&mut self, stop_after: CompilePhase) -> Result<PipelineOutputs, PipelineError> {
        let mut outputs = PipelineOutputs { units: IndexMap::new() };

        // Process each input file
        for input_file in self.config.input_files.clone() {
            let source_id = match input_file {
                PathOrBuffer::Path(path) => match self.source_manager.add_file_from_path(&path) {
                    Ok(id) => id,
                    Err(e) => return Err(PipelineError::IoError(e)),
                },
                PathOrBuffer::Buffer(path, buffer) => self.source_manager.add_buffer(buffer, &path),
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
        let mut out = CompileArtifact {
            preprocessed: None,
            lexed: None,
            ast: None,
            mir: None,
            sema_output: None,
            clif_dump: None,
            object_file: None,
        };

        // Preprocessing phase
        let pp_tokens = self.run_preprocessor(source_id)?;
        if stop_after == CompilePhase::Preprocess {
            out.preprocessed = Some(pp_tokens);
            return Ok(out);
        }

        // Lexing & Parsing phase
        let tokens = self.run_lexer(&pp_tokens)?;
        if stop_after == CompilePhase::Lex {
            out.lexed = Some(tokens);
            return Ok(out);
        }

        let ast = self.run_parser(&tokens)?;
        if stop_after == CompilePhase::Parse {
            out.ast = Some(ast);
            return Ok(out);
        }

        // semantic lowering and MIR generation phase
        let sema_output = self.run_mir(ast)?;
        if stop_after == CompilePhase::Mir {
            out.mir = Some(sema_output.module.clone());
            out.sema_output = Some(sema_output);
            return Ok(out);
        }

        // Cranelift code generation phase
        let emit_kind = if stop_after == CompilePhase::Cranelift {
            EmitKind::Clif
        } else {
            EmitKind::Object
        };
        let cl_output = self.run_codegen(sema_output, emit_kind)?;

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
            Err(_) => {
                // printing diagnostics is handled in the caller
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
        if self.diagnostics.has_errors() {
            return Err(PipelineError::Fatal);
        }

        Ok(tokens)
    }

    fn run_parser(&mut self, tokens: &[Token]) -> Result<Ast, PipelineError> {
        // Parsing phase
        let mut ast = Ast::new();
        let mut parser = Parser::new(tokens, &mut ast, &mut self.diagnostics);
        match parser.parse_translation_unit() {
            Ok(_) => Ok(ast),
            Err(e) => {
                self.diagnostics.report(e);
                Err(PipelineError::Fatal)
            }
        }
    }

    fn run_mir(&mut self, mut ast: Ast) -> Result<SemaOutput, PipelineError> {
        let mut symbol_table = SymbolTable::new();

        // Run symbol resolver to resolve identifiers using the symbol table
        {
            use crate::semantic::resolver::run_symbol_resolver;
            run_symbol_resolver(&mut ast, &mut self.diagnostics, &mut symbol_table);
        }

        // Check for semantic analysis errors and stop if any
        if self.diagnostics.has_errors() {
            return Err(PipelineError::Fatal);
        }

        // Run type checker phase immediately after symbol resolver
        {
            use crate::semantic::type_checker::run_type_checker;
            run_type_checker(&mut ast, &mut self.diagnostics, &mut symbol_table);
        }

        // Check for semantic analysis errors and stop if any
        if self.diagnostics.has_errors() {
            return Err(PipelineError::Fatal);
        }

        // validation: all node of identifier must have symbol in ast
        for node in &ast.nodes {
            match &node.kind {
                NodeKind::VarDecl(..) | NodeKind::Ident(..) if node.resolved_symbol.get() == None => {
                    panic!("node.resolved_symbol still None: {:?}", node)
                }
                _ => (),
            }
        }

        // Check for semantic analysis errors and stop if any
        if self.diagnostics.has_errors() {
            return Err(PipelineError::Fatal);
        }

        // Check for semantic analysis errors after resolver and stop if any
        if self.diagnostics.has_errors() {
            return Err(PipelineError::Fatal);
        }

        // this is AstToMirLowerer
        let mut sema = AstToMirLowerer::new(&mut ast, &mut self.diagnostics, &mut symbol_table);
        let sema_output = sema.lower_module_complete();

        // Check for semantic analysis errors and stop if any
        if self.diagnostics.has_errors() {
            return Err(PipelineError::Fatal);
        }

        Ok(sema_output)
    }

    fn run_codegen(&mut self, sema_output: SemaOutput, emit_kind: EmitKind) -> Result<ClifOutput, PipelineError> {
        // Validate MIR before code generation
        log::debug!("Running MIR validation");
        let mut validator = MirValidator::new();
        if let Err(errors) = validator.validate(&sema_output) {
            panic!("MIR validation failed: {:?}", errors);
        }

        // Use MIR codegen instead of AST codegen
        let mir_codegen = MirToCraneliftLowerer::new(sema_output);
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

    /// Run the compilation process for all input files
    /// this function handles the full pipeline from source to executable
    /// and emit diagnostics if any error occurs
    pub fn run(&mut self) -> Result<(), DriverError> {
        let result = self.run_pipeline(self.config.stop_after);
        match result {
            Ok(outputs) => {
                // Process outputs if needed
                for (_source_id, artifact) in outputs.units {
                    if let Some(object_file) = artifact.object_file {
                        // Determine the output path
                        let output_path = if let Some(output_path) = &self.config.output_path {
                            output_path.clone()
                        } else {
                            // Default to a.out if no output path is specified
                            "a.out".into()
                        };
                        // Write the object file to a temporary file
                        let temp_object_path = format!("{}.o", output_path.display());
                        std::fs::write(&temp_object_path, object_file).unwrap();

                        // TODO: handle linking after all input files are compiled, for now its okay because we only handle single input file

                        // Link the object file into an executable using clang
                        let _status = std::process::Command::new("clang")
                            .arg(&temp_object_path)
                            .arg("-o")
                            .arg(&output_path)
                            .status()
                            .expect("Failed to execute clang for linking");

                        // Set executable permissions on the output file
                        use std::os::unix::fs::PermissionsExt;
                        if let Ok(metadata) = std::fs::metadata(&output_path) {
                            let mut permissions = metadata.permissions();
                            permissions.set_mode(0o755); // rwxr-xr-x
                            if let Err(e) = std::fs::set_permissions(&output_path, permissions) {
                                eprintln!("Warning: Failed to set executable permissions: {}", e);
                            }
                        }
                    } else if let Some(clif_dump) = artifact.clif_dump {
                        // Output Cranelift IR dump to console
                        println!("{}", clif_dump);
                    } else if let Some(sema_output) = artifact.sema_output {
                        // Output MIR dump to console
                        let dump_config = MirDumpConfig { include_header: true };

                        let dumper = MirDumper::new(&sema_output, &dump_config);
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
                        self.output_handler.dump_parser(&ast);
                    } else if let Some(preprocessed) = artifact.preprocessed {
                        self.output_handler.dump_preprocessed_output(
                            &preprocessed,
                            self.config.suppress_line_markers,
                            &self.source_manager,
                        )?;
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
    pub fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.diagnostics().to_vec()
    }

    /// Print accumulated diagnostics without returning an error
    pub fn print_diagnostics(&self) {
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
