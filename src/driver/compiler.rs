//! Core compilation pipeline orchestration module
//!
//! This module contains the main compiler driver that orchestrates
//! the compilation pipeline including preprocessing, lexing, parsing,
//! semantic analysis, and output generation.

use std::io::Write;
use std::path::PathBuf;
use std::time::Instant;

use indexmap::IndexMap;

use crate::ast::dumper::AstDumper;
use crate::ast::{Ast, NodeKind, ParsedAst, SourceId};
use crate::codegen::{ClifGen, ClifOutput, EmitKind};
use crate::diagnostic::{DiagnosticEngine, IntoDiagnostic};
use crate::driver::cli::PathOrBuffer;
use crate::mir::validation::MirValidator;
use crate::parser::Lexer;

use super::artifact::{CompileArtifact, CompilePhase, PipelineOutputs};
use super::cli::CompileConfig;
use crate::codegen::MirGen;
use crate::mir::MirProgram;
use crate::mir::dumper::{MirDumpConfig, MirDumper};
use crate::parser::Parser;
use crate::pp::{Preprocessor, dumper::PPDumper};
use crate::semantic::{SymbolTable, TypeRegistry};
use crate::source_manager::{FileKind, SourceManager};

/// Main compiler driver
pub struct CompilerDriver {
    pub(crate) config: CompileConfig,
    pub(crate) de: DiagnosticEngine,
    pub(crate) sm: SourceManager,
}

impl CompilerDriver {
    /// Create a new compiler driver from CLI arguments
    pub fn new(cli: super::cli::Cli) -> Result<Self, String> {
        let config = cli.into_config()?;
        Ok(Self::from_config(config))
    }

    /// Create a new compiler driver from configuration
    pub fn from_config(config: CompileConfig) -> Self {
        let mut de = DiagnosticEngine::from_warnings(&config.warnings);
        // Default to one error report as requested, or use the configured limit
        de.set_error_limit(config.fmax_errors.unwrap_or(20));
        // Also set a default warning limit to prevent massive overhead for very large files
        de.set_warning_limit(200);

        let driver = CompilerDriver {
            de,
            sm: SourceManager::new(),
            config,
        };

        driver.report_ignored_flags();
        driver
    }

    fn report_ignored_flags(&self) {
        for flag in &self.config.ignored_f_flags {
            log::warn!("ignoring unrecognized command-line option '-f{}'", flag);
            eprintln!(
                "cendol: warning: ignoring unrecognized command-line option '-f{}'",
                flag
            );
        }

        for flag in &self.config.ignored_m_flags {
            log::warn!("ignoring unrecognized command-line option '-M{}'", flag);
            eprintln!(
                "cendol: warning: ignoring unrecognized command-line option '-M{}'",
                flag
            );
        }
    }

    /// Run the compilation pipeline for all input files
    pub fn run_pipeline(&mut self, stop_after: CompilePhase) -> Result<PipelineOutputs, PipelineError> {
        let mut outputs = PipelineOutputs {
            units: IndexMap::new(),
            external_object_files: Vec::new(),
        };

        let input_files = std::mem::take(&mut self.config.input_files);
        for input_file in input_files {
            if input_file.is_external_object() {
                if let PathOrBuffer::Path(path) = input_file {
                    let abs_path = std::fs::canonicalize(&path).unwrap_or(path);
                    outputs.external_object_files.push(abs_path);
                }
                continue;
            }

            if !input_file.is_source_file() {
                if let PathOrBuffer::Path(path) = &input_file {
                    log::warn!("skipping unrecognized file: {}", path.display());
                    eprintln!("cendol: warning: skipping unrecognized file: {}", path.display());
                }
                continue;
            }

            let source_id = match input_file {
                PathOrBuffer::Path(path) => self.sm.add_file(&path, None).map_err(PipelineError::IoError)?,
                PathOrBuffer::Buffer(path, buffer) => self.sm.add_buffer(buffer, path, None, FileKind::Real),
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
        let timing_enabled = self.config.timing;
        let total_start = if timing_enabled { Some(Instant::now()) } else { None };

        let mut preprocessor = Preprocessor::new(&mut self.sm, &mut self.de, &self.config.preprocessor);

        for (name, value) in &self.config.defines {
            preprocessor.define_user_macro(name, value.as_deref());
        }

        // 1. Preprocessing
        let t0 = Instant::now();
        if stop_after == CompilePhase::Preprocess {
            out.preprocessed = Some(
                preprocessor
                    .process(source_id, &self.config.preprocessor)
                    .map_err(|e| {
                        self.de.report_streaming(e.into(), &self.sm);
                        PipelineError::Fatal
                    })?,
            );
            if timing_enabled {
                eprintln!("[TIMING] Preprocessor: {:?}", t0.elapsed());
            }
            self.check_diagnostics_and_return_if_error()?;
            return Ok(out);
        }

        // 2. Lexing
        preprocessor.start_processing(source_id);
        let mut lexer = Lexer::new(&mut preprocessor, self.config.lang_options.c_standard);
        let t1 = Instant::now();
        if stop_after == CompilePhase::Lex {
            out.lexed = Some(lexer.tokenize_all().map_err(|e| {
                self.de.report_streaming(e.into(), &self.sm);
                PipelineError::Fatal
            })?);
            self.check_diagnostics_and_return_if_error()?;
            if timing_enabled {
                eprintln!("[TIMING] Lexer: {:?}", t1.elapsed());
            }
            return Ok(out);
        }

        // 3. Parsing
        let t2 = Instant::now();
        let mut parsed_ast = ParsedAst::new();
        Parser::new(&mut lexer, &mut parsed_ast, &self.config.lang_options)
            .parse_translation_unit()
            .map_err(|e| {
                for diag in e.into_diagnostic() {
                    self.de.report_streaming(diag, &self.sm);
                }
                PipelineError::Fatal
            })?;

        if timing_enabled {
            eprintln!("[TIMING] Parser: {:?}", t2.elapsed());
        }
        if stop_after == CompilePhase::Parse {
            out.parsed_ast = Some(parsed_ast);
            return Ok(out);
        }

        // 4. Semantic Lowering
        let t3 = Instant::now();
        let (ast, symbol_table, registry) = self.visit_parsed_ast(parsed_ast)?;
        if timing_enabled {
            eprintln!("[TIMING] Semantic Lowering: {:?}", t3.elapsed());
        }
        if stop_after == CompilePhase::SemanticLowering {
            out.ast = Some(ast);
            out.type_registry = Some(registry);
            out.symbol_table = Some(symbol_table);
            return Ok(out);
        }

        // 5. Semantic Analysis & MIR
        let t4 = Instant::now();
        let mir_program = self.visit_ast(ast, symbol_table, registry)?;
        if timing_enabled {
            eprintln!("[TIMING] Semantic Analysis + MIR: {:?}", t4.elapsed());
        }
        if stop_after == CompilePhase::Mir {
            out.mir_program = Some(mir_program);
            return Ok(out);
        }

        // 6. Codegen
        let t5 = Instant::now();
        let emit_kind = if stop_after == CompilePhase::Cranelift {
            EmitKind::Clif
        } else {
            EmitKind::Object
        };
        match self.run_codegen(mir_program, emit_kind)? {
            ClifOutput::ClifDump(dump) => out.clif_dump = Some(dump),
            ClifOutput::ObjectFile(obj) => out.object_file = Some(obj),
        }

        if timing_enabled {
            eprintln!("[TIMING] Codegen: {:?}", t5.elapsed());
            if let Some(start) = total_start {
                eprintln!("[TIMING] TOTAL: {:?}", start.elapsed());
            }
        }

        Ok(out)
    }

    fn visit_parsed_ast(&mut self, parsed_ast: ParsedAst) -> Result<(Ast, SymbolTable, TypeRegistry), PipelineError> {
        let mut symbol_table = SymbolTable::new();
        // Use the target triple from configuration to initialize TypeRegistry
        let mut registry = TypeRegistry::new(self.config.target.0.clone());
        let mut ast = Ast::new();

        use crate::semantic::lowering::visit_ast;
        visit_ast(
            &parsed_ast,
            &mut ast,
            &mut self.de,
            &mut symbol_table,
            &mut registry,
            &self.config.lang_options,
        );

        self.check_diagnostics_and_return_if_error()?;

        #[cfg(debug_assertions)]
        self.validate_ast_invariants(&ast);

        Ok((ast, symbol_table, registry))
    }

    fn validate_ast_invariants(&self, ast: &Ast) {
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
                _ => {}
            }
        }

        for (i, kind) in ast.kinds.iter().enumerate() {
            let parent_idx = i + 1;
            kind.visit_children(|child| {
                let child_idx = child.raw() as usize;
                if child_idx <= parent_idx {
                    panic!(
                        "ICE: AST invariant violation: parent index ({}) >= child index ({}) for node {:?}",
                        parent_idx, child_idx, kind
                    );
                }
            });
        }
    }

    fn visit_ast(
        &mut self,
        mut ast: Ast,
        symbol_table: SymbolTable,
        mut registry: TypeRegistry,
    ) -> Result<MirProgram, PipelineError> {
        // Timing for semantic analysis
        let timing_enabled = self.config.timing;

        use crate::semantic::analyzer::visit_ast;
        let t0 = if timing_enabled { Some(Instant::now()) } else { None };
        let semantic_info = visit_ast(
            &ast,
            &mut self.de,
            &symbol_table,
            &mut registry,
            &self.config.lang_options,
            &self.sm,
        );
        if let Some(t0) = t0 {
            eprintln!("[TIMING]   Semantic Analyzer: {:?}", t0.elapsed());
        }
        self.check_diagnostics_and_return_if_error()?;

        // Attach semantic info to AST (like scope_map)
        ast.attach_semantic_info(semantic_info);

        // MIR generation
        let t1 = if timing_enabled { Some(Instant::now()) } else { None };
        let mut sema = MirGen::new(
            &ast,
            &symbol_table,
            &mut registry,
            self.config.lang_options.fpic,
            self.config.lang_options.signed_overflow_mode,
            self.config.lang_options.visibility,
        );
        let mir_program = sema.visit_module();
        if let Some(t1) = t1 {
            eprintln!("[TIMING]   MIR Generation: {:?}", t1.elapsed());
        }
        self.check_diagnostics_and_return_if_error()?;

        Ok(mir_program)
    }

    fn run_codegen(&mut self, mir_program: MirProgram, emit_kind: EmitKind) -> Result<ClifOutput, PipelineError> {
        let validator = MirValidator::new(&mir_program);
        if let Err(errors) = validator.validate() {
            panic!("MIR validation failed: {:?}", errors);
        }

        // Use MIR codegen instead of AST codegen
        let mir_codegen = ClifGen::new(mir_program);
        Ok(mir_codegen.visit_module(emit_kind))
    }

    /// Check if there are any diagnostics errors and return PipelineError::Fatal if there are
    fn check_diagnostics_and_return_if_error(&self) -> Result<(), PipelineError> {
        if self.de.has_errors() {
            Err(PipelineError::Fatal)
        } else {
            Ok(())
        }
    }

    /// Run the compilation process for all input files
    /// this function handles the full pipeline from source to executable
    /// and emit diagnostics if any error occurs
    pub fn run(&mut self) -> Result<(), DriverError> {
        let stop_after = self.config.stop_after;
        let res = match self.run_pipeline(stop_after) {
            Ok(outputs) => self.process_outputs(outputs),
            Err(e) => self.handle_pipeline_error(e),
        };
        if res.is_ok() {
            self.print_diagnostics();
        }
        res
    }

    fn handle_pipeline_error(&self, err: PipelineError) -> Result<(), DriverError> {
        self.print_diagnostics();
        match err {
            PipelineError::IoError(io_err) => {
                let message = format!("I/O Error: {}", io_err);
                Err(DriverError::IoError(message))
            }
            PipelineError::Fatal => Err(DriverError::CompilationFailed),
        }
    }

    fn process_outputs(&mut self, outputs: PipelineOutputs) -> Result<(), DriverError> {
        let mut object_files_to_link = outputs.external_object_files;
        let mut temp_files = Vec::new();

        for (source_id, artifact) in outputs.units {
            self.handle_artifact(source_id, artifact, &mut object_files_to_link, &mut temp_files)?;
        }

        if !object_files_to_link.is_empty() && !self.config.compile_only {
            self.perform_linking(object_files_to_link, &mut temp_files)?;
        }

        Ok(())
    }

    fn handle_artifact(
        &self,
        source_id: SourceId,
        artifact: CompileArtifact,
        object_files: &mut Vec<PathBuf>,
        temp_files: &mut Vec<tempfile::NamedTempFile>,
    ) -> Result<(), DriverError> {
        if let Some(object_code) = artifact.object_file {
            self.handle_object_file(source_id, object_code, object_files, temp_files)
        } else {
            self.handle_artifact_dump(artifact)
        }
    }

    fn handle_artifact_dump(&self, artifact: CompileArtifact) -> Result<(), DriverError> {
        if let Some(clif_dump) = artifact.clif_dump {
            println!("{}", clif_dump);
        } else if let Some(mir_program) = artifact.mir_program {
            let dump_config = MirDumpConfig { include_header: true };
            let dumper = MirDumper::new(&mir_program, &dump_config);
            match dumper.generate_mir_dump() {
                Ok(mir_dump) => println!("{}", mir_dump),
                Err(_) => {
                    self.print_diagnostics();
                    return Err(DriverError::CompilationFailed);
                }
            }
        } else if let Some(ast) = artifact.ast {
            print!("{}", AstDumper::dump_ast(&ast, artifact.symbol_table.as_ref()));
            if let Some(registry) = artifact.type_registry {
                print!("{}", AstDumper::dump_type_registry(&ast, &registry));
            }
        } else if let Some(parsed_ast) = artifact.parsed_ast {
            print!("{}", AstDumper::dump_parsed_ast(&parsed_ast));
        } else if let Some(preprocessed) = artifact.preprocessed {
            let dumper = PPDumper::new(&preprocessed, &self.sm, self.config.suppress_line_markers);

            if let Some(ref output_path) = self.config.output_path {
                let mut file = std::fs::File::create(output_path)
                    .map_err(|e| DriverError::IoError(format!("Failed to create output file: {}", e)))?;
                dumper
                    .dump(&mut file)
                    .map_err(|e| DriverError::IoError(e.to_string()))?;
            } else {
                dumper
                    .dump(&mut std::io::stdout())
                    .map_err(|e| DriverError::IoError(e.to_string()))?;
            }
        }
        Ok(())
    }

    fn handle_object_file(
        &self,
        source_id: SourceId,
        object_code: Vec<u8>,
        object_files: &mut Vec<PathBuf>,
        temp_files: &mut Vec<tempfile::NamedTempFile>,
    ) -> Result<(), DriverError> {
        if self.config.compile_only {
            let output_path = if let Some(ref path) = self.config.output_path {
                path.clone()
            } else {
                let file_info = self.sm.get_file_info(source_id).expect("Source file should exist");
                let mut path = file_info.path.clone();
                path.set_extension("o");
                path
            };

            std::fs::write(&output_path, &object_code)
                .map_err(|e| DriverError::IoError(format!("Failed to write object file: {}", e)))?;
        } else {
            let mut temp_file = tempfile::Builder::new()
                .suffix(".o")
                .tempfile()
                .map_err(|e| DriverError::IoError(format!("Failed to create temp file: {}", e)))?;

            temp_file
                .write_all(&object_code)
                .map_err(|e| DriverError::IoError(format!("Failed to write object file: {}", e)))?;

            object_files.push(temp_file.path().to_path_buf());
            temp_files.push(temp_file);
        }
        Ok(())
    }

    fn perform_linking(
        &self,
        mut object_files: Vec<PathBuf>,
        temp_files: &mut Vec<tempfile::NamedTempFile>,
    ) -> Result<(), DriverError> {
        if self.config.target.0.architecture == "x86_64".parse().unwrap() {
            self.add_x86_64_vararg_trampoline(&mut object_files, temp_files)?;
        }

        let output_path = self.config.output_path.clone().unwrap_or_else(|| "a.out".into());
        let link_config = crate::codegen::LinkConfig {
            output_path,
            library_paths: self.config.library_paths.clone(),
            libraries: self.config.libraries.clone(),
            optimization: self.config.optimization.clone(),
            debug_info: self.config.debug_info,
            shared: self.config.shared,
            verbose: self.config.verbose,
            fuse_ld: self.config.fuse_ld.clone(),
            linker_args: self.config.linker_args.clone(),
        };

        crate::codegen::LinkGen::link(&object_files, &link_config).map_err(|e| match e {
            crate::codegen::LinkError::IoError(msg) => DriverError::IoError(msg),
            crate::codegen::LinkError::LinkFailed => DriverError::LinkingFailed,
        })
    }

    fn add_x86_64_vararg_trampoline(
        &self,
        object_files: &mut Vec<PathBuf>,
        temp_files: &mut Vec<tempfile::NamedTempFile>,
    ) -> Result<(), DriverError> {
        let mut temp_s = tempfile::Builder::new()
            .suffix(".s")
            .tempfile()
            .map_err(|e| DriverError::IoError(format!("Failed to create temp assembly: {}", e)))?;

        let asm_content = b"
.data
.global __cendol_vararg_al_count
.global __cendol_vararg_target_addr
.align 8
__cendol_vararg_al_count:
        .quad 0
__cendol_vararg_target_addr:
        .quad 0

.text
.global __cendol_vararg_trampoline
.type __cendol_vararg_trampoline, @function
__cendol_vararg_trampoline:
        movq __cendol_vararg_al_count(%rip), %rax
        movq __cendol_vararg_target_addr(%rip), %r11
        jmp *%r11
        .size __cendol_vararg_trampoline, . - __cendol_vararg_trampoline

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,\"\",%progbits
#endif
";
        temp_s
            .write_all(asm_content)
            .map_err(|e| DriverError::IoError(format!("Failed to write assembly: {}", e)))?;
        object_files.push(temp_s.path().to_path_buf());
        temp_files.push(temp_s);
        Ok(())
    }

    /// Get diagnostics for testing
    #[cfg(test)]
    pub(crate) fn get_diagnostics(&self) -> Vec<crate::diagnostic::Diagnostic> {
        self.de.diagnostics.clone()
    }

    /// Print accumulated diagnostics without returning an error
    pub(crate) fn print_diagnostics(&self) {
        self.de
            .print_diagnostics_filtered(&self.sm, self.config.suppress_warnings);
    }
}

/// Error types for the compiler driver
#[derive(Debug, thiserror::Error)]
pub enum DriverError {
    #[error("I/O error: {0}")]
    IoError(String),

    #[error("Compilation failed due to errors")]
    CompilationFailed,

    #[error("Linking failed")]
    LinkingFailed,
}

/// Error that will stop the compilation pipeline
#[derive(Debug)]
pub enum PipelineError {
    Fatal,
    IoError(std::io::Error),
}
