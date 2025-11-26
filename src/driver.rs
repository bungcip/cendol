// Compiler driver module

use clap::{Args, Parser as CliParser};
use itertools::Itertools;
use log::debug;
use std::fs;
use std::path::{Path, PathBuf};
use target_lexicon::Triple;

use crate::ast::{Ast, NodeKind};
use crate::ast_dumper::{AstDumper, DumpConfig};
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::parser::Parser;
use crate::pp::{Preprocessor, PreprocessorConfig, PPTokenFlags};
use crate::semantic::{SemanticAnalyzer, SymbolTable};
use crate::source_manager::SourceManager;

// Remove duplicate PreprocessorConfig definition

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

    /// Dump parser state
    #[clap(long)]
    pub dump_parser: bool,

    /// Generate HTML AST dump
    #[clap(long)]
    pub dump_ast: bool,

    /// Preprocess only, output preprocessed source to stdout
    #[clap(short = 'E')]
    pub preprocess_only: bool,

    /// Preprocessor options
    #[clap(flatten)]
    pub preprocessor: PreprocessorOptions,

    /// Suppress line markers in preprocessor output
    #[clap(short = 'P')]
    pub suppress_line_markers: bool,

    /// Retain comments in preprocessor output
    #[clap(short = 'C', long = "retain-comments")]
    pub retain_comments: bool,

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
    pub dump_parser: bool,
    pub preprocess_only: bool,
    pub verbose: bool,
    pub preprocessor: PreprocessorConfig,
    pub suppress_line_markers: bool,
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
            dump_parser: cli.dump_parser,
            preprocess_only: cli.preprocess_only,
            verbose: cli.verbose,
            preprocessor: PreprocessorConfig {
                max_include_depth: cli.preprocessor.max_include_depth,
                system_include_paths: vec![],
            },
            suppress_line_markers: cli.suppress_line_markers,
            include_paths: cli.include_paths,
            defines,
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
        debug!("Starting compilation of file: {}", source_path.display());
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
                lang_options.clone(),  // TODO: make it to just borrow
                target_triple.clone(), // TODO: make it to just borrow
                &self.config.preprocessor,
            );

            // Preprocessor is dropped here, releasing the borrow on diagnostics
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

        // Check for preprocessing errors and stop if any
        if self.diagnostics.has_errors() {
            return Ok(()); // Stop processing this file
        }

        // If preprocess only, dump the preprocessed output
        if self.config.preprocess_only {
            self.dump_preprocessed_output(&pp_tokens, self.config.suppress_line_markers)?;
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

            // Lexer is dropped here, releasing the borrow on diagnostics
            lexer.tokenize_all()
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
            return Ok(()); // Stop processing this file
        }

        // print parser AST to check
        if self.config.dump_parser {
            self.dump_parser(&ast);
            return Ok(());
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
                max_source_lines: None,
                output_path: output_path.clone(),
            };
            let mut dumper = AstDumper::new(
                &ast,
                &symbol_table,
                &mut self.diagnostics,
                &mut self.source_manager,
                &lang_options,
                &target_triple,
                dump_config,
            );
            let html = dumper.generate_html().map_err(|e| {
                CompilerError::AstDumpError(format!("HTML generation error: {:?}", e))
            })?;

            println!("Dumping AST to {}...", output_path.display());
            fs::write(&output_path, html)
                .map_err(|e| CompilerError::IoError(format!("Failed to write AST dump: {}", e)))?;
        }

        Ok(())
    }

    fn dump_preprocessed_output(
        &self,
        pp_tokens: &[crate::pp::PPToken],
        suppress_line_markers: bool,
    ) -> Result<(), CompilerError> {
        if pp_tokens.is_empty() {
            return Ok(());
        }

        // Get the source buffer for the first token
        let first_token = &pp_tokens[0];
        let mut current_file_id = first_token.location.source_id();
        let mut current_buffer = self.source_manager.get_buffer(current_file_id);
        let mut last_pos = 0u32;

        for token in pp_tokens {
            if token.kind == crate::pp::PPTokenKind::Eof {
                break;
            }

            // Check for file transitions and emit line markers
            if token.location.source_id() != current_file_id {
                // Emit line marker for file transition (unless suppressed)
                if !suppress_line_markers {
                    if let Some(file_info) = self.source_manager.get_file_info(token.location.source_id()) {
                        let line = self.source_manager.get_line_column(token.location)
                            .map(|(l, _)| l)
                            .unwrap_or(1);
                        let filename = file_info.path.file_name()
                            .and_then(|n| n.to_str())
                            .unwrap_or("<unknown>");

                        // For now, use flag "1" for entering file (simplified)
                        println!("# {} \"{}\" 1", line, filename);
                    }
                }

                current_file_id = token.location.source_id();
                current_buffer = self.source_manager.get_buffer(current_file_id);
                last_pos = token.location.offset();
            }

            // Handle macro-expanded tokens (Level A: use canonical spelling)
            if token.flags.contains(PPTokenFlags::MACRO_EXPANDED) {
                // For macro-expanded tokens, just print the canonical spelling
                // No whitespace reconstruction for Level A - these tokens don't have
                // meaningful source locations for whitespace calculation
                print!("{}", token.get_text());
                // Don't update last_pos for macro-expanded tokens
                continue;
            }

            let token_start = token.location.offset();
            let token_end = token_start + token.length as u32;

            // Print all bytes between last_pos and token_start (whitespace, comments)
            if token_start > last_pos {
                let slice = &current_buffer[last_pos as usize..token_start as usize];
                // Convert to string, assuming UTF-8 (preprocessor should ensure this)
                if let Ok(text) = std::str::from_utf8(slice) {
                    print!("{}", text);
                }
            }

            // Print the token's raw bytes from source
            let token_slice = token.get_raw_slice(current_buffer);
            if let Ok(text) = std::str::from_utf8(token_slice) {
                print!("{}", text);
            }

            last_pos = token_end;
        }

        println!();
        Ok(())
    }

    fn dump_parser(&self, ast: &Ast) {
        for (i, node) in ast.nodes.iter().enumerate() {
            if matches!(node.kind, NodeKind::Dummy) {
                continue;
            }
            print!("{}: ", i + 1);
            self.dump_parser_kind(&node.kind);
        }
    }

    fn dump_parser_kind(&self, kind: &NodeKind) {
        match kind {
            NodeKind::TranslationUnit(tu) => {
                println!(
                    "TranslationUnit([{}])",
                    tu.iter().map(|&r| r.get().to_string()).join(", ")
                );
            }
            NodeKind::LiteralInt(i) => println!("LiteralInt({})", i),
            NodeKind::LiteralFloat(f) => println!("LiteralFloat({})", f),
            NodeKind::LiteralString(s) => println!("LiteralString({})", s),
            NodeKind::LiteralChar(c) => println!("LiteralChar('{}')", c.escape_default()),
            NodeKind::Ident(sym, _) => println!("Ident({})", sym),
            NodeKind::UnaryOp(op, operand) => println!("UnaryOp({:?}, {})", op, operand.get()),
            NodeKind::BinaryOp(op, left, right) => {
                println!("BinaryOp({:?}, {}, {})", op, left.get(), right.get())
            }
            NodeKind::TernaryOp(cond, then, else_) => {
                println!("TernaryOp({}, {}, {})", cond.get(), then.get(), else_.get())
            }
            NodeKind::PostIncrement(expr) => println!("PostIncrement({})", expr.get()),
            NodeKind::PostDecrement(expr) => println!("PostDecrement({})", expr.get()),
            NodeKind::Assignment(op, lhs, rhs) => {
                println!("Assignment({:?}, {}, {})", op, lhs.get(), rhs.get())
            }
            NodeKind::FunctionCall(func, args) => println!(
                "FunctionCall({}, [{}])",
                func.get(),
                args.iter().map(|&r| r.get().to_string()).join(", ")
            ),
            NodeKind::MemberAccess(obj, field, is_arrow) => println!(
                "MemberAccess({}, {}, {})",
                obj.get(),
                field,
                if *is_arrow { "->" } else { "." }
            ),
            NodeKind::IndexAccess(array, index) => {
                println!("IndexAccess({}, {})", array.get(), index.get())
            }
            NodeKind::Cast(ty, expr) => println!("Cast({}, {})", ty.get(), expr.get()),
            NodeKind::SizeOfExpr(expr) => println!("SizeOfExpr({})", expr.get()),
            NodeKind::SizeOfType(ty) => println!("SizeOfType({})", ty.get()),
            NodeKind::AlignOf(ty) => println!("AlignOf({})", ty.get()),
            NodeKind::CompoundLiteral(ty, init) => {
                println!("CompoundLiteral({}, {})", ty.get(), init.get())
            }
            NodeKind::GenericSelection(ctrl, assocs) => println!(
                "GenericSelection({}, {} associations)",
                ctrl.get(),
                assocs.len()
            ),
            NodeKind::VaArg(va_list, ty) => println!("VaArg({}, {})", va_list.get(), ty.get()),
            NodeKind::CompoundStatement(stmts) => println!(
                "CompoundStatement([{}])",
                stmts.iter().map(|&r| r.get().to_string()).join(", ")
            ),
            NodeKind::If(if_stmt) => println!(
                "If(condition={}, then={}, else={})",
                if_stmt.condition.get(),
                if_stmt.then_branch.get(),
                if_stmt
                    .else_branch
                    .map(|r| r.get().to_string())
                    .unwrap_or("none".to_string())
            ),
            NodeKind::While(while_stmt) => println!(
                "While(condition={}, body={})",
                while_stmt.condition.get(),
                while_stmt.body.get()
            ),
            NodeKind::DoWhile(body, cond) => {
                println!("DoWhile(body={}, condition={})", body.get(), cond.get())
            }
            NodeKind::For(for_stmt) => println!(
                "For(init={}, condition={}, increment={}, body={})",
                for_stmt
                    .init
                    .map(|r| r.get().to_string())
                    .unwrap_or("none".to_string()),
                for_stmt
                    .condition
                    .map(|r| r.get().to_string())
                    .unwrap_or("none".to_string()),
                for_stmt
                    .increment
                    .map(|r| r.get().to_string())
                    .unwrap_or("none".to_string()),
                for_stmt.body.get()
            ),
            NodeKind::Return(expr) => println!(
                "Return({})",
                expr.map(|r| r.get().to_string())
                    .unwrap_or("void".to_string())
            ),
            NodeKind::Break => println!("Break"),
            NodeKind::Continue => println!("Continue"),
            NodeKind::Goto(label) => println!("Goto({})", label),
            NodeKind::Label(label, stmt) => println!("Label({}, {})", label, stmt.get()),
            NodeKind::Switch(cond, body) => {
                println!("Switch(condition={}, body={})", cond.get(), body.get())
            }
            NodeKind::Case(expr, stmt) => println!("Case({}, {})", expr.get(), stmt.get()),
            NodeKind::CaseRange(start, end, stmt) => {
                println!("CaseRange({}, {}, {})", start.get(), end.get(), stmt.get())
            }
            NodeKind::Default(stmt) => println!("Default({})", stmt.get()),
            NodeKind::ExpressionStatement(expr) => println!(
                "ExpressionStatement({})",
                expr.map(|r| r.get().to_string())
                    .unwrap_or("none".to_string())
            ),
            NodeKind::EmptyStatement => println!("EmptyStatement"),
            NodeKind::Declaration(decl) => {
                println!(
                    "Declaration({} specifiers, init_declarators = [{}])",
                    decl.specifiers.len(),
                    decl.init_declarators
                        .iter()
                        .map(|x| { format!("{:?} {:?}", x.declarator, x.initializer) })
                        .join(",")
                        .to_string()
                );
            }
            NodeKind::FunctionDef(func_def) => println!(
                "FunctionDef({} specifiers, body={})",
                func_def.specifiers.len(),
                func_def.body.get()
            ),
            NodeKind::EnumConstant(name, value) => println!(
                "EnumConstant({}, {})",
                name,
                value
                    .map(|r| r.get().to_string())
                    .unwrap_or("auto".to_string())
            ),
            NodeKind::StaticAssert(cond, msg) => {
                println!("StaticAssert(condition={}, message={})", cond.get(), msg)
            }
            NodeKind::Dummy => println!("DUMMY"),
        }
    }

    fn report_errors(&self) -> Result<(), CompilerError> {
        if self.diagnostics.has_errors() {
            let formatter = crate::diagnostic::ErrorFormatter::default();
            formatter.print_diagnostics(self.diagnostics.diagnostics(), &self.source_manager);
            // Continue instead of failing
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
