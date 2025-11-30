//! Output formatting and file writing module
// //!
// //! This module handles various output formats including preprocessed source,
// //! parser AST dumps, and HTML AST dumps.

use itertools::Itertools;
use std::fs;
use std::path::PathBuf;

use crate::ast::{Ast, NodeKind};
use crate::ast_dumper::{AstDumper, DumpConfig};
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::pp::PPToken;
use crate::semantic::SymbolTable;
use crate::source_manager::SourceManager;
use target_lexicon::Triple;

use super::cli::CompileConfig;
use super::compiler::CompilerError;

/// Handler for various output formats
pub struct OutputHandler;

impl Default for OutputHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl OutputHandler {
    /// Create a new output handler
    pub fn new() -> Self {
        OutputHandler
    }

    /// Dump preprocessed output to stdout
    pub fn dump_preprocessed_output(
        &self,
        pp_tokens: &[PPToken],
        suppress_line_markers: bool,
        source_manager: &SourceManager,
    ) -> Result<(), CompilerError> {
        if pp_tokens.is_empty() {
            return Ok(());
        }

        // Get the source buffer for the first token
        let first_token = &pp_tokens[0];
        let mut current_file_id = first_token.location.source_id();
        let mut current_buffer = source_manager.get_buffer(current_file_id);
        let mut last_pos = 0u32;
        let mut last_was_macro_expanded = false;

        for token in pp_tokens {
            if token.kind == crate::pp::PPTokenKind::Eof {
                break;
            }

            // Check for file transitions and emit line markers
            if token.location.source_id() != current_file_id {
                // Emit line marker for file transition (unless suppressed)
                if !suppress_line_markers
                    && let Some(file_info) = source_manager.get_file_info(token.location.source_id())
                {
                    let line = source_manager
                        .get_line_column(token.location)
                        .map(|(l, _)| l)
                        .unwrap_or(1);
                    let filename = file_info
                        .path
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("<unknown>");

                    // For now, use flag "1" for entering file (simplified)
                    println!("# {} \\\"{}\\\" 1", line, filename);
                }

                current_file_id = token.location.source_id();
                current_buffer = source_manager.get_buffer(current_file_id);
                last_pos = token.location.offset();
                last_was_macro_expanded = false;
            }

            // Handle macro-expanded tokens (Level A: use canonical spelling)
            if token.flags.contains(crate::pp::PPTokenFlags::MACRO_EXPANDED) {
                // Add space between consecutive macro-expanded tokens
                if last_was_macro_expanded {
                    print!(" ");
                }
                // For macro-expanded tokens, just print the canonical spelling
                // No whitespace reconstruction for Level A - these tokens don't have
                // meaningful source locations for whitespace calculation
                print!("{}", token.get_text());
                last_was_macro_expanded = true;
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
                    // Only print slices that are all whitespace to avoid printing directive text
                    if text.chars().all(|c| c.is_whitespace()) {
                        print!("{}", text);
                    }
                }
            }

            // Print the token's raw bytes from source
            let token_slice = token.get_raw_slice(current_buffer);
            if let Ok(text) = std::str::from_utf8(token_slice) {
                print!("{}", text);
            }

            last_pos = token_end;
            last_was_macro_expanded = false;
        }

        println!();
        Ok(())
    }

    /// Dump parser AST to stdout
    pub fn dump_parser(&self, ast: &Ast) {
        for (i, node) in ast.nodes.iter().enumerate() {
            if matches!(node.kind, NodeKind::Dummy) {
                continue;
            }
            print!("{}: ", i + 1);
            self.dump_parser_kind(&node.kind);
        }
    }

    /// Dump a single AST node kind
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
            NodeKind::LiteralChar(c) => println!("LiteralChar('{}')", *c as char),
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
            NodeKind::GenericSelection(ctrl, assocs) => {
                println!("GenericSelection({}, {} associations)", ctrl.get(), assocs.len())
            }
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
                for_stmt.init.map(|r| r.get().to_string()).unwrap_or("none".to_string()),
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
                expr.map(|r| r.get().to_string()).unwrap_or("void".to_string())
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
                expr.map(|r| r.get().to_string()).unwrap_or("none".to_string())
            ),
            NodeKind::EmptyStatement => println!("EmptyStatement"),
            NodeKind::Declaration(decl) => {
                println!(
                    "Declaration({} specifiers, init_declarators = [{}])",
                    decl.specifiers.len(),
                    decl.init_declarators
                        .iter()
                        .map(|x| { format!("{:?} {:?}", x.declarator, x.initializer) })
                        .join(", ")
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
                value.map(|r| r.get().to_string()).unwrap_or("auto".to_string())
            ),
            NodeKind::StaticAssert(cond, msg) => {
                println!("StaticAssert(condition={}, message={})", cond.get(), msg)
            }
            NodeKind::Dummy => println!("DUMMY"),
        }
    }

    /// Dump AST to HTML file
    pub fn dump_ast(&self, args: &mut AstDumpArgs, config: &CompileConfig) -> Result<(), CompilerError> {
        let output_path = config
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
            args.ast,
            args.symbol_table,
            args.diagnostics,
            args.source_manager,
            args.lang_options,
            args.target_triple,
            dump_config,
        );
        let html = dumper
            .generate_html()
            .map_err(|e| CompilerError::AstDumpError(format!("HTML generation error: {:?}", e)))?;

        println!("Dumping AST to {}...", output_path.display());
        fs::write(&output_path, html)
            .map_err(|e| CompilerError::IoError(format!("Failed to write AST dump: {}", e)))?;

        Ok(())
    }
}
pub struct AstDumpArgs<'a> {
    pub ast: &'a Ast,
    pub symbol_table: &'a SymbolTable,
    pub diagnostics: &'a mut DiagnosticEngine,
    pub source_manager: &'a mut SourceManager,
    pub lang_options: &'a LangOptions,
    pub target_triple: &'a Triple,
}
