//! Output formatting and file writing module
//!
//! This module handles various output formats including preprocessed source,
//! parser AST dumps, and HTML AST dumps.

use itertools::Itertools;

use crate::ast::{Ast, NodeKind};
use crate::pp::PPToken;
use crate::source_manager::SourceManager;

use super::compiler::DriverError;

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
    ) -> Result<(), DriverError> {
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
                    println!("# {} \"{}\" 1", line, filename);
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

    /// Get function name from symbol entry reference
    fn get_function_name(&self, symbol_ref: crate::ast::SymbolEntryRef) -> String {
        // For now, return a placeholder since we don't have access to the symbol table here
        // In a real implementation, we would need access to the symbol table
        format!("func_{}", symbol_ref.get())
    }

    /// Format a DeclSpecifier for display
    fn format_decl_specifier(&self, specifier: &crate::ast::nodes::DeclSpecifier) -> String {
        match specifier {
            crate::ast::nodes::DeclSpecifier::StorageClass(storage) => match storage {
                crate::ast::nodes::StorageClass::Typedef => "typedef".to_string(),
                crate::ast::nodes::StorageClass::Extern => "extern".to_string(),
                crate::ast::nodes::StorageClass::Static => "static".to_string(),
                crate::ast::nodes::StorageClass::Auto => "auto".to_string(),
                crate::ast::nodes::StorageClass::Register => "register".to_string(),
                crate::ast::nodes::StorageClass::ThreadLocal => "_Thread_local".to_string(),
            },
            crate::ast::nodes::DeclSpecifier::TypeQualifiers(quals) => {
                let mut parts = Vec::new();
                if quals.contains(crate::ast::types::TypeQualifiers::CONST) {
                    parts.push("const");
                }
                if quals.contains(crate::ast::types::TypeQualifiers::VOLATILE) {
                    parts.push("volatile");
                }
                if quals.contains(crate::ast::types::TypeQualifiers::RESTRICT) {
                    parts.push("restrict");
                }
                if quals.contains(crate::ast::types::TypeQualifiers::ATOMIC) {
                    parts.push("_Atomic");
                }
                if parts.is_empty() {
                    "TypeQualifiers(0x0)".to_string()
                } else {
                    parts.join(" ")
                }
            }
            crate::ast::nodes::DeclSpecifier::FunctionSpecifiers(func_spec) => {
                let mut parts = Vec::new();
                if func_spec.contains(crate::ast::nodes::FunctionSpecifiers::INLINE) {
                    parts.push("inline");
                }
                if func_spec.contains(crate::ast::nodes::FunctionSpecifiers::NORETURN) {
                    parts.push("_Noreturn");
                }
                if parts.is_empty() {
                    "FunctionSpecifiers(0x0)".to_string()
                } else {
                    parts.join(" ")
                }
            }
            crate::ast::nodes::DeclSpecifier::AlignmentSpecifier(_) => "_Alignas(...)".to_string(),
            crate::ast::nodes::DeclSpecifier::TypeSpecifier(type_spec) => match type_spec {
                crate::ast::nodes::TypeSpecifier::Void => "void".to_string(),
                crate::ast::nodes::TypeSpecifier::Char => "char".to_string(),
                crate::ast::nodes::TypeSpecifier::Short => "short".to_string(),
                crate::ast::nodes::TypeSpecifier::Int => "int".to_string(),
                crate::ast::nodes::TypeSpecifier::Long => "long".to_string(),
                crate::ast::nodes::TypeSpecifier::LongLong => "long long".to_string(),
                crate::ast::nodes::TypeSpecifier::Float => "float".to_string(),
                crate::ast::nodes::TypeSpecifier::Double => "double".to_string(),
                crate::ast::nodes::TypeSpecifier::LongDouble => "long double".to_string(),
                crate::ast::nodes::TypeSpecifier::Signed => "signed".to_string(),
                crate::ast::nodes::TypeSpecifier::Unsigned => "unsigned".to_string(),
                crate::ast::nodes::TypeSpecifier::Bool => "_Bool".to_string(),
                crate::ast::nodes::TypeSpecifier::Complex => "_Complex".to_string(),
                crate::ast::nodes::TypeSpecifier::Atomic(_) => "_Atomic(...)".to_string(),
                crate::ast::nodes::TypeSpecifier::Record(is_union, tag, _) => {
                    let type_name = if *is_union { "union" } else { "struct" };
                    match tag {
                        Some(symbol) => format!("{} {}", type_name, symbol),
                        None => type_name.to_string(),
                    }
                }
                crate::ast::nodes::TypeSpecifier::Enum(tag, _) => match tag {
                    Some(symbol) => format!("enum {}", symbol),
                    None => "enum".to_string(),
                },
                crate::ast::nodes::TypeSpecifier::TypedefName(symbol) => {
                    format!("typedef {}", symbol)
                }
            },
            crate::ast::nodes::DeclSpecifier::Attribute => "__attribute__(...)".to_string(),
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
            NodeKind::GnuStatementExpression(compound_stmt, result_expr) => {
                println!("GnuStatementExpression({}, {})", compound_stmt.get(), result_expr.get())
            }
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
                let specifiers_str = decl
                    .specifiers
                    .iter()
                    .map(|spec| self.format_decl_specifier(spec))
                    .join(", ");
                println!(
                    "Declaration({}, init_declarators = [{}])",
                    specifiers_str,
                    decl.init_declarators
                        .iter()
                        .map(|x| { format!("{:?} {:?}", x.declarator, x.initializer) })
                        .join(", ")
                );
            }
            NodeKind::FunctionDef(func_def) => {
                let specifiers_str = func_def
                    .specifiers
                    .iter()
                    .map(|spec| self.format_decl_specifier(spec))
                    .join(", ");
                println!("FunctionDef({}, body={})", specifiers_str, func_def.body.get());
            }
            NodeKind::Function(function_data) => {
                // Get the function name from the symbol table
                let func_name = self.get_function_name(function_data.symbol);
                println!(
                    "Function(name={}, ty={}, body={})",
                    func_name,
                    function_data.ty.get(),
                    function_data.body.get()
                )
            }
            NodeKind::EnumConstant(name, value) => println!(
                "EnumConstant({}, {})",
                name,
                value.map(|r| r.get().to_string()).unwrap_or("auto".to_string())
            ),
            NodeKind::StaticAssert(cond, msg) => {
                println!("StaticAssert(condition={}, message={})", cond.get(), msg)
            }
            NodeKind::VarDecl(var_decl) => {
                println!(
                    "VarDecl(name={}, ty={}, storage={:?})",
                    var_decl.name,
                    var_decl.ty.get(),
                    var_decl.storage
                )
            }
            NodeKind::FunctionDecl(func_decl) => {
                println!(
                    "FunctionDecl(name={}, ty={}, storage={:?})",
                    func_decl.name,
                    func_decl.ty.get(),
                    func_decl.storage
                )
            }
            NodeKind::TypedefDecl(typedef_decl) => {
                println!("TypedefDecl(name={}, ty={})", typedef_decl.name, typedef_decl.ty.get())
            }
            NodeKind::RecordDecl(record_decl) => {
                println!(
                    "RecordDecl(name={:?}, ty={}, is_union={})",
                    record_decl.name,
                    record_decl.ty.get(),
                    record_decl.is_union
                )
            }
            NodeKind::DeclarationList(stmts) => println!(
                "DeclarationList([{}])",
                stmts.iter().map(|&r| r.get().to_string()).join(", ")
            ),
            NodeKind::Dummy => println!("DUMMY"),
        }
    }
}
