//! Output formatting and file writing module
//!
//! This module handles various output formats including preprocessed source,
//! parser AST dumps, and HTML AST dumps.

use hashbrown::HashSet;
use itertools::Itertools;

use crate::ast::{Ast, NodeKind};
use crate::pp::PPToken;
use crate::semantic::{SymbolRef, TypeRegistry};
use crate::source_manager::SourceManager;

use super::compiler::DriverError;

/// Handler for various output formats
pub(crate) struct OutputHandler;

impl Default for OutputHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl OutputHandler {
    /// Create a new output handler
    pub(crate) fn new() -> Self {
        OutputHandler
    }

    /// Dump preprocessed output to stdout
    pub(crate) fn dump_preprocessed_output(
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
    pub(crate) fn dump_parser(&self, ast: &Ast, symbol_table: Option<&crate::semantic::SymbolTable>) {
        for (i, node) in ast.nodes.iter().enumerate() {
            if matches!(node.kind, NodeKind::Dummy) {
                continue;
            }
            print!("{}: ", i + 1);
            self.dump_parser_kind(&node.kind, symbol_table);
        }
    }

    /// Dump TypeRegistry information for used TypeRefs in the AST
    pub(crate) fn dump_type_registry(&self, ast: &Ast, registry: &TypeRegistry) {
        // Collect all TypeRefs used in the AST
        let mut used_type_refs = HashSet::new();

        for node in &ast.nodes {
            self.collect_type_refs_from_node(&node.kind, &mut used_type_refs);
        }

        if used_type_refs.is_empty() {
            return;
        }

        // Print header
        println!("\n=== TypeRegistry (Used TypeRefs) ===");

        // Sort TypeRefs for consistent output
        let mut sorted_type_refs: Vec<_> = used_type_refs.into_iter().collect();
        sorted_type_refs.sort_by_key(|ty_ref| ty_ref.get());

        // Dump each used TypeRef with user-friendly formatting
        for ty_ref in sorted_type_refs {
            let ty = registry.get(ty_ref);
            let formatted_type = self.format_type_kind_user_friendly(&ty.kind, registry);
            println!("TypeRef({}): {}", ty_ref.get(), formatted_type);
        }
    }

    /// Format TypeKind in a user-friendly way for TypeRegistry dump
    fn format_type_kind_user_friendly(&self, kind: &crate::semantic::TypeKind, registry: &TypeRegistry) -> String {
        use crate::semantic::TypeKind;

        match kind {
            // Basic types - use the existing dump format
            TypeKind::Void => "void".to_string(),
            TypeKind::Bool => "_Bool".to_string(),
            TypeKind::Char { is_signed } => {
                if *is_signed {
                    "char".to_string()
                } else {
                    "unsigned char".to_string()
                }
            }
            TypeKind::Short { is_signed } => {
                if *is_signed {
                    "short".to_string()
                } else {
                    "unsigned short".to_string()
                }
            }
            TypeKind::Int { is_signed } => {
                if *is_signed {
                    "int".to_string()
                } else {
                    "unsigned int".to_string()
                }
            }
            TypeKind::Long {
                is_signed,
                is_long_long,
            } => {
                if *is_long_long {
                    if *is_signed {
                        "long long".to_string()
                    } else {
                        "unsigned long long".to_string()
                    }
                } else if *is_signed {
                    "long".to_string()
                } else {
                    "unsigned long".to_string()
                }
            }
            TypeKind::Float => "float".to_string(),
            TypeKind::Double { is_long_double } => {
                if *is_long_double {
                    "long double".to_string()
                } else {
                    "double".to_string()
                }
            }
            TypeKind::Complex { .. } => "_Complex".to_string(),
            TypeKind::Error => "<error>".to_string(),

            // Complex types - provide more detailed information
            TypeKind::Pointer { pointee } => {
                let pointee_type = registry.get(*pointee);
                format!("{}*", self.format_type_kind_user_friendly(&pointee_type.kind, registry))
            }
            TypeKind::Array { element_type, size } => {
                let element_str = self.format_type_kind_user_friendly(&registry.get(*element_type).kind, registry);
                match size {
                    crate::semantic::ArraySizeType::Constant(len) => format!("{}[{}]", element_str, len),
                    crate::semantic::ArraySizeType::Incomplete => format!("{}[]", element_str),
                    crate::semantic::ArraySizeType::Variable(_) => "<VLA>".to_string(),
                    crate::semantic::ArraySizeType::Star => format!("{}[*]", element_str),
                }
            }
            TypeKind::Function {
                return_type,
                parameters,
                is_variadic,
            } => {
                let return_str = self.format_type_kind_user_friendly(&registry.get(*return_type).kind, registry);
                let mut param_strs = Vec::new();
                for param in parameters {
                    let param_str =
                        self.format_type_kind_user_friendly(&registry.get(param.param_type.ty).kind, registry);
                    param_strs.push(param_str);
                }
                let params = param_strs.join(", ");
                let variadic = if *is_variadic { ", ..." } else { "" };
                format!("{}({}{})", return_str, params, variadic)
            }
            TypeKind::Record { tag, is_union, .. } => {
                let kind_str = if *is_union { "union" } else { "struct" };
                if let Some(tag_name) = tag {
                    format!("{} {}", kind_str, tag_name)
                } else {
                    format!("{} (anonymous)", kind_str)
                }
            }
            TypeKind::Enum { tag, .. } => {
                if let Some(tag_name) = tag {
                    format!("enum {}", tag_name)
                } else {
                    "enum (anonymous)".to_string()
                }
            }
        }
    }

    /// Collect TypeRefs from a NodeKind
    fn collect_type_refs_from_node(&self, kind: &NodeKind, type_refs: &mut HashSet<crate::semantic::TypeRef>) {
        match kind {
            // Direct TypeRef usage
            NodeKind::VaArg(_, ty_ref) => {
                type_refs.insert(*ty_ref);
            }
            NodeKind::Function(func_data) => {
                type_refs.insert(func_data.ty);
                // Also collect from function parameters
                for param in &func_data.params {
                    type_refs.insert(param.ty.ty);
                }
            }
            NodeKind::FunctionDecl(func_decl) => {
                type_refs.insert(func_decl.ty);
            }
            NodeKind::RecordDecl(record_decl) => {
                type_refs.insert(record_decl.ty);
                // Also collect from record members
                for member in &record_decl.members {
                    type_refs.insert(member.ty.ty);
                }
            }
            NodeKind::EnumDecl(enum_decl) => {
                type_refs.insert(enum_decl.ty);
            }

            // QualType usage (contains TypeRef)
            NodeKind::Cast(qual_type, _) => {
                type_refs.insert(qual_type.ty);
            }
            NodeKind::SizeOfType(qual_type) => {
                type_refs.insert(qual_type.ty);
            }
            NodeKind::AlignOf(qual_type) => {
                type_refs.insert(qual_type.ty);
            }
            NodeKind::CompoundLiteral(qual_type, _) => {
                type_refs.insert(qual_type.ty);
            }
            NodeKind::VarDecl(var_decl) => {
                type_refs.insert(var_decl.ty.ty);
            }
            NodeKind::TypedefDecl(typedef_decl) => {
                type_refs.insert(typedef_decl.ty.ty);
            }
            NodeKind::GenericSelection(_, assocs) => {
                for assoc in assocs {
                    if let Some(qual_type) = assoc.ty {
                        type_refs.insert(qual_type.ty);
                    }
                }
            }

            // Literal nodes - don't contain TypeRefs
            NodeKind::LiteralInt(_)
            | NodeKind::LiteralFloat(_)
            | NodeKind::LiteralString(_)
            | NodeKind::LiteralChar(_)
            | NodeKind::Ident(_, _) => {
                // These don't contain TypeRefs
            }

            // Statement types that don't directly contain TypeRefs
            NodeKind::TranslationUnit(_)
            | NodeKind::CompoundStatement(_)
            | NodeKind::If(_)
            | NodeKind::While(_)
            | NodeKind::DoWhile(_, _)
            | NodeKind::For(_)
            | NodeKind::Return(_)
            | NodeKind::Break
            | NodeKind::Continue
            | NodeKind::Goto(_, _)
            | NodeKind::Label(_, _, _)
            | NodeKind::Switch(_, _)
            | NodeKind::Case(_, _)
            | NodeKind::CaseRange(_, _, _)
            | NodeKind::Default(_)
            | NodeKind::ExpressionStatement(_)
            | NodeKind::EmptyStatement
            | NodeKind::DeclarationList(_)
            | NodeKind::InitializerList(_)
            | NodeKind::StaticAssert(_, _)
            | NodeKind::EnumConstant(_, _)
            | NodeKind::Declaration(_)
            | NodeKind::FunctionDef(_)
            | NodeKind::Dummy => {
                // These don't directly contain TypeRefs
            }

            // Parser-specific nodes that use ParsedType (not semantic TypeRef)
            NodeKind::ParsedCast(_, _)
            | NodeKind::ParsedSizeOfType(_)
            | NodeKind::ParsedAlignOf(_)
            | NodeKind::ParsedCompoundLiteral(_, _)
            | NodeKind::ParsedGenericSelection(_, _) => {
                // These use ParsedType, not semantic TypeRef
            }

            // GNU extensions
            NodeKind::GnuStatementExpression(_, _) => {
                // Doesn't directly contain TypeRef
            }

            // Expression nodes with NodeRef children - types handled during traversal
            NodeKind::FunctionCall(_, _)
            | NodeKind::BinaryOp(_, _, _)
            | NodeKind::UnaryOp(_, _)
            | NodeKind::TernaryOp(_, _, _)
            | NodeKind::PostIncrement(_)
            | NodeKind::PostDecrement(_)
            | NodeKind::Assignment(_, _, _)
            | NodeKind::MemberAccess(_, _, _)
            | NodeKind::IndexAccess(_, _)
            | NodeKind::SizeOfExpr(_) => {
                // These don't directly contain TypeRefs, they will be handled when we process child nodes
            }
        }
    }

    /// Get function name from symbol entry reference
    fn get_function_name(&self, symbol_ref: SymbolRef, symbol_table: Option<&crate::semantic::SymbolTable>) -> String {
        if let Some(table) = symbol_table {
            let entry = table.get_symbol(symbol_ref);
            return entry.name.to_string();
        }
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
            crate::ast::nodes::DeclSpecifier::TypeQualifier(qual) => {
                let s = format!("{:?}", qual);
                if s == "Atomic" {
                    "_Atomic".to_string()
                } else {
                    s.to_lowercase()
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

    /// Format a DesignatedInitializer for display
    fn format_designated_initializer(&self, init: &crate::ast::nodes::DesignatedInitializer) -> String {
        let mut result = String::new();
        for designator in &init.designation {
            match designator {
                crate::ast::nodes::Designator::FieldName(name) => {
                    result.push_str(&format!(".{}", name));
                }
                crate::ast::nodes::Designator::ArrayIndex(index) => {
                    result.push_str(&format!("[{}]", index.get()));
                }
                crate::ast::nodes::Designator::GnuArrayRange(start, end) => {
                    result.push_str(&format!("[{} ... {}]", start.get(), end.get()));
                }
            }
        }

        if !init.designation.is_empty() {
            result.push_str(" = ");
        }

        result.push_str(&init.initializer.get().to_string());
        result
    }

    /// Dump a single AST node kind
    fn dump_parser_kind(&self, kind: &NodeKind, symbol_table: Option<&crate::semantic::SymbolTable>) {
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
            NodeKind::Cast(ty, expr) => println!("Cast({}, {})", ty, expr.get()),
            NodeKind::SizeOfExpr(expr) => println!("SizeOfExpr({})", expr.get()),
            NodeKind::SizeOfType(ty) => println!("SizeOfType({})", ty),
            NodeKind::AlignOf(ty) => println!("AlignOf({})", ty),
            NodeKind::CompoundLiteral(ty, init) => {
                println!("CompoundLiteral({}, {})", ty, init.get())
            }
            // Parser variants with ParsedType
            NodeKind::ParsedCast(_, expr) => println!("ParsedCast(PARSED_TYPE, {})", expr.get()),
            NodeKind::ParsedSizeOfType(_) => println!("ParsedSizeOfType(PARSED_TYPE)"),
            NodeKind::ParsedAlignOf(_) => println!("ParsedAlignOf(PARSED_TYPE)"),
            NodeKind::ParsedCompoundLiteral(_, init) => println!("ParsedCompoundLiteral(PARSED_TYPE, {})", init.get()),
            NodeKind::ParsedGenericSelection(ctrl, assocs) => {
                println!("ParsedGenericSelection({}, {} associations)", ctrl.get(), assocs.len())
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
            NodeKind::Goto(label, _) => println!("Goto({})", label),
            NodeKind::Label(label, stmt, _) => println!("Label({}, {})", label, stmt.get()),
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
                let func_name = self.get_function_name(function_data.symbol, symbol_table);
                println!(
                    "Function(name={}, ty={}, body={})",
                    func_name,
                    function_data.ty,
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
                    var_decl.name, var_decl.ty, var_decl.storage
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
                println!("TypedefDecl(name={}, ty={})", typedef_decl.name, typedef_decl.ty)
            }
            NodeKind::RecordDecl(record_decl) => {
                println!(
                    "RecordDecl(name={:?}, ty={}, is_union={})",
                    record_decl.name,
                    record_decl.ty.get(),
                    record_decl.is_union
                )
            }
            NodeKind::EnumDecl(enum_decl) => {
                println!(
                    "EnumDecl(name={:?}, ty={}, members=[{}])",
                    enum_decl.name,
                    enum_decl.ty.get(),
                    enum_decl
                        .members
                        .iter()
                        .map(|m| format!("{}={}", m.name, m.value))
                        .join(", ")
                )
            }
            NodeKind::DeclarationList(stmts) => println!(
                "DeclarationList([{}])",
                stmts.iter().map(|&r| r.get().to_string()).join(", ")
            ),
            NodeKind::InitializerList(list) => println!(
                "InitializerList([{}])",
                list.iter().map(|r| self.format_designated_initializer(r)).join(", ")
            ),
            NodeKind::Dummy => println!("DUMMY"),
        }
    }
}
