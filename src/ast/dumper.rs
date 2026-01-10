//! AST Dumper module
//!
//! This module handles AST dumping for debugging and visualization.

use hashbrown::HashSet;
use itertools::Itertools;

use crate::ast::{Ast, DesignatedInitializer, Designator, NodeKind};
use crate::semantic::{ArraySizeType, SymbolRef, SymbolTable, TypeKind, TypeRef, TypeRegistry};

/// Dumper for AST
pub struct AstDumper;

impl AstDumper {
    /// Dump parser AST to stdout
    pub fn dump_parser(ast: &Ast, symbol_table: Option<&SymbolTable>) {
        for (i, kind) in ast.kinds.iter().enumerate() {
            if matches!(kind, NodeKind::Dummy) {
                continue;
            }
            print!("{}: ", i + 1);
            Self::dump_parser_kind(kind, symbol_table);
        }
    }

    /// Dump TypeRegistry information for used TypeRefs in the AST
    pub fn dump_type_registry(ast: &Ast, registry: &TypeRegistry) {
        // Collect all TypeRefs used in the AST
        let mut used_type_refs = HashSet::new();

        for kind in &ast.kinds {
            Self::collect_type_refs_from_node(kind, &mut used_type_refs);
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
            let formatted_type = Self::format_type_kind_user_friendly(&ty.kind, registry);
            println!("TypeRef({}): {}", ty_ref.get(), formatted_type);
        }
    }

    /// Format TypeKind in a user-friendly way for TypeRegistry dump
    #[allow(clippy::only_used_in_recursion)]
    fn format_type_kind_user_friendly(kind: &TypeKind, registry: &TypeRegistry) -> String {
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
                format!(
                    "{}*",
                    Self::format_type_kind_user_friendly(&pointee_type.kind, registry)
                )
            }
            TypeKind::Array { element_type, size } => {
                let element_str = Self::format_type_kind_user_friendly(&registry.get(*element_type).kind, registry);
                match size {
                    ArraySizeType::Constant(len) => format!("{}[{}]", element_str, len),
                    ArraySizeType::Incomplete => format!("{}[]", element_str),
                    ArraySizeType::Variable(_) => "<VLA>".to_string(),
                    ArraySizeType::Star => format!("{}[*]", element_str),
                }
            }
            TypeKind::Function {
                return_type,
                parameters,
                is_variadic,
            } => {
                let return_str = Self::format_type_kind_user_friendly(&registry.get(*return_type).kind, registry);
                let mut param_strs = Vec::new();
                for param in parameters {
                    let param_str =
                        Self::format_type_kind_user_friendly(&registry.get(param.param_type.ty()).kind, registry);
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
    fn collect_type_refs_from_node(kind: &NodeKind, type_refs: &mut HashSet<TypeRef>) {
        match kind {
            // Direct TypeRef usage
            NodeKind::VaArg(_, ty_ref) => {
                type_refs.insert(*ty_ref);
            }
            NodeKind::Function(func_data) => {
                type_refs.insert(func_data.ty);
                // Also collect from function parameters
                for param in &func_data.params {
                    type_refs.insert(param.ty.ty());
                }
            }
            NodeKind::FunctionDecl(func_decl) => {
                type_refs.insert(func_decl.ty);
            }
            NodeKind::RecordDecl(record_decl) => {
                type_refs.insert(record_decl.ty);
                // Also collect from record members
                for member in &record_decl.members {
                    type_refs.insert(member.ty.ty());
                }
            }
            NodeKind::EnumDecl(enum_decl) => {
                type_refs.insert(enum_decl.ty);
            }

            // QualType usage (contains TypeRef)
            NodeKind::Cast(qual_type, _) => {
                type_refs.insert(qual_type.ty());
            }
            NodeKind::SizeOfType(qual_type) => {
                type_refs.insert(qual_type.ty());
            }
            NodeKind::AlignOf(qual_type) => {
                type_refs.insert(qual_type.ty());
            }
            NodeKind::CompoundLiteral(qual_type, _) => {
                type_refs.insert(qual_type.ty());
            }
            NodeKind::VarDecl(var_decl) => {
                type_refs.insert(var_decl.ty.ty());
            }
            NodeKind::TypedefDecl(typedef_decl) => {
                type_refs.insert(typedef_decl.ty.ty());
            }
            NodeKind::GenericSelection(_, assocs) => {
                for assoc in assocs {
                    if let Some(qual_type) = assoc.ty {
                        type_refs.insert(qual_type.ty());
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
            | NodeKind::InitializerList(_)
            | NodeKind::StaticAssert(_, _)
            | NodeKind::EnumConstant(_, _)
            | NodeKind::Dummy => {
                // These don't directly contain TypeRefs
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
    fn get_function_name(symbol_ref: SymbolRef, symbol_table: Option<&SymbolTable>) -> String {
        if let Some(table) = symbol_table {
            let entry = table.get_symbol(symbol_ref);
            return entry.name.to_string();
        }
        format!("func_{}", symbol_ref.get())
    }

    /// Format a DesignatedInitializer for display
    fn format_designated_initializer(init: &DesignatedInitializer) -> String {
        let mut result = String::new();
        for designator in &init.designation {
            match designator {
                Designator::FieldName(name) => {
                    result.push_str(&format!(".{}", name));
                }
                Designator::ArrayIndex(index) => {
                    result.push_str(&format!("[{}]", index.get()));
                }
                Designator::GnuArrayRange(start, end) => {
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
    fn dump_parser_kind(kind: &NodeKind, symbol_table: Option<&SymbolTable>) {
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
            // Declaration and FunctionDef removed
            NodeKind::Function(function_data) => {
                // Get the function name from the symbol table
                let func_name = Self::get_function_name(function_data.symbol, symbol_table);
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
            NodeKind::InitializerList(list) => println!(
                "InitializerList([{}])",
                list.iter().map(Self::format_designated_initializer).join(", ")
            ),
            NodeKind::Dummy => println!("DUMMY"),
        }
    }
}
