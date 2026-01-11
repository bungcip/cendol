//! AST Dumper module
//!
//! This module handles AST dumping for debugging and visualization.

use hashbrown::HashSet;

use crate::ast::{Ast, DesignatedInitializer, Designator, NodeKind};
use crate::semantic::{ArraySizeType, BuiltinType, SymbolRef, SymbolTable, TypeKind, TypeRef, TypeRegistry};

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
            Self::dump_parser_kind(kind, ast, symbol_table);
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
            println!("TypeRef({}): {}", ty_ref.base(), formatted_type);
        }
    }

    /// Format TypeKind in a user-friendly way for TypeRegistry dump
    #[allow(clippy::only_used_in_recursion)]
    fn format_type_kind_user_friendly(kind: &TypeKind, registry: &TypeRegistry) -> String {
        match kind {
            // Basic types - use the existing dump format
            TypeKind::Builtin(b) => match b {
                BuiltinType::Void => "void".to_string(),
                BuiltinType::Bool => "_Bool".to_string(),
                BuiltinType::Char => "char".to_string(),
                BuiltinType::SChar => "signed char".to_string(),
                BuiltinType::UChar => "unsigned char".to_string(),
                BuiltinType::Short => "short".to_string(),
                BuiltinType::UShort => "unsigned short".to_string(),
                BuiltinType::Int => "int".to_string(),
                BuiltinType::UInt => "unsigned int".to_string(),
                BuiltinType::Long => "long".to_string(),
                BuiltinType::ULong => "unsigned long".to_string(),
                BuiltinType::LongLong => "long long".to_string(),
                BuiltinType::ULongLong => "unsigned long long".to_string(),
                BuiltinType::Float => "float".to_string(),
                BuiltinType::Double => "double".to_string(),
                BuiltinType::LongDouble => "long double".to_string(),
            },
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
            NodeKind::Designator(_) => {}
            NodeKind::Function(data) => {
                type_refs.insert(data.ty);
            }
            NodeKind::Param(data) => {
                type_refs.insert(data.ty.ty());
            }
            NodeKind::FunctionDecl(func_decl) => {
                type_refs.insert(func_decl.ty);
            }
            NodeKind::RecordDecl(record_decl) => {
                type_refs.insert(record_decl.ty);
            }
            NodeKind::FieldDecl(field_decl) => {
                type_refs.insert(field_decl.ty.ty());
            }
            NodeKind::EnumDecl(enum_decl) => {
                type_refs.insert(enum_decl.ty);
            }
            NodeKind::EnumMember(_) => {}

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
            NodeKind::GenericSelection(_) => {
                // GenericSelectionData doesn't contain TypeRefs directly.
            }
            NodeKind::GenericAssociation(ga) => {
                if let Some(qual_type) = ga.ty {
                    type_refs.insert(qual_type.ty());
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
            | NodeKind::InitializerList(_)
            | NodeKind::InitializerItem(_)
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
            NodeKind::FunctionCall(_)
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
    fn format_designated_initializer(init: &DesignatedInitializer, ast: &Ast) -> String {
        let mut result = String::new();
        for designator_ref in init.designator_start.range(init.designator_len) {
            match ast.get_kind(designator_ref) {
                NodeKind::Designator(d) => match d {
                    Designator::FieldName(name) => {
                        result.push_str(&format!(".{}", name));
                    }
                    Designator::ArrayIndex(index) => {
                        result.push_str(&format!("[{}]", index.get()));
                    }
                    Designator::GnuArrayRange(start, end) => {
                        result.push_str(&format!("[{} ... {}]", start.get(), end.get()));
                    }
                },
                _ => result.push_str("<invalid designator>"),
            }
        }

        if init.designator_len > 0 {
            result.push_str(" = ");
        }

        result.push_str(&init.initializer.get().to_string());
        result
    }

    /// Dump a single AST node kind
    fn dump_parser_kind(kind: &NodeKind, ast: &Ast, symbol_table: Option<&SymbolTable>) {
        match kind {
            NodeKind::TranslationUnit(tu_data) => {
                let start = tu_data.decl_start.get();
                if tu_data.decl_len > 0 {
                    let last = start + tu_data.decl_len as u32 - 1;
                    println!("TranslationUnit(decls={}..{}) (parser kind)", start, last);
                } else {
                    println!("TranslationUnit(decls=[]) (parser kind)");
                }
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
            NodeKind::FunctionCall(call_expr) => {
                let start = call_expr.arg_start.get();
                if call_expr.arg_len > 0 {
                    let last = start + call_expr.arg_len as u32 - 1;
                    println!(
                        "FunctionCall(callee={}, args={}..{})",
                        call_expr.callee.get(),
                        start,
                        last
                    );
                } else {
                    println!("FunctionCall(callee={}, args=[])", call_expr.callee.get());
                }
            }

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

            NodeKind::GenericSelection(gs) => {
                let start = gs.assoc_start.get();
                if gs.assoc_len > 0 {
                    let last = start + gs.assoc_len as u32 - 1;
                    println!(
                        "GenericSelection(control={}, associations={}..{})",
                        gs.control.get(),
                        start,
                        last
                    );
                } else {
                    println!("GenericSelection(control={}, associations=[])", gs.control.get());
                }
            }
            NodeKind::GenericAssociation(ga) => {
                println!(
                    "GenericAssociation(ty={:?}, result_expr={})",
                    ga.ty,
                    ga.result_expr.get()
                )
            }
            NodeKind::GnuStatementExpression(compound_stmt, result_expr) => {
                println!("GnuStatementExpression({}, {})", compound_stmt.get(), result_expr.get())
            }
            NodeKind::CompoundStatement(cs) => {
                let start = cs.stmt_start.get();
                if cs.stmt_len > 0 {
                    let last = start + cs.stmt_len as u32 - 1;
                    println!("CompoundStatement(stmts={}..{})", start, last);
                } else {
                    println!("CompoundStatement(stmts=[])");
                }
            }
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

            // Declaration and FunctionDef removed
            NodeKind::Function(data) => {
                let func_name = Self::get_function_name(data.symbol, symbol_table);
                let start = data.param_start.get();
                if data.param_len > 0 {
                    let last = start + data.param_len as u32 - 1;
                    println!(
                        "Function(name={}, symbol={:?}, ty={}, params={}..{}, body={})",
                        func_name,
                        data.symbol,
                        data.ty,
                        start,
                        last,
                        data.body.get()
                    );
                } else {
                    println!(
                        "Function(name={}, symbol={:?}, ty={}, params=[], body={})",
                        func_name,
                        data.symbol,
                        data.ty,
                        data.body.get()
                    );
                }
            }
            NodeKind::Param(data) => {
                println!("Param(symbol={:?}, ty={:?})", data.symbol, data.ty)
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
                let start = record_decl.member_start.get();
                if record_decl.member_len > 0 {
                    let last = start + record_decl.member_len as u32 - 1;
                    println!(
                        "RecordDecl(name={:?}, ty={}, is_union={}, members={}..{})",
                        record_decl.name,
                        record_decl.ty.get(),
                        record_decl.is_union,
                        start,
                        last
                    );
                } else {
                    println!(
                        "RecordDecl(name={:?}, ty={}, is_union={}, members=[])",
                        record_decl.name,
                        record_decl.ty.get(),
                        record_decl.is_union
                    );
                }
            }
            NodeKind::FieldDecl(field_decl) => {
                println!("FieldDecl(name={:?}, ty={})", field_decl.name, field_decl.ty)
            }
            NodeKind::EnumDecl(enum_decl) => {
                let start = enum_decl.member_start.get();
                if enum_decl.member_len > 0 {
                    let last = start + enum_decl.member_len as u32 - 1;
                    println!(
                        "EnumDecl(name={:?}, ty={}, members={}..{})",
                        enum_decl.name,
                        enum_decl.ty.get(),
                        start,
                        last
                    );
                } else {
                    println!(
                        "EnumDecl(name={:?}, ty={}, members=[])",
                        enum_decl.name,
                        enum_decl.ty.get()
                    );
                }
            }
            NodeKind::EnumMember(enum_member) => {
                println!("EnumMember(name={}, value={})", enum_member.name, enum_member.value)
            }
            NodeKind::InitializerList(list) => {
                let start = list.init_start.get();
                if list.init_len > 0 {
                    let last = start + list.init_len as u32 - 1;
                    println!("InitializerList(inits={}..{})", start, last);
                } else {
                    println!("InitializerList(inits=[])");
                }
            }
            NodeKind::InitializerItem(init) => {
                println!("InitializerItem({})", Self::format_designated_initializer(init, ast))
            }
            NodeKind::Designator(d) => match d {
                Designator::FieldName(name) => println!("Designator(.{})", name),
                Designator::ArrayIndex(idx) => println!("Designator([{}])", idx.get()),
                Designator::GnuArrayRange(start, end) => println!("Designator([{} ... {}])", start.get(), end.get()),
            },
            NodeKind::Dummy => println!("DUMMY"),
        }
    }
}
