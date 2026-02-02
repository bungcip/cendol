//! AST Dumper module
//!
//! This module handles AST dumping for debugging and visualization.

use hashbrown::HashSet;
use std::fmt;

use crate::ast::literal;
use crate::ast::parsed::{ParsedAst, ParsedNodeKind};
use crate::ast::{Ast, DesignatedInitializer, Designator, NodeKind};
use crate::semantic::{ArraySizeType, BuiltinType, SymbolRef, SymbolTable, TypeKind, TypeRef, TypeRegistry};

pub struct ParsedAstDisplay<'a>(pub &'a ParsedAst);

impl<'a> fmt::Display for ParsedAstDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ast = self.0;
        for (i, node) in ast.nodes.iter().enumerate() {
            if matches!(node.kind, ParsedNodeKind::Dummy) {
                continue;
            }
            write!(f, "{}: ", i + 1)?;
            AstDumper::dump_parsed_node_kind(f, &node.kind, ast)?;
        }
        Ok(())
    }
}

pub struct ParserAstDisplay<'a> {
    pub ast: &'a Ast,
    pub symbol_table: Option<&'a SymbolTable>,
}

impl<'a> fmt::Display for ParserAstDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ast = self.ast;
        for (i, kind) in ast.kinds.iter().enumerate() {
            if matches!(kind, NodeKind::Dummy) {
                continue;
            }
            write!(f, "{}: ", i + 1)?;
            AstDumper::dump_parser_kind(f, kind, ast, self.symbol_table)?;
        }
        Ok(())
    }
}

pub struct TypeRegistryDisplay<'a> {
    pub ast: &'a Ast,
    pub registry: &'a TypeRegistry,
}

impl<'a> fmt::Display for TypeRegistryDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Collect all TypeRefs used in the AST
        let mut used_type_refs = HashSet::new();

        for kind in &self.ast.kinds {
            AstDumper::collect_type_refs_from_node(kind, &mut used_type_refs);
        }

        if used_type_refs.is_empty() {
            return Ok(());
        }

        // Print header
        writeln!(f, "\n=== TypeRegistry (Used TypeRefs) ===")?;

        // Sort TypeRefs for consistent output
        let mut sorted_type_refs: Vec<_> = used_type_refs.into_iter().collect();
        sorted_type_refs.sort_by_key(|ty_ref| ty_ref.get());

        // Dump each used TypeRef with user-friendly formatting
        for ty_ref in sorted_type_refs {
            let ty = self.registry.get(ty_ref);
            let formatted_type = AstDumper::format_type_kind_user_friendly(&ty.kind, self.registry);
            writeln!(f, "TypeRef({}): {}", ty_ref.base(), formatted_type)?;
        }
        Ok(())
    }
}

/// Dumper for AST
pub(crate) struct AstDumper;

impl AstDumper {
    /// Dump parsed AST to stdout
    pub(crate) fn dump_parsed_ast(ast: &ParsedAst) -> ParsedAstDisplay<'_> {
        ParsedAstDisplay(ast)
    }

    /// Dump parser AST to stdout
    pub(crate) fn dump_parser<'a>(ast: &'a Ast, symbol_table: Option<&'a SymbolTable>) -> ParserAstDisplay<'a> {
        ParserAstDisplay { ast, symbol_table }
    }

    /// Dump TypeRegistry information for used TypeRefs in the AST
    pub(crate) fn dump_type_registry<'a>(ast: &'a Ast, registry: &'a TypeRegistry) -> TypeRegistryDisplay<'a> {
        TypeRegistryDisplay { ast, registry }
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
                BuiltinType::Signed => "signed".to_string(),
                BuiltinType::VaList => "__builtin_va_list".to_string(),
                BuiltinType::Complex => "_Complex (marker)".to_string(),
            },
            TypeKind::Complex { .. } => "_Complex".to_string(),
            TypeKind::Error => "<error>".to_string(),

            // Complex types - provide more detailed information
            TypeKind::Pointer { pointee } => {
                let current_type = registry.get(pointee.ty());
                format!(
                    "{}*",
                    Self::format_type_kind_user_friendly(&current_type.kind, registry)
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
                ..
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
            NodeKind::BuiltinVaArg(qual_type, _) => {
                type_refs.insert(qual_type.ty());
            }
            NodeKind::BuiltinVaStart(_, _)
            | NodeKind::BuiltinVaEnd(_)
            | NodeKind::BuiltinVaCopy(_, _)
            | NodeKind::BuiltinExpect(_, _)
            | NodeKind::AtomicOp(..) => {}
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
            NodeKind::Literal(_) | NodeKind::Ident(_, _) => {
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

    /// Dump a single parsed parsed node kind
    fn dump_parsed_node_kind(f: &mut fmt::Formatter<'_>, kind: &ParsedNodeKind, ast: &ParsedAst) -> fmt::Result {
        match kind {
            ParsedNodeKind::Literal(literal) => match literal {
                crate::ast::literal::Literal::Int { val, suffix } => {
                    writeln!(f, "LiteralInt({:?}, {:?})", val, suffix)
                }
                crate::ast::literal::Literal::Float { val, suffix } => {
                    writeln!(f, "LiteralFloat({}, {:?})", val, suffix)
                }
                crate::ast::literal::Literal::String(s) => writeln!(f, "LiteralString(\"{}\")", s),
                crate::ast::literal::Literal::Char(c) => writeln!(f, "LiteralChar('{}')", *c as char),
            },
            ParsedNodeKind::Ident(name) => writeln!(f, "Ident({})", name),

            // Expressions
            ParsedNodeKind::UnaryOp(op, node) => writeln!(f, "UnaryOp({:?}, {})", op, node.get()),
            ParsedNodeKind::BinaryOp(op, l, r) => {
                writeln!(f, "BinaryOp({:?}, {}, {})", op, l.get(), r.get())
            }
            ParsedNodeKind::TernaryOp(c, t, e) => {
                writeln!(f, "TernaryOp({}, {}, {})", c.get(), t.get(), e.get())
            }
            ParsedNodeKind::GnuStatementExpression(stmt, expr) => {
                writeln!(f, "GnuStatementExpression({}, {})", stmt.get(), expr.get())
            }
            ParsedNodeKind::PostIncrement(node) => writeln!(f, "PostIncrement({})", node.get()),
            ParsedNodeKind::PostDecrement(node) => writeln!(f, "PostDecrement({})", node.get()),
            ParsedNodeKind::Assignment(op, l, r) => {
                writeln!(f, "Assignment({:?}, {}, {})", op, l.get(), r.get())
            }
            ParsedNodeKind::FunctionCall(callee, args) => {
                let args_str = args.iter().map(|a| a.get().to_string()).collect::<Vec<_>>().join(", ");
                writeln!(f, "FunctionCall(callee={}, args=[{}])", callee.get(), args_str)
            }
            ParsedNodeKind::MemberAccess(obj, field, arrow) => writeln!(
                f,
                "MemberAccess({}, {}, {})",
                obj.get(),
                field,
                if *arrow { "->" } else { "." }
            ),
            ParsedNodeKind::IndexAccess(arr, idx) => {
                writeln!(f, "IndexAccess({}, {})", arr.get(), idx.get())
            }
            ParsedNodeKind::Cast(ty, expr) => writeln!(f, "Cast({:?}, {})", ty, expr.get()),
            ParsedNodeKind::SizeOfExpr(expr) => writeln!(f, "SizeOfExpr({})", expr.get()),
            ParsedNodeKind::SizeOfType(ty) => writeln!(f, "SizeOfType({:?})", ty),
            ParsedNodeKind::AlignOf(ty) => writeln!(f, "AlignOf({:?})", ty),
            ParsedNodeKind::CompoundLiteral(ty, init) => {
                writeln!(f, "CompoundLiteral({:?}, {})", ty, init.get())
            }
            ParsedNodeKind::BuiltinVaArg(ty, expr) => {
                writeln!(f, "BuiltinVaArg({:?}, {})", ty, expr.get())
            }
            ParsedNodeKind::BuiltinVaStart(ap, last) => {
                writeln!(f, "BuiltinVaStart({}, {})", ap.get(), last.get())
            }
            ParsedNodeKind::BuiltinVaEnd(ap) => {
                writeln!(f, "BuiltinVaEnd({})", ap.get())
            }
            ParsedNodeKind::BuiltinVaCopy(dst, src) => {
                writeln!(f, "BuiltinVaCopy({}, {})", dst.get(), src.get())
            }
            ParsedNodeKind::BuiltinExpect(exp, c) => {
                writeln!(f, "BuiltinExpect({}, {})", exp.get(), c.get())
            }
            ParsedNodeKind::AtomicOp(op, args) => {
                let args_str = args.iter().map(|a| a.get().to_string()).collect::<Vec<_>>().join(", ");
                writeln!(f, "AtomicOp({:?}, args=[{}])", op, args_str)
            }
            ParsedNodeKind::GenericSelection(ctrl, assocs) => {
                writeln!(f, "GenericSelection({}, {:?})", ctrl.get(), assocs)
            }

            // Statements
            ParsedNodeKind::CompoundStatement(stmts) => {
                let stmts_str = stmts.iter().map(|s| s.get().to_string()).collect::<Vec<_>>().join(", ");
                writeln!(f, "CompoundStatement(stmts=[{}])", stmts_str)
            }
            ParsedNodeKind::If(data) => writeln!(f, "If({:?})", data),
            ParsedNodeKind::While(data) => writeln!(f, "While({:?})", data),
            ParsedNodeKind::DoWhile(body, cond) => {
                writeln!(f, "DoWhile(body={}, cond={})", body.get(), cond.get())
            }
            ParsedNodeKind::For(data) => writeln!(f, "For({:?})", data),
            ParsedNodeKind::Return(expr) => writeln!(
                f,
                "Return({})",
                expr.map(|e| e.get().to_string()).unwrap_or("void".to_string())
            ),
            ParsedNodeKind::Break => writeln!(f, "Break"),
            ParsedNodeKind::Continue => writeln!(f, "Continue"),
            ParsedNodeKind::Goto(label) => writeln!(f, "Goto({})", label),
            ParsedNodeKind::Label(label, stmt) => writeln!(f, "Label({}, {})", label, stmt.get()),
            ParsedNodeKind::Switch(cond, body) => {
                writeln!(f, "Switch({}, {})", cond.get(), body.get())
            }
            ParsedNodeKind::Case(val, stmt) => writeln!(f, "Case({}, {})", val.get(), stmt.get()),
            ParsedNodeKind::CaseRange(start, end, stmt) => {
                writeln!(f, "CaseRange({}, {}, {})", start.get(), end.get(), stmt.get())
            }
            ParsedNodeKind::Default(stmt) => writeln!(f, "Default({})", stmt.get()),
            ParsedNodeKind::ExpressionStatement(expr) => writeln!(
                f,
                "ExpressionStatement({})",
                expr.map(|e| e.get().to_string()).unwrap_or("empty".to_string())
            ),
            ParsedNodeKind::EmptyStatement => writeln!(f, "EmptyStatement"),

            // Declarations & Definitions
            ParsedNodeKind::Declaration(data) => writeln!(f, "Declaration({:?})", data),
            ParsedNodeKind::FunctionDef(data) => writeln!(f, "FunctionDef({:?})", data),
            ParsedNodeKind::EnumConstant(name, val) => writeln!(
                f,
                "EnumConstant({}, {})",
                name,
                val.map(|v| v.get().to_string()).unwrap_or("auto".to_string())
            ),
            ParsedNodeKind::StaticAssert(cond, msg) => {
                let message_str = if let ParsedNodeKind::Literal(literal::Literal::String(s)) = &ast.get_node(*msg).kind
                {
                    s.to_string()
                } else {
                    "<invalid>".to_string()
                };
                writeln!(f, "StaticAssert({}, \"{}\")", cond.get(), message_str)
            }

            // Top Level
            ParsedNodeKind::TranslationUnit(decls) => {
                let decls_str = decls.iter().map(|d| d.get().to_string()).collect::<Vec<_>>().join(", ");
                writeln!(f, "TranslationUnit(decls=[{}])", decls_str)
            }

            // InitializerList
            ParsedNodeKind::InitializerList(inits) => writeln!(f, "InitializerList({:?})", inits),

            ParsedNodeKind::Dummy => writeln!(f, "Dummy"),
        }
    }

    /// Dump a single AST node kind
    fn dump_parser_kind(
        f: &mut fmt::Formatter<'_>,
        kind: &NodeKind,
        ast: &Ast,
        symbol_table: Option<&SymbolTable>,
    ) -> fmt::Result {
        match kind {
            NodeKind::TranslationUnit(tu_data) => {
                let start = tu_data.decl_start.get();
                if tu_data.decl_len > 0 {
                    let last = start + tu_data.decl_len as u32 - 1;
                    writeln!(f, "TranslationUnit(decls={}..{}) (parser kind)", start, last)
                } else {
                    writeln!(f, "TranslationUnit(decls=[]) (parser kind)")
                }
            }
            NodeKind::Literal(literal) => match literal {
                crate::ast::literal::Literal::Int { val, suffix } => {
                    writeln!(f, "LiteralInt({:?}, {:?})", val, suffix)
                }
                crate::ast::literal::Literal::Float { val, suffix } => {
                    writeln!(f, "LiteralFloat({}, {:?})", val, suffix)
                }
                crate::ast::literal::Literal::String(s) => writeln!(f, "LiteralString({})", s),
                crate::ast::literal::Literal::Char(c) => writeln!(f, "LiteralChar('{}')", *c as char),
            },
            NodeKind::Ident(sym, _) => writeln!(f, "Ident({})", sym),
            NodeKind::UnaryOp(op, operand) => writeln!(f, "UnaryOp({:?}, {})", op, operand.get()),
            NodeKind::BinaryOp(op, left, right) => {
                writeln!(f, "BinaryOp({:?}, {}, {})", op, left.get(), right.get())
            }
            NodeKind::TernaryOp(cond, then, else_) => {
                writeln!(f, "TernaryOp({}, {}, {})", cond.get(), then.get(), else_.get())
            }
            NodeKind::PostIncrement(expr) => writeln!(f, "PostIncrement({})", expr.get()),
            NodeKind::PostDecrement(expr) => writeln!(f, "PostDecrement({})", expr.get()),
            NodeKind::Assignment(op, lhs, rhs) => {
                writeln!(f, "Assignment({:?}, {}, {})", op, lhs.get(), rhs.get())
            }
            NodeKind::FunctionCall(call_expr) => {
                let start = call_expr.arg_start.get();
                if call_expr.arg_len > 0 {
                    let last = start + call_expr.arg_len as u32 - 1;
                    writeln!(
                        f,
                        "FunctionCall(callee={}, args={}..{})",
                        call_expr.callee.get(),
                        start,
                        last
                    )
                } else {
                    writeln!(f, "FunctionCall(callee={}, args=[])", call_expr.callee.get())
                }
            }

            NodeKind::MemberAccess(obj, field, is_arrow) => writeln!(
                f,
                "MemberAccess({}, {}, {})",
                obj.get(),
                field,
                if *is_arrow { "->" } else { "." }
            ),
            NodeKind::IndexAccess(array, index) => {
                writeln!(f, "IndexAccess({}, {})", array.get(), index.get())
            }
            NodeKind::Cast(ty, expr) => writeln!(f, "Cast({}, {})", ty, expr.get()),
            NodeKind::SizeOfExpr(expr) => writeln!(f, "SizeOfExpr({})", expr.get()),
            NodeKind::SizeOfType(ty) => writeln!(f, "SizeOfType({})", ty),
            NodeKind::AlignOf(ty) => writeln!(f, "AlignOf({})", ty),
            NodeKind::CompoundLiteral(ty, init) => {
                writeln!(f, "CompoundLiteral({}, {})", ty, init.get())
            }
            NodeKind::BuiltinVaArg(ty, expr) => {
                writeln!(f, "BuiltinVaArg({}, {})", ty, expr.get())
            }
            NodeKind::BuiltinVaStart(ap, last) => {
                writeln!(f, "BuiltinVaStart({}, {})", ap.get(), last.get())
            }
            NodeKind::BuiltinVaEnd(ap) => {
                writeln!(f, "BuiltinVaEnd({})", ap.get())
            }
            NodeKind::BuiltinVaCopy(dst, src) => {
                writeln!(f, "BuiltinVaCopy({}, {})", dst.get(), src.get())
            }
            NodeKind::BuiltinExpect(exp, c) => {
                writeln!(f, "BuiltinExpect({}, {})", exp.get(), c.get())
            }
            NodeKind::AtomicOp(op, args_start, args_len) => {
                let start = args_start.get();
                if *args_len > 0 {
                    let last = start + *args_len as u32 - 1;
                    writeln!(f, "AtomicOp({:?}, args={}..{})", op, start, last)
                } else {
                    writeln!(f, "AtomicOp({:?}, args=[])", op)
                }
            }

            NodeKind::GenericSelection(gs) => {
                let start = gs.assoc_start.get();
                if gs.assoc_len > 0 {
                    let last = start + gs.assoc_len as u32 - 1;
                    writeln!(
                        f,
                        "GenericSelection(control={}, associations={}..{})",
                        gs.control.get(),
                        start,
                        last
                    )
                } else {
                    writeln!(f, "GenericSelection(control={}, associations=[])", gs.control.get())
                }
            }
            NodeKind::GenericAssociation(ga) => {
                writeln!(
                    f,
                    "GenericAssociation(ty={:?}, result_expr={})",
                    ga.ty,
                    ga.result_expr.get()
                )
            }
            NodeKind::GnuStatementExpression(compound_stmt, result_expr) => {
                writeln!(
                    f,
                    "GnuStatementExpression({}, {})",
                    compound_stmt.get(),
                    result_expr.get()
                )
            }
            NodeKind::CompoundStatement(cs) => {
                let start = cs.stmt_start.get();
                if cs.stmt_len > 0 {
                    let last = start + cs.stmt_len as u32 - 1;
                    writeln!(f, "CompoundStatement(stmts={}..{})", start, last)
                } else {
                    writeln!(f, "CompoundStatement(stmts=[])")
                }
            }
            NodeKind::If(if_stmt) => writeln!(
                f,
                "If(condition={}, then={}, else={})",
                if_stmt.condition.get(),
                if_stmt.then_branch.get(),
                if_stmt
                    .else_branch
                    .map(|r| r.get().to_string())
                    .unwrap_or("none".to_string())
            ),
            NodeKind::While(while_stmt) => writeln!(
                f,
                "While(condition={}, body={})",
                while_stmt.condition.get(),
                while_stmt.body.get()
            ),
            NodeKind::DoWhile(body, cond) => {
                writeln!(f, "DoWhile(body={}, condition={})", body.get(), cond.get())
            }
            NodeKind::For(for_stmt) => writeln!(
                f,
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
            NodeKind::Return(expr) => writeln!(
                f,
                "Return({})",
                expr.map(|r| r.get().to_string()).unwrap_or("void".to_string())
            ),
            NodeKind::Break => writeln!(f, "Break"),
            NodeKind::Continue => writeln!(f, "Continue"),
            NodeKind::Goto(label, _) => writeln!(f, "Goto({})", label),
            NodeKind::Label(label, stmt, _) => writeln!(f, "Label({}, {})", label, stmt.get()),
            NodeKind::Switch(cond, body) => {
                writeln!(f, "Switch(condition={}, body={})", cond.get(), body.get())
            }
            NodeKind::Case(expr, stmt) => writeln!(f, "Case({}, {})", expr.get(), stmt.get()),
            NodeKind::CaseRange(start, end, stmt) => {
                writeln!(f, "CaseRange({}, {}, {})", start.get(), end.get(), stmt.get())
            }
            NodeKind::Default(stmt) => writeln!(f, "Default({})", stmt.get()),
            NodeKind::ExpressionStatement(expr) => writeln!(
                f,
                "ExpressionStatement({})",
                expr.map(|r| r.get().to_string()).unwrap_or("none".to_string())
            ),

            // Declaration and FunctionDef removed
            NodeKind::Function(data) => {
                let func_name = Self::get_function_name(data.symbol, symbol_table);
                let start = data.param_start.get();
                if data.param_len > 0 {
                    let last = start + data.param_len as u32 - 1;
                    writeln!(
                        f,
                        "Function(name={}, symbol={:?}, ty={}, params={}..{}, body={})",
                        func_name,
                        data.symbol,
                        data.ty,
                        start,
                        last,
                        data.body.get()
                    )
                } else {
                    writeln!(
                        f,
                        "Function(name={}, symbol={:?}, ty={}, params=[], body={})",
                        func_name,
                        data.symbol,
                        data.ty,
                        data.body.get()
                    )
                }
            }
            NodeKind::Param(data) => {
                writeln!(f, "Param(symbol={:?}, ty={:?})", data.symbol, data.ty)
            }
            NodeKind::EnumConstant(name, value) => writeln!(
                f,
                "EnumConstant({}, {})",
                name,
                value.map(|r| r.get().to_string()).unwrap_or("auto".to_string())
            ),
            NodeKind::StaticAssert(cond, msg) => {
                let message_str = if let NodeKind::Literal(literal::Literal::String(s)) = ast.get_kind(*msg) {
                    s.to_string()
                } else {
                    "<invalid>".to_string()
                };
                writeln!(f, "StaticAssert(condition={}, message=\"{}\")", cond.get(), message_str)
            }
            NodeKind::VarDecl(var_decl) => {
                writeln!(
                    f,
                    "VarDecl(name={}, ty={}, storage={:?})",
                    var_decl.name, var_decl.ty, var_decl.storage
                )
            }
            NodeKind::FunctionDecl(func_decl) => {
                writeln!(
                    f,
                    "FunctionDecl(name={}, ty={}, storage={:?})",
                    func_decl.name,
                    func_decl.ty.get(),
                    func_decl.storage
                )
            }
            NodeKind::TypedefDecl(typedef_decl) => {
                writeln!(f, "TypedefDecl(name={}, ty={})", typedef_decl.name, typedef_decl.ty)
            }
            NodeKind::RecordDecl(record_decl) => {
                let start = record_decl.member_start.get();
                if record_decl.member_len > 0 {
                    let last = start + record_decl.member_len as u32 - 1;
                    writeln!(
                        f,
                        "RecordDecl(name={:?}, ty={}, is_union={}, members={}..{})",
                        record_decl.name,
                        record_decl.ty.get(),
                        record_decl.is_union,
                        start,
                        last
                    )
                } else {
                    writeln!(
                        f,
                        "RecordDecl(name={:?}, ty={}, is_union={}, members=[])",
                        record_decl.name,
                        record_decl.ty.get(),
                        record_decl.is_union
                    )
                }
            }
            NodeKind::FieldDecl(field_decl) => {
                writeln!(f, "FieldDecl(name={:?}, ty={})", field_decl.name, field_decl.ty)
            }
            NodeKind::EnumDecl(enum_decl) => {
                let start = enum_decl.member_start.get();
                if enum_decl.member_len > 0 {
                    let last = start + enum_decl.member_len as u32 - 1;
                    writeln!(
                        f,
                        "EnumDecl(name={:?}, ty={}, members={}..{})",
                        enum_decl.name,
                        enum_decl.ty.get(),
                        start,
                        last
                    )
                } else {
                    writeln!(
                        f,
                        "EnumDecl(name={:?}, ty={}, members=[])",
                        enum_decl.name,
                        enum_decl.ty.get()
                    )
                }
            }
            NodeKind::EnumMember(enum_member) => {
                writeln!(f, "EnumMember(name={}, value={})", enum_member.name, enum_member.value)
            }
            NodeKind::InitializerList(list) => {
                let start = list.init_start.get();
                if list.init_len > 0 {
                    let last = start + list.init_len as u32 - 1;
                    writeln!(f, "InitializerList(inits={}..{})", start, last)
                } else {
                    writeln!(f, "InitializerList(inits=[])")
                }
            }
            NodeKind::InitializerItem(init) => {
                writeln!(f, "InitializerItem({})", Self::format_designated_initializer(init, ast))
            }
            NodeKind::Designator(d) => match d {
                Designator::FieldName(name) => writeln!(f, "Designator(.{})", name),
                Designator::ArrayIndex(idx) => writeln!(f, "Designator([{}])", idx.get()),
                Designator::GnuArrayRange(start, end) => writeln!(f, "Designator([{} ... {}])", start.get(), end.get()),
            },
            NodeKind::Dummy => writeln!(f, "DUMMY"),
        }
    }
}
