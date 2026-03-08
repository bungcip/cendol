//! AST Dumper module
//!
//! This module handles AST dumping for debugging and visualization.

use hashbrown::HashSet;
use std::fmt;

use crate::ast::literal::Literal;
use crate::ast::parsed::{ParsedAst, ParsedNodeKind, ParsedNodeRef};
use crate::ast::{Ast, DesignatedInitializer, Designator, NodeKind, NodeRef};
use crate::semantic::{SymbolRef, SymbolTable, TypeRef, TypeRegistry};

pub(crate) struct ParsedAstDisplay<'a>(pub(crate) &'a ParsedAst);

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

pub(crate) struct ParserAstDisplay<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: Option<&'a SymbolTable>,
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

pub(crate) struct TypeRegistryDisplay<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) registry: &'a TypeRegistry,
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
            let formatted_type = self.registry.display_type(ty_ref);
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
            NodeKind::BuiltinTypesCompatibleP(t1, t2) => {
                type_refs.insert(t1.ty());
                type_refs.insert(t2.ty());
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
            NodeKind::BuiltinVaArg(qual_type, _) | NodeKind::BuiltinOffsetof(qual_type, _) => {
                type_refs.insert(qual_type.ty());
            }
            NodeKind::BuiltinVaStart(_, _)
            | NodeKind::BuiltinVaEnd(_)
            | NodeKind::BuiltinVaCopy(_, _)
            | NodeKind::BuiltinPopcount(_)
            | NodeKind::BuiltinClz(_)
            | NodeKind::BuiltinCtz(_)
            | NodeKind::BuiltinFfs(_)
            | NodeKind::BuiltinBswap16(_)
            | NodeKind::BuiltinBswap32(_)
            | NodeKind::BuiltinBswap64(_)
            | NodeKind::BuiltinExpect(_, _)
            | NodeKind::AtomicOp(..) => {}
            NodeKind::VarDecl(var_decl) => {
                type_refs.insert(var_decl.ty.ty());
            }
            NodeKind::TypedefDecl(typedef_decl) => {
                type_refs.insert(typedef_decl.ty.ty());
            }
            NodeKind::GenericSelection(_) => {
                // GenericSelection doesn't contain TypeRefs directly.
            }
            NodeKind::GenericAssociation(ga) => {
                if let Some(qual_type) = ga.ty {
                    type_refs.insert(qual_type.ty());
                }
            }
            NodeKind::BuiltinChooseExpr(_, _, _) => {}
            NodeKind::BuiltinConstantP(_) => {}
            NodeKind::BuiltinUnreachable | NodeKind::BuiltinTrap => {}

            // Literal nodes - don't contain TypeRefs
            NodeKind::Literal(_) | NodeKind::Ident(_, _) => {
                // These don't contain TypeRefs
            }

            // Statement types that don't directly contain TypeRefs
            NodeKind::TranslationUnit(_)
            | NodeKind::CompoundStmt(_)
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
            | NodeKind::ExpressionStmt(_)
            | NodeKind::InitializerList(_)
            | NodeKind::InitializerItem(_)
            | NodeKind::StaticAssert(_, _)
            | NodeKind::EnumConstant(_, _)
            | NodeKind::Dummy => {
                // These don't directly contain TypeRefs
            }

            // GNU extensions
            NodeKind::GnuStatementExpr(_, _) => {
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

    fn format_range(label: &str, start: NodeRef, len: u16) -> String {
        if len > 0 {
            let s = start.get();
            format!("{}={}..{}", label, s, s + len as u32 - 1)
        } else {
            format!("{}=[]", label)
        }
    }

    fn format_literal(literal: &Literal) -> String {
        match literal {
            Literal::Int { val, suffix, base } => {
                format!("LiteralInt({:?}, {:?}, base={})", val, suffix, base)
            }
            Literal::Float { val, suffix } => {
                format!("LiteralFloat({}, {:?})", val, suffix)
            }
            Literal::String(s) => format!("LiteralString(\"{}\")", s),
            Literal::Char(c) => format!(
                "LiteralChar('{}')",
                char::from_u32(*c as u32).unwrap_or(char::REPLACEMENT_CHARACTER)
            ),
        }
    }

    fn format_parsed_list(nodes: &[ParsedNodeRef]) -> String {
        nodes.iter().map(|n| n.get().to_string()).collect::<Vec<_>>().join(", ")
    }

    /// Dump a single parsed parsed node kind
    fn dump_parsed_node_kind(f: &mut fmt::Formatter<'_>, kind: &ParsedNodeKind, ast: &ParsedAst) -> fmt::Result {
        use crate::ast::ParsedNodeKind as PNK;
        match kind {
            PNK::Literal(literal) => writeln!(f, "{}", Self::format_literal(literal)),
            PNK::Ident(name) => writeln!(f, "Ident({})", name),

            // Expressions
            PNK::UnaryOp(op, node) => writeln!(f, "UnaryOp({:?}, {})", op, node.get()),
            PNK::BinaryOp(op, l, r) => {
                writeln!(f, "BinaryOp({:?}, {}, {})", op, l.get(), r.get())
            }
            PNK::TernaryOp(c, t, e) => {
                writeln!(f, "TernaryOp({}, {}, {})", c.get(), t.get(), e.get())
            }
            PNK::GnuStatementExpr(stmt, expr) => {
                writeln!(f, "GnuStatementExpr({}, {})", stmt.get(), expr.get())
            }
            PNK::Assignment(op, l, r) => {
                writeln!(f, "Assignment({:?}, {}, {})", op, l.get(), r.get())
            }
            PNK::FunctionCall(callee, args) => {
                writeln!(
                    f,
                    "FunctionCall(callee={}, args=[{}])",
                    callee.get(),
                    Self::format_parsed_list(args)
                )
            }
            PNK::MemberAccess(obj, field, arrow) => writeln!(
                f,
                "MemberAccess({}, {}, {})",
                obj.get(),
                field,
                if *arrow { "->" } else { "." }
            ),
            PNK::IndexAccess(arr, idx) => {
                writeln!(f, "IndexAccess({}, {})", arr.get(), idx.get())
            }
            PNK::Cast(ty, expr)
            | PNK::CompoundLiteral(ty, expr)
            | PNK::BuiltinVaArg(ty, expr)
            | PNK::BuiltinOffsetof(ty, expr) => {
                let name = match kind {
                    PNK::Cast(_, _) => "Cast",
                    PNK::CompoundLiteral(_, _) => "CompoundLiteral",
                    PNK::BuiltinVaArg(_, _) => "BuiltinVaArg",
                    PNK::BuiltinOffsetof(_, _) => "BuiltinOffsetof",
                    _ => unreachable!(),
                };
                writeln!(f, "{}({:?}, {})", name, ty, expr.get())
            }
            PNK::SizeOfType(ty) | PNK::AlignOf(ty) => {
                let name = match kind {
                    PNK::SizeOfType(_) => "SizeOfType",
                    PNK::AlignOf(_) => "AlignOf",
                    _ => unreachable!(),
                };
                writeln!(f, "{}({:?})", name, ty)
            }
            PNK::BuiltinTypesCompatibleP(t1, t2) => {
                writeln!(f, "BuiltinTypesCompatibleP({:?}, {:?})", t1, t2)
            }
            PNK::BuiltinVaStart(ap, last) => {
                writeln!(f, "BuiltinVaStart({}, {})", ap.get(), last.get())
            }
            PNK::BuiltinVaCopy(dst, src) => {
                writeln!(f, "BuiltinVaCopy({}, {})", dst.get(), src.get())
            }
            PNK::BuiltinExpect(exp, c) => {
                writeln!(f, "BuiltinExpect({}, {})", exp.get(), c.get())
            }
            PNK::BuiltinVaEnd(exp)
            | PNK::BuiltinPopcount(exp)
            | PNK::BuiltinClz(exp)
            | PNK::BuiltinCtz(exp)
            | PNK::BuiltinFfs(exp)
            | PNK::BuiltinBswap16(exp)
            | PNK::BuiltinBswap32(exp)
            | PNK::BuiltinBswap64(exp)
            | PNK::BuiltinConstantP(exp)
            | PNK::SizeOfExpr(exp)
            | PNK::PostIncrement(exp)
            | PNK::PostDecrement(exp)
            | PNK::Default(exp) => {
                let name = match kind {
                    PNK::BuiltinVaEnd(_) => "BuiltinVaEnd",
                    PNK::BuiltinPopcount(_) => "BuiltinPopcount",
                    PNK::BuiltinClz(_) => "BuiltinClz",
                    PNK::BuiltinCtz(_) => "BuiltinCtz",
                    PNK::BuiltinFfs(_) => "BuiltinFfs",
                    PNK::BuiltinBswap16(_) => "BuiltinBswap16",
                    PNK::BuiltinBswap32(_) => "BuiltinBswap32",
                    PNK::BuiltinBswap64(_) => "BuiltinBswap64",
                    PNK::BuiltinConstantP(_) => "BuiltinConstantP",
                    PNK::SizeOfExpr(_) => "SizeOfExpr",
                    PNK::PostIncrement(_) => "PostIncrement",
                    PNK::PostDecrement(_) => "PostDecrement",
                    PNK::Default(_) => "Default",
                    _ => unreachable!(),
                };
                writeln!(f, "{}({})", name, exp.get())
            }
            PNK::AtomicOp(op, args) => {
                writeln!(f, "AtomicOp({:?}, args=[{}])", op, Self::format_parsed_list(args))
            }
            PNK::GenericSelection(ctrl, assocs) => {
                writeln!(f, "GenericSelection({}, {:?})", ctrl.get(), assocs)
            }
            PNK::BuiltinChooseExpr(c, t, e) => {
                writeln!(f, "BuiltinChooseExpr({}, {}, {})", c.get(), t.get(), e.get())
            }
            PNK::BuiltinUnreachable => writeln!(f, "BuiltinUnreachable"),
            PNK::BuiltinTrap => writeln!(f, "BuiltinTrap"),

            // Statements
            PNK::CompoundStmt(stmts) => {
                writeln!(f, "CompoundStmt(stmts=[{}])", Self::format_parsed_list(stmts))
            }
            PNK::If(data) => writeln!(f, "If({:?})", data),
            PNK::While(data) => writeln!(f, "While({:?})", data),
            PNK::DoWhile(body, cond) => {
                writeln!(f, "DoWhile(body={}, cond={})", body.get(), cond.get())
            }
            PNK::For(data) => writeln!(f, "For({:?})", data),
            PNK::Return(expr) => writeln!(
                f,
                "Return({})",
                expr.map(|e| e.get().to_string()).unwrap_or("void".to_string())
            ),
            PNK::Break => writeln!(f, "Break"),
            PNK::Continue => writeln!(f, "Continue"),
            PNK::Goto(label) => writeln!(f, "Goto({})", label),
            PNK::Label(label, stmt) => writeln!(f, "Label({}, {})", label, stmt.get()),
            PNK::Switch(cond, body) => {
                writeln!(f, "Switch({}, {})", cond.get(), body.get())
            }
            PNK::Case(val, stmt) => writeln!(f, "Case({}, {})", val.get(), stmt.get()),
            PNK::CaseRange(start, end, stmt) => {
                writeln!(f, "CaseRange({}, {}, {})", start.get(), end.get(), stmt.get())
            }
            PNK::ExpressionStmt(expr) => writeln!(
                f,
                "ExpressionStmt({})",
                expr.map(|e| e.get().to_string()).unwrap_or("empty".to_string())
            ),
            PNK::EmptyStmt => writeln!(f, "EmptyStmt"),

            // Declarations & Definitions
            PNK::Declaration(data) => writeln!(f, "Declaration({:?})", data),
            PNK::FunctionDef(data) => writeln!(f, "FunctionDef({:?})", data),
            PNK::EnumConstant(name, val) => writeln!(
                f,
                "EnumConstant({}, {})",
                name,
                val.map(|v| v.get().to_string()).unwrap_or("auto".to_string())
            ),
            PNK::StaticAssert(cond, msg) => {
                let message_str = if let PNK::Literal(Literal::String(s)) = &ast.get_node(*msg).kind {
                    s.to_string()
                } else {
                    "<invalid>".to_string()
                };
                writeln!(f, "StaticAssert({}, \"{}\")", cond.get(), message_str)
            }

            PNK::TranslationUnit(decls) => {
                writeln!(f, "TranslationUnit(decls=[{}])", Self::format_parsed_list(decls))
            }
            PNK::InitializerList(inits) => writeln!(f, "InitializerList({:?})", inits),
            PNK::PragmaPack(kind) => writeln!(f, "PragmaPack({:?})", kind),
            PNK::Dummy => writeln!(f, "Dummy"),
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
            NodeKind::TranslationUnit(tu) => {
                writeln!(
                    f,
                    "TranslationUnit({}) (parser kind)",
                    Self::format_range("decls", tu.decl_start, tu.decl_len)
                )
            }
            NodeKind::Literal(literal) => writeln!(f, "{}", Self::format_literal(literal)),
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
                writeln!(
                    f,
                    "FunctionCall(callee={}, {})",
                    call_expr.callee.get(),
                    Self::format_range("args", call_expr.arg_start, call_expr.arg_len)
                )
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
            NodeKind::Cast(ty, expr)
            | NodeKind::CompoundLiteral(ty, expr)
            | NodeKind::BuiltinVaArg(ty, expr)
            | NodeKind::BuiltinOffsetof(ty, expr) => {
                let name = match kind {
                    NodeKind::Cast(_, _) => "Cast",
                    NodeKind::CompoundLiteral(_, _) => "CompoundLiteral",
                    NodeKind::BuiltinVaArg(_, _) => "BuiltinVaArg",
                    NodeKind::BuiltinOffsetof(_, _) => "BuiltinOffsetof",
                    _ => unreachable!(),
                };
                writeln!(f, "{}({}, {})", name, ty, expr.get())
            }
            NodeKind::BuiltinVaStart(ap, last) => {
                writeln!(f, "BuiltinVaStart({}, {})", ap.get(), last.get())
            }
            NodeKind::BuiltinVaCopy(dst, src) => {
                writeln!(f, "BuiltinVaCopy({}, {})", dst.get(), src.get())
            }
            NodeKind::BuiltinExpect(exp, c) => {
                writeln!(f, "BuiltinExpect({}, {})", exp.get(), c.get())
            }
            NodeKind::BuiltinVaEnd(exp)
            | NodeKind::BuiltinPopcount(exp)
            | NodeKind::BuiltinClz(exp)
            | NodeKind::BuiltinCtz(exp)
            | NodeKind::BuiltinFfs(exp)
            | NodeKind::BuiltinBswap16(exp)
            | NodeKind::BuiltinBswap32(exp)
            | NodeKind::BuiltinBswap64(exp)
            | NodeKind::BuiltinConstantP(exp)
            | NodeKind::SizeOfExpr(exp) => {
                let name = match kind {
                    NodeKind::BuiltinVaEnd(_) => "BuiltinVaEnd",
                    NodeKind::BuiltinPopcount(_) => "BuiltinPopcount",
                    NodeKind::BuiltinClz(_) => "BuiltinClz",
                    NodeKind::BuiltinCtz(_) => "BuiltinCtz",
                    NodeKind::BuiltinFfs(_) => "BuiltinFfs",
                    NodeKind::BuiltinBswap16(_) => "BuiltinBswap16",
                    NodeKind::BuiltinBswap32(_) => "BuiltinBswap32",
                    NodeKind::BuiltinBswap64(_) => "BuiltinBswap64",
                    NodeKind::BuiltinConstantP(_) => "BuiltinConstantP",
                    NodeKind::SizeOfExpr(_) => "SizeOfExpr",
                    _ => unreachable!(),
                };
                writeln!(f, "{}({})", name, exp.get())
            }
            NodeKind::SizeOfType(ty) | NodeKind::AlignOf(ty) => {
                let name = match kind {
                    NodeKind::SizeOfType(_) => "SizeOfType",
                    NodeKind::AlignOf(_) => "AlignOf",
                    _ => unreachable!(),
                };
                writeln!(f, "{}({})", name, ty)
            }
            NodeKind::BuiltinTypesCompatibleP(t1, t2) => {
                writeln!(f, "BuiltinTypesCompatibleP({}, {})", t1, t2)
            }
            NodeKind::AtomicOp(op, args_start, args_len) => {
                writeln!(
                    f,
                    "AtomicOp({:?}, {})",
                    op,
                    Self::format_range("args", *args_start, *args_len)
                )
            }

            NodeKind::GenericSelection(gs) => {
                writeln!(
                    f,
                    "GenericSelection(control={}, {})",
                    gs.control.get(),
                    Self::format_range("associations", gs.assoc_start, gs.assoc_len)
                )
            }
            NodeKind::GenericAssociation(ga) => {
                writeln!(
                    f,
                    "GenericAssociation(ty={:?}, result_expr={})",
                    ga.ty,
                    ga.result_expr.get()
                )
            }
            NodeKind::BuiltinChooseExpr(c, t, e) => {
                writeln!(f, "BuiltinChooseExpr({}, {}, {})", c.get(), t.get(), e.get())
            }
            NodeKind::BuiltinUnreachable => writeln!(f, "BuiltinUnreachable"),
            NodeKind::BuiltinTrap => writeln!(f, "BuiltinTrap"),
            NodeKind::GnuStatementExpr(compound_stmt, result_expr) => {
                writeln!(f, "GnuStatementExpr({}, {})", compound_stmt.get(), result_expr.get())
            }
            NodeKind::CompoundStmt(cs) => {
                writeln!(
                    f,
                    "{}",
                    Self::format_range("CompoundStmt(stmts", cs.stmt_start, cs.stmt_len)
                )
                // Note: CompoundStmt uses format_range differently to match the CompoundStmt(stmts=...) format
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
            NodeKind::ExpressionStmt(expr) => writeln!(
                f,
                "ExpressionStmt({})",
                expr.map(|r| r.get().to_string()).unwrap_or("none".to_string())
            ),

            NodeKind::Function(data) => {
                let func_name = Self::get_function_name(data.symbol, symbol_table);
                writeln!(
                    f,
                    "Function(name={}, symbol={:?}, ty={}, {}, body={})",
                    func_name,
                    data.symbol,
                    data.ty,
                    Self::format_range("params", data.param_start, data.param_len),
                    data.body.get()
                )
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
                let message_str = if let NodeKind::Literal(Literal::String(s)) = ast.get_kind(*msg) {
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
                writeln!(
                    f,
                    "RecordDecl(name={:?}, ty={}, is_union={}, {})",
                    record_decl.name,
                    record_decl.ty.get(),
                    record_decl.is_union,
                    Self::format_range("members", record_decl.member_start, record_decl.member_len)
                )
            }
            NodeKind::FieldDecl(field_decl) => {
                writeln!(f, "FieldDecl(name={:?}, ty={})", field_decl.name, field_decl.ty)
            }
            NodeKind::EnumDecl(enum_decl) => {
                writeln!(
                    f,
                    "EnumDecl(name={:?}, ty={}, {})",
                    enum_decl.name,
                    enum_decl.ty.get(),
                    Self::format_range("members", enum_decl.member_start, enum_decl.member_len)
                )
            }
            NodeKind::EnumMember(enum_member) => {
                writeln!(f, "EnumMember(name={}, value={})", enum_member.name, enum_member.value)
            }
            NodeKind::InitializerList(list) => {
                writeln!(
                    f,
                    "{}",
                    Self::format_range("InitializerList(inits", list.init_start, list.init_len)
                )
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
