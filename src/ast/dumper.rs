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
            AstDumper::dump_parsed_node(f, &node.kind, ast)?;
        }
        Ok(())
    }
}

pub(crate) struct AstDisplay<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: Option<&'a SymbolTable>,
}

impl<'a> fmt::Display for AstDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ast = self.ast;
        for (i, kind) in ast.kinds.iter().enumerate() {
            if matches!(kind, NodeKind::Dummy) {
                continue;
            }
            write!(f, "{}: ", i + 1)?;
            AstDumper::dump_node(f, kind, ast, self.symbol_table)?;
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
            AstDumper::collect_type_refs(kind, &mut used_type_refs);
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

    /// Dump AST to stdout
    pub(crate) fn dump_ast<'a>(ast: &'a Ast, symbol_table: Option<&'a SymbolTable>) -> AstDisplay<'a> {
        AstDisplay { ast, symbol_table }
    }

    /// Dump TypeRegistry information for used TypeRefs in the AST
    pub(crate) fn dump_type_registry<'a>(ast: &'a Ast, registry: &'a TypeRegistry) -> TypeRegistryDisplay<'a> {
        TypeRegistryDisplay { ast, registry }
    }

    /// Collect TypeRefs from a NodeKind
    fn collect_type_refs(kind: &NodeKind, type_refs: &mut HashSet<TypeRef>) {
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

    fn format_list(nodes: &[ParsedNodeRef]) -> String {
        nodes.iter().map(|n| n.get().to_string()).collect::<Vec<_>>().join(", ")
    }

    /// Dump a single parsed parsed node kind
    fn dump_parsed_node(f: &mut fmt::Formatter<'_>, kind: &ParsedNodeKind, ast: &ParsedAst) -> fmt::Result {
        fn optional(node: Option<ParsedNodeRef>, text: &'static str) -> String {
            node.map(|n| n.get().to_string()).unwrap_or(text.to_string())
        }
        use crate::ast::ParsedNodeKind as PNK;

        match kind {
            PNK::Literal(literal) => return writeln!(f, "{}", Self::format_literal(literal)),
            PNK::Break | PNK::Continue | PNK::EmptyStmt | PNK::Dummy | PNK::BuiltinUnreachable | PNK::BuiltinTrap => {
                return writeln!(f, "{}", kind.tagname());
            }
            _ => {}
        }

        write!(f, "{}(", kind.tagname())?;

        match kind {
            PNK::Ident(name) => write!(f, "{}", name)?,

            // One NodeRef: Tag(n1.get())
            PNK::BuiltinVaEnd(n1)
            | PNK::BuiltinPopcount(n1)
            | PNK::BuiltinClz(n1)
            | PNK::BuiltinCtz(n1)
            | PNK::BuiltinFfs(n1)
            | PNK::BuiltinBswap16(n1)
            | PNK::BuiltinBswap32(n1)
            | PNK::BuiltinBswap64(n1)
            | PNK::BuiltinConstantP(n1)
            | PNK::SizeOfExpr(n1)
            | PNK::PostIncrement(n1)
            | PNK::PostDecrement(n1)
            | PNK::Default(n1) => write!(f, "{}", n1.get())?,

            // Two NodeRefs: Tag(n1.get(), n2.get())
            PNK::GnuStatementExpr(n1, n2)
            | PNK::IndexAccess(n1, n2)
            | PNK::Switch(n1, n2)
            | PNK::Case(n1, n2)
            | PNK::BuiltinVaStart(n1, n2)
            | PNK::BuiltinVaCopy(n1, n2)
            | PNK::BuiltinExpect(n1, n2) => write!(f, "{}, {}", n1.get(), n2.get())?,

            // Three NodeRefs: Tag(n1.get(), n2.get(), n3.get())
            PNK::TernaryOp(n1, n2, n3) | PNK::BuiltinChooseExpr(n1, n2, n3) | PNK::CaseRange(n1, n2, n3) => {
                write!(f, "{}, {}, {}", n1.get(), n2.get(), n3.get())?
            }

            // Binary Op / Assignment: Tag(op, l.get(), r.get())
            PNK::UnaryOp(op, n) => write!(f, "{:?}, {}", op, n.get())?,
            PNK::BinaryOp(op, l, r) | PNK::Assignment(op, l, r) => write!(f, "{:?}, {}, {}", op, l.get(), r.get())?,

            // TypeRef and NodeRef: Tag(ty, n.get())
            PNK::Cast(ty, n) | PNK::CompoundLiteral(ty, n) | PNK::BuiltinVaArg(ty, n) | PNK::BuiltinOffsetof(ty, n) => {
                write!(f, "{:?}, {}", ty, n.get())?
            }

            // TypeRef only: Tag(ty)
            PNK::SizeOfType(ty) | PNK::AlignOf(ty) => write!(f, "{:?}", ty)?,

            PNK::BuiltinTypesCompatibleP(t1, t2) => write!(f, "{:?}, {:?}", t1, t2)?,

            PNK::FunctionCall(callee, args) => {
                write!(f, "callee={}, args=[{}]", callee.get(), Self::format_list(args))?
            }
            PNK::MemberAccess(obj, field, arrow) => {
                write!(f, "{}, {}, {}", obj.get(), field, if *arrow { "->" } else { "." })?
            }

            PNK::AtomicOp(op, args) => write!(f, "{:?}, args=[{}]", op, Self::format_list(args))?,
            PNK::GenericSelection(ctrl, assocs) => write!(f, "{}, {:?}", ctrl.get(), assocs)?,

            PNK::CompoundStmt(stmts) => write!(f, "stmts=[{}]", Self::format_list(stmts))?,
            PNK::If(data) => write!(f, "{:?}", data)?,
            PNK::While(data) => write!(f, "{:?}", data)?,
            PNK::For(data) => write!(f, "{:?}", data)?,
            PNK::Declaration(data) => write!(f, "{:?}", data)?,
            PNK::FunctionDef(data) => write!(f, "{:?}", data)?,
            PNK::DoWhile(body, cond) => write!(f, "body={}, cond={}", body.get(), cond.get())?,
            PNK::Return(expr) => write!(f, "{}", optional(*expr, "void"))?,
            PNK::Goto(label) => write!(f, "{}", label)?,
            PNK::Label(label, stmt) => write!(f, "{}, {}", label, stmt.get())?,
            PNK::ExpressionStmt(expr) => write!(f, "{}", optional(*expr, "empty"))?,

            PNK::EnumConstant(name, val) => write!(f, "{}, {}", name, optional(*val, "auto"))?,
            PNK::StaticAssert(cond, msg) => {
                let message_str = if let PNK::Literal(Literal::String(s)) = &ast.get_node(*msg).kind {
                    s.to_string()
                } else {
                    "<invalid>".to_string()
                };
                write!(f, "{}, \"{}\"", cond.get(), message_str)?
            }

            PNK::TranslationUnit(decls) => write!(f, "decls=[{}]", Self::format_list(decls))?,
            PNK::InitializerList(inits) => write!(f, "{:?}", inits)?,
            PNK::PragmaPack(kind_pack) => write!(f, "{:?}", kind_pack)?,
            _ => unreachable!(),
        }

        writeln!(f, ")")
    }

    /// Dump a single AST node kind
    fn dump_node(
        f: &mut fmt::Formatter<'_>,
        kind: &NodeKind,
        ast: &Ast,
        symbol_table: Option<&SymbolTable>,
    ) -> fmt::Result {
        fn optional(node: Option<NodeRef>, text: &'static str) -> String {
            node.map(|n| n.get().to_string()).unwrap_or(text.to_string())
        }

        match kind {
            NodeKind::Literal(literal) => return writeln!(f, "{}", Self::format_literal(literal)),
            NodeKind::Break
            | NodeKind::Continue
            | NodeKind::Dummy
            | NodeKind::BuiltinUnreachable
            | NodeKind::BuiltinTrap => {
                return writeln!(f, "{}", kind.tagname());
            }
            _ => {}
        }

        write!(f, "{}(", kind.tagname())?;

        match kind {
            NodeKind::TranslationUnit(tu) => write!(f, "{}", Self::format_range("decls", tu.decl_start, tu.decl_len))?,
            NodeKind::Ident(sym, _) => write!(f, "{}", sym)?,

            // One NodeRef: Tag(n1.get())
            NodeKind::PostIncrement(n)
            | NodeKind::PostDecrement(n)
            | NodeKind::Default(n)
            | NodeKind::BuiltinVaEnd(n)
            | NodeKind::BuiltinPopcount(n)
            | NodeKind::BuiltinClz(n)
            | NodeKind::BuiltinCtz(n)
            | NodeKind::BuiltinFfs(n)
            | NodeKind::BuiltinBswap16(n)
            | NodeKind::BuiltinBswap32(n)
            | NodeKind::BuiltinBswap64(n)
            | NodeKind::BuiltinConstantP(n)
            | NodeKind::SizeOfExpr(n) => write!(f, "{}", n.get())?,

            // Two NodeRefs: Tag(n1.get(), n2.get())
            NodeKind::IndexAccess(n1, n2)
            | NodeKind::Case(n1, n2)
            | NodeKind::GnuStatementExpr(n1, n2)
            | NodeKind::DoWhile(n1, n2)
            | NodeKind::Switch(n1, n2)
            | NodeKind::BuiltinVaStart(n1, n2)
            | NodeKind::BuiltinVaCopy(n1, n2)
            | NodeKind::BuiltinExpect(n1, n2) => write!(f, "{}, {}", n1.get(), n2.get())?,

            // Three NodeRefs: Tag(n1.get(), n2.get(), n3.get())
            NodeKind::TernaryOp(n1, n2, n3)
            | NodeKind::BuiltinChooseExpr(n1, n2, n3)
            | NodeKind::CaseRange(n1, n2, n3) => write!(f, "{}, {}, {}", n1.get(), n2.get(), n3.get())?,

            // Binary Op / Assignment: Tag(op, l.get(), r.get())
            NodeKind::UnaryOp(op, n) => write!(f, "{:?}, {}", op, n.get())?,
            NodeKind::BinaryOp(op, l, r) | NodeKind::Assignment(op, l, r) => {
                write!(f, "{:?}, {}, {}", op, l.get(), r.get())?
            }

            // TypeRef and NodeRef: Tag(ty, n.get())
            NodeKind::Cast(ty, n)
            | NodeKind::CompoundLiteral(ty, n)
            | NodeKind::BuiltinVaArg(ty, n)
            | NodeKind::BuiltinOffsetof(ty, n) => write!(f, "{}, {}", ty, n.get())?,

            // TypeRef only: Tag(ty)
            NodeKind::SizeOfType(ty) | NodeKind::AlignOf(ty) => write!(f, "{}", ty)?,

            NodeKind::BuiltinTypesCompatibleP(t1, t2) => write!(f, "{}, {}", t1, t2)?,

            NodeKind::FunctionCall(call_expr) => write!(
                f,
                "callee={}, {}",
                call_expr.callee.get(),
                Self::format_range("args", call_expr.arg_start, call_expr.arg_len)
            )?,

            NodeKind::MemberAccess(obj, field, is_arrow) => {
                write!(f, "{}, {}, {}", obj.get(), field, if *is_arrow { "->" } else { "." })?
            }

            NodeKind::AtomicOp(op, args_start, args_len) => {
                write!(f, "{:?}, {}", op, Self::format_range("args", *args_start, *args_len))?
            }

            NodeKind::GenericSelection(gs) => write!(
                f,
                "control={}, {}",
                gs.control.get(),
                Self::format_range("associations", gs.assoc_start, gs.assoc_len)
            )?,
            NodeKind::GenericAssociation(ga) => write!(f, "ty={:?}, result_expr={}", ga.ty, ga.result_expr.get())?,

            NodeKind::CompoundStmt(cs) => write!(f, "{}", Self::format_range("stmts", cs.stmt_start, cs.stmt_len))?,
            NodeKind::If(if_stmt) => write!(
                f,
                "condition={}, then={}, else={}",
                if_stmt.condition.get(),
                if_stmt.then_branch.get(),
                optional(if_stmt.else_branch, "none")
            )?,
            NodeKind::While(while_stmt) => write!(
                f,
                "condition={}, body={}",
                while_stmt.condition.get(),
                while_stmt.body.get()
            )?,
            NodeKind::For(for_stmt) => write!(
                f,
                "init={}, condition={}, increment={}, body={}",
                optional(for_stmt.init, "none"),
                optional(for_stmt.condition, "none"),
                optional(for_stmt.increment, "none"),
                for_stmt.body.get()
            )?,
            NodeKind::Return(expr) => write!(f, "{}", optional(*expr, "void"))?,
            NodeKind::Goto(label, _) => write!(f, "{}", label)?,
            NodeKind::Label(label, stmt, _) => write!(f, "{}, {}", label, stmt.get())?,
            NodeKind::ExpressionStmt(expr) => write!(f, "{}", optional(*expr, "none"))?,

            NodeKind::Function(data) => {
                let func_name = Self::get_function_name(data.symbol, symbol_table);
                write!(
                    f,
                    "name={}, symbol={:?}, ty={}, {}, body={}",
                    func_name,
                    data.symbol,
                    data.ty,
                    Self::format_range("params", data.param_start, data.param_len),
                    data.body.get()
                )?
            }
            NodeKind::Param(data) => write!(f, "symbol={:?}, ty={:?}", data.symbol, data.ty)?,
            NodeKind::EnumConstant(name, value) => write!(f, "{}, {}", name, optional(*value, "auto"))?,
            NodeKind::StaticAssert(cond, msg) => {
                let message_str = if let NodeKind::Literal(Literal::String(s)) = ast.get_kind(*msg) {
                    s.to_string()
                } else {
                    "<invalid>".to_string()
                };
                write!(f, "condition={}, message=\"{}\"", cond.get(), message_str)?
            }
            NodeKind::VarDecl(decl) => write!(
                f,
                "name={}, ty={}, storage={:?}, is_tls={}",
                decl.name, decl.ty, decl.storage, decl.is_thread_local
            )?,
            NodeKind::FunctionDecl(decl) => write!(
                f,
                "name={}, ty={}, storage={:?}",
                decl.name,
                decl.ty.get(),
                decl.storage
            )?,
            NodeKind::TypedefDecl(decl) => write!(f, "name={}, ty={}", decl.name, decl.ty)?,
            NodeKind::RecordDecl(decl) => write!(
                f,
                "name={:?}, ty={}, is_union={}, {}",
                decl.name,
                decl.ty.get(),
                decl.is_union,
                Self::format_range("members", decl.member_start, decl.member_len)
            )?,
            NodeKind::FieldDecl(decl) => write!(f, "name={:?}, ty={}", decl.name, decl.ty)?,
            NodeKind::EnumDecl(decl) => write!(
                f,
                "name={:?}, ty={}, {}",
                decl.name,
                decl.ty.get(),
                Self::format_range("members", decl.member_start, decl.member_len)
            )?,
            NodeKind::EnumMember(member) => write!(f, "name={}, value={}", member.name, member.value)?,
            NodeKind::InitializerList(list) => {
                write!(f, "{}", Self::format_range("inits", list.init_start, list.init_len))?
            }
            NodeKind::InitializerItem(init) => write!(f, "{}", Self::format_designated_initializer(init, ast))?,
            NodeKind::Designator(d) => match d {
                Designator::FieldName(name) => write!(f, ".{}", name)?,
                Designator::ArrayIndex(idx) => write!(f, "[{}]", idx.get())?,
                Designator::GnuArrayRange(start, end) => write!(f, "[{} ... {}]", start.get(), end.get())?,
            },
            _ => unreachable!(),
        }

        writeln!(f, ")")
    }
}
