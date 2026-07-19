//! AST Dumper module
//!
//! This module handles AST dumping for debugging and visualization.

use hashbrown::HashSet;
use std::fmt;
use std::fmt::Formatter;

use crate::ast::literal::LitVal;
use crate::ast::parsed::{PAst, PNodeKind, PNodeRef};
use crate::ast::{Ast, DesignatedInitializer, Designator, NodeKind, NodeRef};
use crate::semantic::{SymbolKind, SymbolRef, SymbolTable, TypeRef, TypeRegistry};

pub(crate) struct PAstDisplay<'a>(pub(crate) &'a PAst);

impl<'a> fmt::Display for PAstDisplay<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let ast = self.0;
        for (i, node) in ast.nodes.iter().enumerate() {
            if matches!(node.kind, PNodeKind::Dummy) {
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Collect all TypeRefs used in the AST
        let mut used_types = HashSet::new();

        for kind in &self.ast.kinds {
            AstDumper::collect_types(kind, &mut used_types);
        }

        if used_types.is_empty() {
            return Ok(());
        }

        // Print header
        writeln!(f, "\n=== TypeRegistry (Used TypeRefs) ===")?;

        // Sort TypeRefs for consistent output
        let mut sorted_types: Vec<_> = used_types.into_iter().collect();
        sorted_types.sort_by_key(|ty| ty.get());

        // Dump each used TypeRef with user-friendly formatting
        for ty in sorted_types {
            let formatted_type = self.registry.display_type(ty);
            writeln!(f, "TypeRef({}): {}", ty.base(), formatted_type)?;
        }
        Ok(())
    }
}

/// Dumper for AST
pub(crate) struct AstDumper;

impl AstDumper {
    /// Dump parsed AST to stdout
    pub(crate) fn dump_parsed_ast(ast: &PAst) -> PAstDisplay<'_> {
        PAstDisplay(ast)
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
    fn collect_types(kind: &NodeKind, types: &mut HashSet<TypeRef>) {
        match kind {
            NodeKind::Param(data) => {
                types.insert(data.qt.ty());
            }
            NodeKind::FieldDecl(field_decl) => {
                types.insert(field_decl.qt.ty());
            }
            NodeKind::Cast(qual_type, _)
            | NodeKind::CompoundLiteral(qual_type, _)
            | NodeKind::BuiltinVaArg(qual_type, _)
            | NodeKind::BuiltinOffsetof(qual_type, _)
            | NodeKind::SizeOfType(qual_type)
            | NodeKind::AlignOfType(qual_type) => {
                types.insert(qual_type.ty());
            }
            NodeKind::BuiltinTypesCompatibleP(t1, t2) => {
                types.insert(t1.ty());
                types.insert(t2.ty());
            }
            NodeKind::GenericAssociation(ga) => {
                if let Some(qual_type) = ga.ty {
                    types.insert(qual_type.ty());
                }
            }
            _ => {}
        }
    }

    /// Write function name from symbol entry reference
    fn write_function_name(
        f: &mut Formatter<'_>,
        symbol: SymbolRef,
        symbol_table: Option<&SymbolTable>,
    ) -> fmt::Result {
        if let Some(table) = symbol_table {
            let entry = table.get_symbol(symbol);
            return write!(f, "{}", entry.name);
        }
        write!(f, "func_{}", symbol.get())
    }

    fn write_designator(f: &mut Formatter<'_>, designator: &Designator) -> fmt::Result {
        match designator {
            Designator::FieldName(name) => write!(f, ".{}", name),
            Designator::ArrayIndex(idx) => write!(f, "[{}]", idx.raw()),
            Designator::ArrayRange(start, end) => write!(f, "[{} ... {}]", start.raw(), end.raw()),
        }
    }

    /// Write a DesignatedInitializer for display
    fn write_designated_initializer(f: &mut Formatter<'_>, init: &DesignatedInitializer, ast: &Ast) -> fmt::Result {
        for designator in init.designator_start.range(init.designator_len) {
            match ast.get_kind(designator) {
                NodeKind::Designator(d) => Self::write_designator(f, d)?,
                _ => write!(f, "<invalid designator>")?,
            }
        }

        if init.designator_len > 0 {
            write!(f, " = ")?;
        }

        write!(f, "{}", init.initializer.raw())
    }

    fn write_range(f: &mut Formatter<'_>, label: &str, start: NodeRef, len: impl Into<u32>) -> fmt::Result {
        let len = len.into();
        if len > 0 {
            let s = start.raw();
            write!(f, "{}={}..{}", label, s, s + len - 1)
        } else {
            write!(f, "{}=[]", label)
        }
    }

    fn format_literal(f: &mut Formatter<'_>, literal: &LitVal) -> fmt::Result {
        match literal {
            LitVal::Int { value, suffix, radix } => {
                write!(f, "LiteralInt({}, {:?}, base={})", value, suffix, radix)
            }
            LitVal::Float { suffix, .. } => {
                write!(f, "LiteralFloat({}, {:?})", literal.as_f64(), suffix)
            }
            LitVal::String { value, .. } => write!(f, "LiteralString(\"{}\")", String::from_utf8_lossy(value)),
            LitVal::Char(c, prefix) => {
                write!(f, "LiteralChar({}, {:?})", c, prefix)
            }
            LitVal::Nullptr => write!(f, "LiteralNull"),
            LitVal::True => write!(f, "LiteralTrue"),
            LitVal::False => write!(f, "LiteralFalse"),
        }
    }

    fn write_list(f: &mut Formatter<'_>, nodes: &[PNodeRef]) -> fmt::Result {
        for (i, n) in nodes.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", n.get())?;
        }
        Ok(())
    }

    fn write_parsed_list(f: &mut Formatter<'_>, label: &str, nodes: &[PNodeRef]) -> fmt::Result {
        write!(f, "{}=[", label)?;
        Self::write_list(f, nodes)?;
        write!(f, "]")
    }

    /// Dump a single parsed parsed node kind
    fn dump_parsed_node(f: &mut Formatter<'_>, kind: &PNodeKind, ast: &PAst) -> fmt::Result {
        let optional = |f: &mut Formatter<'_>, node: Option<PNodeRef>, text: &'static str| -> fmt::Result {
            match node {
                Some(n) => write!(f, "{}", n.get()),
                None => write!(f, "{}", text),
            }
        };
        use crate::ast::PNodeKind as PNK;

        if let PNK::Literal(literal) = kind {
            Self::format_literal(f, &literal.get_val())?;
            return writeln!(f);
        }
        if matches!(
            kind,
            PNK::Break | PNK::Continue | PNK::EmptyStmt | PNK::Dummy | PNK::PragmaPack(_) | PNK::PragmaVisibility(_)
        ) {
            return writeln!(f, "{}", kind.tagname());
        }

        write!(f, "{}(", kind.tagname())?;

        match kind {
            PNK::Ident(name) => write!(f, "{}", name)?,

            // One NodeRef: Tag(n1.get())
            PNK::SizeOfExpr(n1)
            | PNK::AlignOfExpr(n1)
            | PNK::PostIncrement(n1)
            | PNK::PostDecrement(n1)
            | PNK::Default(n1) => write!(f, "{}", n1.get())?,

            // Two NodeRefs: Tag(n1.get(), n2.get())
            PNK::GnuStatementExpr(n1, n2)
            | PNK::IndexAccess(n1, n2)
            | PNK::Switch(n1, n2)
            | PNK::Case(n1, n2)
            | PNK::BuiltinComplex(n1, n2) => write!(f, "{}, {}", n1.get(), n2.get())?,

            // Three NodeRefs: Tag(n1.get(), n2.get(), n3.get())
            PNK::TernaryOp(n1, n2, n3) | PNK::BuiltinChooseExpr(n1, n2, n3) | PNK::CaseRange(n1, n2, n3) => {
                write!(f, "{}, {}, {}", n1.get(), n2.get(), n3.get())?
            }

            // Binary Op / Assignment: Tag(op, l.get(), r.get())
            PNK::UnaryOp(op, n) => write!(f, "{:?}, {}", op, n.get())?,
            PNK::BinaryOp(op, l, r) | PNK::Assignment(op, l, r) => write!(f, "{:?}, {}, {}", op, l.get(), r.get())?,

            // TypeRef and NodeRef: Tag(ty, n.get())
            PNK::Cast(ty, n)
            | PNK::CompoundLiteral(ty, n)
            | PNK::BuiltinVaArg(ty, n)
            | PNK::BuiltinBitCast(ty, n)
            | PNK::BuiltinOffsetof(ty, n) => write!(f, "{:?}, {}", ty, n.get())?,

            PNK::BuiltinConvertVector(n, ty) => write!(f, "{}, {:?}", n.get(), ty)?,

            // TypeRef only: Tag(ty)
            PNK::SizeOfType(ty) | PNK::AlignOfType(ty) => write!(f, "{:?}", ty)?,

            PNK::BuiltinTypesCompatibleP(boxed) => {
                let (t1, t2) = &**boxed;
                write!(f, "{:?}, {:?}", t1, t2)?
            }

            PNK::FunctionCall(callee, args) => {
                write!(f, "callee={}, ", callee.get())?;
                Self::write_parsed_list(f, "args", args)?
            }
            PNK::MemberAccess(obj, field, arrow) => {
                write!(f, "{}, {}, {}", obj.get(), field, if *arrow { "->" } else { "." })?
            }

            PNK::GenericSelection(ctrl, assocs) => write!(f, "{}, {:?}", ctrl.get(), assocs)?,

            PNK::CompoundStmt(stmts, _) => Self::write_parsed_list(f, "stmts", stmts)?,
            PNK::If(data) => write!(f, "{:?}", data)?,
            PNK::While(data) => write!(f, "{:?}", data)?,
            PNK::For(data) => write!(f, "{:?}", data)?,
            PNK::Declaration(data) => write!(f, "{:?}", data)?,
            PNK::FunctionDef(data) => write!(f, "{:?}", data)?,
            PNK::DoWhile(body, cond) => write!(f, "body={}, cond={}", body.get(), cond.get())?,
            PNK::Return(expr) => optional(f, *expr, "void")?,
            PNK::Goto(label) => write!(f, "{}", label)?,
            PNK::Label(label, stmt) => write!(f, "{}, {}", label, stmt.get())?,
            PNK::ExpressionStmt(expr) => optional(f, *expr, "empty")?,
            PNK::AsmStmt(_) => write!(f, "asm")?,

            PNK::EnumConstant(name, val) => {
                write!(f, "{}, ", name)?;
                optional(f, *val, "auto")?
            }
            PNK::StaticAssert(cond, msg) => {
                let message_str = match msg.map(|m| &ast.get_node(m).kind) {
                    Some(PNK::Literal(lit)) => match lit.get_val() {
                        LitVal::String { value, .. } => String::from_utf8_lossy(&value).into_owned(),
                        _ => "<invalid>".to_string(),
                    },
                    Some(_) => "<invalid>".to_string(),
                    None => "<none>".to_string(),
                };
                write!(f, "{}, \"{}\"", cond.get(), message_str)?
            }

            PNK::TranslationUnit(decls) => Self::write_parsed_list(f, "decls", decls)?,
            PNK::InitializerList(inits) => write!(f, "{:?}", inits)?,
            _ => unreachable!(),
        }

        writeln!(f, ")")
    }

    /// Dump a single AST node kind
    fn dump_node(f: &mut Formatter<'_>, kind: &NodeKind, ast: &Ast, symbol_table: Option<&SymbolTable>) -> fmt::Result {
        let optional = |f: &mut Formatter<'_>, node: Option<NodeRef>, text: &'static str| -> fmt::Result {
            match node {
                Some(n) => write!(f, "{}", n.raw()),
                None => write!(f, "{}", text),
            }
        };
        let get_sym = |sym_ref| symbol_table.map(|st| st.get_symbol(sym_ref));

        if let NodeKind::Literal(literal) = kind {
            Self::format_literal(f, &literal.get_val())?;
            return writeln!(f);
        }
        if matches!(kind, NodeKind::Break | NodeKind::Continue | NodeKind::Dummy) {
            return writeln!(f, "{}", kind.tagname());
        }

        write!(f, "{}(", kind.tagname())?;

        match kind {
            NodeKind::TranslationUnit(tu) => Self::write_range(f, "decls", tu.decl_start, tu.decl_len)?,
            NodeKind::Ident(sym, _) => write!(f, "{}", sym)?,

            // One NodeRef: Tag(n1.get())
            NodeKind::PostIncrement(n)
            | NodeKind::PostDecrement(n)
            | NodeKind::Default(n)
            | NodeKind::SizeOfExpr(n)
            | NodeKind::AlignOfExpr(n)
            | NodeKind::BuiltinConvertVector(n, _) => write!(f, "{}", n.raw())?,

            // Two NodeRefs: Tag(n1.get(), n2.get())
            NodeKind::IndexAccess(n1, n2)
            | NodeKind::Case(n1, n2)
            | NodeKind::StatementExpr(n1, n2)
            | NodeKind::DoWhile(n1, n2)
            | NodeKind::Switch(n1, n2)
            | NodeKind::BuiltinComplex(n1, n2) => write!(f, "{}, {}", n1.raw(), n2.raw())?,

            // Three NodeRefs: Tag(n1.get(), n2.get(), n3.get())
            NodeKind::TernaryOp(n1, n2, n3)
            | NodeKind::BuiltinChooseExpr(n1, n2, n3)
            | NodeKind::CaseRange(n1, n2, n3) => write!(f, "{}, {}, {}", n1.raw(), n2.raw(), n3.raw())?,

            // Binary Op / Assignment: Tag(op, l.get(), r.get())
            NodeKind::UnaryOp(op, n) => write!(f, "{:?}, {}", op, n.raw())?,
            NodeKind::BinaryOp(op, l, r) | NodeKind::Assignment(op, l, r) => {
                write!(f, "{:?}, {}, {}", op, l.raw(), r.raw())?
            }

            // TypeRef and NodeRef: Tag(ty, n.get())
            NodeKind::Cast(ty, n)
            | NodeKind::CompoundLiteral(ty, n)
            | NodeKind::BuiltinVaArg(ty, n)
            | NodeKind::BuiltinBitCast(ty, n)
            | NodeKind::BuiltinOffsetof(ty, n) => write!(f, "{}, {}", ty, n.raw())?,

            // TypeRef only: Tag(ty)
            NodeKind::SizeOfType(ty) | NodeKind::AlignOfType(ty) => write!(f, "{}", ty)?,

            NodeKind::BuiltinTypesCompatibleP(t1, t2) => write!(f, "{}, {}", t1, t2)?,

            NodeKind::FunctionCall(call_expr) => {
                write!(f, "callee={}, ", call_expr.callee.raw())?;
                Self::write_range(f, "args", call_expr.arg_start, call_expr.arg_len)?
            }

            NodeKind::MemberAccess(obj, field, is_arrow) => {
                write!(f, "{}, {}, {}", obj.raw(), field, if *is_arrow { "->" } else { "." })?
            }

            NodeKind::GenericSelection(gs) => {
                write!(f, "control={}, ", gs.control.raw())?;
                Self::write_range(f, "associations", gs.assoc_start, gs.assoc_len)?
            }
            NodeKind::GenericAssociation(ga) => write!(f, "ty={:?}, result_expr={}", ga.ty, ga.result_expr.raw())?,

            NodeKind::CompoundStmt(cs) => Self::write_range(f, "stmts", cs.stmt_start, cs.stmt_len)?,
            NodeKind::DeclList(dl) => Self::write_range(f, "decls", dl.stmt_start, dl.stmt_len)?,
            NodeKind::If(if_stmt) => {
                write!(
                    f,
                    "condition={}, then={}, else=",
                    if_stmt.condition.raw(),
                    if_stmt.then_branch.raw()
                )?;
                optional(f, if_stmt.else_branch, "none")?
            }
            NodeKind::While(while_stmt) => write!(
                f,
                "condition={}, body={}",
                while_stmt.condition.raw(),
                while_stmt.body.raw()
            )?,
            NodeKind::For(for_stmt) => {
                write!(f, "child_start={}", for_stmt.child_start.raw())?;
                write!(f, ", body={}", for_stmt.body.raw())?
            }
            NodeKind::Return(expr) => optional(f, *expr, "void")?,
            NodeKind::Goto(label, _) => write!(f, "{}", label)?,
            NodeKind::Label(label, stmt, _) => write!(f, "{}, {}", label, stmt.raw())?,
            NodeKind::ExpressionStmt(expr) => optional(f, *expr, "none")?,
            NodeKind::AsmStmt(_) => write!(f, "asm")?,

            NodeKind::FunctionDef(data) => {
                write!(f, "name=")?;
                Self::write_function_name(f, data.symbol, symbol_table)?;
                write!(f, ", symbol={:?}, ", data.symbol)?;

                let body_node = data.child_start.add_offset(data.param_len);
                Self::write_range(f, "params", data.child_start, data.param_len)?;
                write!(f, ", body={}", body_node.raw())?
            }
            NodeKind::Param(data) => write!(f, "symbol={:?}, ty={:?}", data.symbol, data.qt)?,
            NodeKind::StaticAssert(cond, msg) => {
                let message_str = match msg.map(|m| ast.get_kind(m)) {
                    Some(NodeKind::Literal(lit)) => match lit.get_val() {
                        LitVal::String { value, .. } => String::from_utf8_lossy(&value).into_owned(),
                        _ => "<not-a-string-literal>".to_string(),
                    },
                    Some(_) => "<invalid>".to_string(),
                    None => "<none>".to_string(),
                };
                write!(f, "condition={}, message=\"{}\"", cond.raw(), message_str)?
            }
            NodeKind::VarDecl(decl) => {
                write!(f, "symbol={:?}", decl.symbol)?;
                if let Some(sym) = get_sym(decl.symbol) {
                    write!(f, ", name={}, ty={}", sym.name, sym.type_info)?;
                }
                if let Some(init) = decl.init {
                    write!(f, ", init={}", init.raw())?;
                }
            }
            NodeKind::FunctionDecl(decl) => {
                write!(f, "symbol={:?}", decl.symbol)?;
                if let Some(sym) = get_sym(decl.symbol) {
                    let storage = sym.get_function_storage();
                    write!(f, ", name={}, ty={}, storage={:?}", sym.name, sym.type_info, storage)?;
                }
            }
            NodeKind::TypedefDecl(decl) => {
                write!(f, "symbol={:?}", decl.symbol)?;
                if let Some(sym) = get_sym(decl.symbol)
                    && let SymbolKind::Typedef(aliased_type) = sym.kind
                {
                    write!(f, ", name={}, qt={}", sym.name, aliased_type)?;
                }
            }
            NodeKind::RecordDecl(decl) => {
                write!(f, "symbol={:?}", decl.symbol)?;
                if let Some(sym) = get_sym(decl.symbol) {
                    write!(f, ", name={:?}, ty={}", sym.name, sym.type_info)?;
                }
                write!(f, ", ")?;
                Self::write_range(f, "members", decl.member_start, decl.member_len)?
            }
            NodeKind::FieldDecl(decl) => write!(f, "name={:?}, ty={}", decl.name, decl.qt)?,
            NodeKind::EnumDecl(decl) => {
                write!(f, "symbol={:?}", decl.symbol)?;
                if let Some(sym) = get_sym(decl.symbol) {
                    write!(f, ", name={:?}, ty={}, ", sym.name, sym.type_info)?;
                }
                Self::write_range(f, "members", decl.member_start, decl.member_len)?
            }
            NodeKind::EnumMember(member) => {
                write!(f, "symbol={:?}", member.symbol)?;
                if let Some(sym) = get_sym(member.symbol)
                    && let crate::semantic::symbol_table::SymbolKind::EnumConstant { value } = sym.kind
                {
                    write!(f, ", name={}, value={}", sym.name, value)?;
                }
            }
            NodeKind::InitializerList(list) => Self::write_range(f, "inits", list.init_start, list.init_len)?,
            NodeKind::InitializerItem(init) => Self::write_designated_initializer(f, init, ast)?,
            NodeKind::Designator(d) => Self::write_designator(f, d)?,
            _ => unreachable!(),
        }

        writeln!(f, ")")
    }
}
