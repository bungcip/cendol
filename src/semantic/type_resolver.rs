use crate::{
    ast::{nodes::*, *},
    diagnostic::SemanticError,
    semantic::{
        SymbolTable, TypeContext, conversions::usual_arithmetic_conversions, type_context::QualType,
        utils::is_scalar_type,
    },
};

pub fn run_type_resolver(
    ast: &Ast,
    diag: &mut crate::diagnostic::DiagnosticEngine,
    symbol_table: &SymbolTable,
    type_ctx: &mut TypeContext,
) {
    let mut resolver = TypeResolver {
        ast,
        diag,
        symbol_table,
        type_ctx,
        current_function_ret_type: None,
    };
    let root = ast.get_root();
    resolver.visit_node(root);
}

struct TypeResolver<'a> {
    ast: &'a Ast,
    diag: &'a mut crate::diagnostic::DiagnosticEngine,
    symbol_table: &'a SymbolTable,
    type_ctx: &'a mut TypeContext,
    current_function_ret_type: Option<QualType>,
}

impl<'a> TypeResolver<'a> {
    fn report_error(&mut self, error: SemanticError) {
        self.diag.report(error);
    }

    fn is_lvalue(&self, node_ref: NodeRef) -> bool {
        let node_kind = &self.ast.get_node(node_ref).kind;
        match node_kind {
            NodeKind::Ident(_, symbol) => {
                if let Some(symbol_ref) = symbol.get() {
                    let symbol = self.symbol_table.get_symbol(symbol_ref);
                    matches!(symbol.kind, crate::semantic::SymbolKind::Variable { .. })
                } else {
                    false
                }
            }
            NodeKind::UnaryOp(op, _) => matches!(*op, UnaryOp::Deref),
            NodeKind::IndexAccess(..) => true,
            NodeKind::MemberAccess(obj_ref, _, is_arrow) => *is_arrow || self.is_lvalue(*obj_ref),
            NodeKind::LiteralString(..) => true,
            NodeKind::CompoundLiteral(..) => true,
            _ => false,
        }
    }

    fn visit_if_statement(&mut self, stmt: &IfStmt) {
        if let Some(cond_ty) = self.visit_node(stmt.condition) {
            if !is_scalar_type(cond_ty, self.type_ctx) {
                // report error
            }
        }
        self.visit_node(stmt.then_branch);
        if let Some(else_branch) = stmt.else_branch {
            self.visit_node(else_branch);
        }
    }

    fn visit_while_statement(&mut self, stmt: &WhileStmt) {
        if let Some(cond_ty) = self.visit_node(stmt.condition) {
            if !is_scalar_type(cond_ty, self.type_ctx) {
                // report error
            }
        }
        self.visit_node(stmt.body);
    }

    fn visit_for_statement(&mut self, stmt: &ForStmt) {
        if let Some(init) = stmt.init {
            self.visit_node(init);
        }
        if let Some(cond) = stmt.condition {
            if let Some(cond_ty) = self.visit_node(cond) {
                if !is_scalar_type(cond_ty, self.type_ctx) {
                    // report error
                }
            }
        }
        if let Some(inc) = stmt.increment {
            self.visit_node(inc);
        }
        self.visit_node(stmt.body);
    }

    fn visit_return_statement(&mut self, expr: &Option<NodeRef>, _span: SourceSpan) {
        let ret_ty = self.current_function_ret_type;
        let is_void_func = ret_ty.map_or(false, |ty| self.type_ctx.get(ty.ty).kind == TypeKind::Void);

        if let Some(expr_ref) = expr {
            if is_void_func {
                // self.report_error(SemanticError::VoidReturnWithValue { span });
            }
            self.visit_node(*expr_ref);
        } else if !is_void_func {
            // self.report_error(SemanticError::NonVoidReturnWithoutValue { span });
        }
    }

    fn visit_unary_op(&mut self, op: UnaryOp, operand_ref: NodeRef, full_span: SourceSpan) -> Option<QualType> {
        let operand_ty = self.visit_node(operand_ref)?;
        let operand_kind = &self.type_ctx.get(operand_ty.ty).kind;

        match op {
            UnaryOp::AddrOf => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span: full_span });
                    return None;
                }
                Some(QualType::unqualified(self.type_ctx.pointer_to(operand_ty.ty)))
            }
            UnaryOp::Deref => match operand_kind {
                TypeKind::Pointer { pointee } => Some(QualType::unqualified(*pointee)),
                _ => None,
            },
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span: full_span });
                }
                if is_scalar_type(operand_ty, self.type_ctx) {
                    Some(operand_ty)
                } else {
                    None
                }
            }
            UnaryOp::Plus | UnaryOp::Minus => {
                if is_scalar_type(operand_ty, self.type_ctx) {
                    Some(operand_ty)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn visit_binary_op(&mut self, _op: BinaryOp, lhs_ref: NodeRef, rhs_ref: NodeRef) -> Option<QualType> {
        let lhs_ty = self.visit_node(lhs_ref)?;
        let rhs_ty = self.visit_node(rhs_ref)?;
        usual_arithmetic_conversions(self.type_ctx, lhs_ty, rhs_ty)
    }

    fn visit_assignment(&mut self, lhs_ref: NodeRef, rhs_ref: NodeRef, full_span: SourceSpan) -> Option<QualType> {
        let lhs_ty = self.visit_node(lhs_ref)?;
        self.visit_node(rhs_ref)?;

        if !self.is_lvalue(lhs_ref) {
            self.report_error(SemanticError::NotAnLvalue { span: full_span });
        }
        Some(lhs_ty)
    }

    fn visit_function_call(&mut self, func_ref: NodeRef, args: &[NodeRef]) -> Option<QualType> {
        for arg in args {
            self.visit_node(*arg);
        }

        let func_ty = self.visit_node(func_ref).unwrap();
        let func_kind = self.type_ctx.get(func_ty.ty).kind.clone();

        match func_kind {
            TypeKind::Function { return_type, .. } => Some(QualType::unqualified(return_type)),
            TypeKind::Pointer { pointee } => {
                let pointee_kind = &self.type_ctx.get(pointee).kind;
                if let TypeKind::Function { return_type, .. } = pointee_kind {
                    Some(QualType::unqualified(*return_type))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn visit_member_access(&mut self, obj_ref: NodeRef, field_name: NameId, is_arrow: bool) -> Option<QualType> {
        let obj_ty = self.visit_node(obj_ref)?;
        let obj_kind = &self.type_ctx.get(obj_ty.ty).kind;

        let record_ty_ref = if is_arrow {
            if let TypeKind::Pointer { pointee } = obj_kind {
                *pointee
            } else {
                return None; // Error: arrow access on non-pointer
            }
        } else {
            obj_ty.ty
        };

        if let TypeKind::Record { members, .. } = &self.type_ctx.get(record_ty_ref).kind {
            // Find the member
            if let Some(member) = members.iter().find(|m| m.name == field_name) {
                return Some(member.member_type);
            }
        }

        None // Error: field not found or not a struct/union
    }

    fn visit_index_access(&mut self, arr_ref: NodeRef, idx_ref: NodeRef) -> Option<QualType> {
        self.visit_node(idx_ref);
        let arr_ty = self.visit_node(arr_ref)?;
        let arr_kind = &self.type_ctx.get(arr_ty.ty).kind;

        match arr_kind {
            TypeKind::Array { element_type, .. } => Some(QualType::unqualified(*element_type)),
            TypeKind::Pointer { pointee } => Some(QualType::unqualified(*pointee)),
            _ => None,
        }
    }

    fn visit_node(&mut self, node_ref: NodeRef) -> Option<QualType> {
        let node = self.ast.get_node(node_ref);
        let result_type = match node.kind.clone() {
            NodeKind::TranslationUnit(nodes) => {
                for child in nodes {
                    self.visit_node(child);
                }
                None
            }
            NodeKind::Function(data) => {
                let func_ty = self.type_ctx.get(data.ty);
                if let TypeKind::Function { return_type, .. } = func_ty.kind.clone() {
                    self.current_function_ret_type = Some(QualType::unqualified(return_type));
                }
                self.visit_node(data.body);
                self.current_function_ret_type = None;
                None
            }
            NodeKind::VarDecl(data) => {
                if let Some(init) = data.init {
                    self.visit_node(init);
                }
                None
            }
            NodeKind::DeclarationList(nodes) | NodeKind::CompoundStatement(nodes) => {
                for child in nodes {
                    self.visit_node(child);
                }
                None
            }
            NodeKind::If(stmt) => {
                self.visit_if_statement(&stmt);
                None
            }
            NodeKind::While(stmt) => {
                self.visit_while_statement(&stmt);
                None
            }
            NodeKind::For(stmt) => {
                self.visit_for_statement(&stmt);
                None
            }
            NodeKind::DoWhile(body, condition) => {
                self.visit_node(body);
                self.visit_node(condition);
                None
            }
            NodeKind::Switch(cond, body) => {
                self.visit_node(cond);
                self.visit_node(body);
                None
            }
            NodeKind::Case(expr, stmt) => {
                self.visit_node(expr);
                self.visit_node(stmt);
                None
            }
            NodeKind::CaseRange(start, end, stmt) => {
                self.visit_node(start);
                self.visit_node(end);
                self.visit_node(stmt);
                None
            }
            NodeKind::Default(stmt) => {
                self.visit_node(stmt);
                None
            }
            NodeKind::Return(expr) => {
                self.visit_return_statement(&expr, node.span);
                None
            }
            NodeKind::ExpressionStatement(expr) => {
                if let Some(expr_ref) = expr {
                    self.visit_node(expr_ref);
                }
                None
            }
            NodeKind::StaticAssert(cond, _) => {
                self.visit_node(cond);
                None
            }
            NodeKind::EnumConstant(_, value_expr) => {
                if let Some(expr) = value_expr {
                    self.visit_node(expr);
                }
                Some(QualType::unqualified(self.type_ctx.type_int))
            }
            // Literals
            NodeKind::LiteralInt(_) => Some(QualType::unqualified(self.type_ctx.type_int)),
            NodeKind::LiteralFloat(_) => Some(QualType::unqualified(self.type_ctx.type_double)),
            NodeKind::LiteralChar(_) => Some(QualType::unqualified(self.type_ctx.type_char)),
            NodeKind::LiteralString(name) => {
                let char_type = self.type_ctx.type_char;
                let array_size = name.as_str().len() + 1;
                let array_type = self.type_ctx.array_of(char_type, ArraySizeType::Constant(array_size));
                Some(QualType::unqualified(array_type))
            }
            // Expressions
            NodeKind::Ident(_, symbol_ref) => {
                let symbol = self.symbol_table.get_symbol(symbol_ref.get().unwrap());
                Some(QualType::unqualified(symbol.type_info))
            }
            NodeKind::UnaryOp(op, operand) => self.visit_unary_op(op, operand, node.span),
            NodeKind::BinaryOp(op, lhs, rhs) => self.visit_binary_op(op, lhs, rhs),
            NodeKind::TernaryOp(cond, then, else_expr) => {
                self.visit_node(cond);
                let then_ty = self.visit_node(then);
                self.visit_node(else_expr);
                then_ty // A simplification, should implement ternary conversions
            }
            NodeKind::GnuStatementExpression(stmt, _) => {
                // The type of a statement expression is the type of the last expression.
                if let NodeKind::CompoundStatement(nodes) = &self.ast.get_node(stmt).kind {
                    self.visit_node(stmt);
                    if let Some(last_node) = nodes.last() {
                        if let NodeKind::ExpressionStatement(Some(expr)) = self.ast.get_node(*last_node).kind.clone() {
                            return self.visit_node(expr);
                        }
                    }
                }
                None
            }
            NodeKind::PostIncrement(expr) | NodeKind::PostDecrement(expr) => {
                let ty = self.visit_node(expr);
                if !self.is_lvalue(expr) {
                    self.report_error(SemanticError::NotAnLvalue { span: node.span });
                }
                ty
            }
            NodeKind::Assignment(_, lhs, rhs) => self.visit_assignment(lhs, rhs, node.span),
            NodeKind::FunctionCall(func, args) => self.visit_function_call(func, &args),
            NodeKind::MemberAccess(obj, field_name, is_arrow) => self.visit_member_access(obj, field_name, is_arrow),
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(arr, idx),
            NodeKind::Cast(ty, expr) => {
                self.visit_node(expr);
                Some(ty)
            }
            NodeKind::SizeOfExpr(expr) => {
                self.visit_node(expr);
                Some(QualType::unqualified(self.type_ctx.type_long_unsigned))
            }
            NodeKind::SizeOfType(_) => Some(QualType::unqualified(self.type_ctx.type_long_unsigned)),
            NodeKind::AlignOf(_) => Some(QualType::unqualified(self.type_ctx.type_long_unsigned)),
            NodeKind::CompoundLiteral(ty, init) => {
                self.visit_node(init);
                Some(ty)
            }
            NodeKind::GenericSelection(ctrl, assocs) => {
                self.visit_node(ctrl);
                for assoc in &assocs {
                    self.visit_node(assoc.result_expr);
                }
                assocs.first().and_then(|a| self.visit_node(a.result_expr))
            }
            NodeKind::VaArg(expr, ty) => {
                self.visit_node(expr);
                Some(QualType::unqualified(ty))
            }
            NodeKind::InitializerList(inits) => {
                for init in inits {
                    for designator in &init.designation {
                        match designator {
                            Designator::ArrayIndex(expr_ref) => {
                                self.visit_node(*expr_ref);
                            }
                            Designator::GnuArrayRange(start_ref, end_ref) => {
                                self.visit_node(*start_ref);
                                self.visit_node(*end_ref);
                            }
                            Designator::FieldName(_) => {}
                        }
                    }
                    self.visit_node(init.initializer);
                }
                None
            }
            NodeKind::RecordDecl(_) | NodeKind::TypedefDecl(_) | NodeKind::FunctionDecl(_) => None,
            NodeKind::Break
            | NodeKind::Continue
            | NodeKind::Goto(_, _)
            | NodeKind::Label(_, _, _)
            | NodeKind::EmptyStatement => None,
            _ => {
                // For any unhandled nodes, explicitly do nothing.
                // This prevents panics for node types that don't need type resolution.
                None
            }
        };

        if let Some(ty) = result_type {
            node.resolved_type.set(Some(ty));
        }
        result_type
    }
}
