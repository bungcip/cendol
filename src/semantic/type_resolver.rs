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
}

trait SemanticVisitor {
    fn get_ast(&self) -> &Ast;
    fn get_type_ctx(&mut self) -> &mut TypeContext;
    fn visit_node(&mut self, node_ref: NodeRef) -> Option<QualType>;

    fn visit_if_statement(&mut self, stmt: &IfStmt) {
        if let Some(cond_ty) = self.visit_node(stmt.condition) {
            if !is_scalar_type(cond_ty, self.get_type_ctx()) {
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
            if !is_scalar_type(cond_ty, self.get_type_ctx()) {
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
                if !is_scalar_type(cond_ty, self.get_type_ctx()) {
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
        let ret_ty = self.get_current_function_ret_type();
        let is_void_func = ret_ty.map_or(false, |ty| self.get_type_ctx().get(ty.ty).kind == TypeKind::Void);

        if let Some(expr_ref) = expr {
            if is_void_func {
                // self.report_error(SemanticError::VoidReturnWithValue { span });
            }
            self.visit_node(*expr_ref);
        } else if !is_void_func {
            // self.report_error(SemanticError::NonVoidReturnWithoutValue { span });
        }
    }

    fn get_current_function_ret_type(&self) -> Option<QualType>;

    fn visit_unary_op(&mut self, op: UnaryOp, operand_ref: NodeRef) -> Option<QualType> {
        let operand_ty = self.visit_node(operand_ref)?;
        let operand_kind = &self.get_type_ctx().get(operand_ty.ty).kind;

        match op {
            UnaryOp::AddrOf => Some(QualType::unqualified(self.get_type_ctx().pointer_to(operand_ty.ty))),
            UnaryOp::Deref => match operand_kind {
                TypeKind::Pointer { pointee } => Some(QualType::unqualified(*pointee)),
                _ => None,
            },
            UnaryOp::Plus | UnaryOp::Minus => {
                if is_scalar_type(operand_ty, self.get_type_ctx()) {
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
        usual_arithmetic_conversions(self.get_type_ctx(), lhs_ty, rhs_ty)
    }

    fn visit_assignment(&mut self, lhs_ref: NodeRef, rhs_ref: NodeRef) -> Option<QualType> {
        let lhs_ty = self.visit_node(lhs_ref)?;
        self.visit_node(rhs_ref)?;
        Some(lhs_ty)
    }

    fn visit_function_call(&mut self, func_ref: NodeRef, args: &[NodeRef]) -> Option<QualType> {
        for arg in args {
            self.visit_node(*arg);
        }

        let func_ty = self.visit_node(func_ref).unwrap();
        let func_kind = self.get_type_ctx().get(func_ty.ty).kind.clone();

        match func_kind {
            TypeKind::Function { return_type, .. } => Some(QualType::unqualified(return_type)),
            TypeKind::Pointer { pointee } => {
                let pointee_kind = &self.get_type_ctx().get(pointee).kind;
                if let TypeKind::Function { return_type, .. } = pointee_kind {
                    Some(QualType::unqualified(*return_type))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn visit_member_access(&mut self, obj_ref: NodeRef, is_arrow: bool) -> Option<QualType> {
        let obj_ty = self.visit_node(obj_ref)?;
        let obj_kind = &self.get_type_ctx().get(obj_ty.ty).kind;

        let record_ty_ref = if is_arrow {
            if let TypeKind::Pointer { pointee } = obj_kind {
                *pointee
            } else {
                return None;
            }
        } else {
            obj_ty.ty
        };

        if let TypeKind::Record { .. } = &self.get_type_ctx().get(record_ty_ref).kind {
        } else {
            return None;
        }

        None
    }

    fn visit_index_access(&mut self, arr_ref: NodeRef, idx_ref: NodeRef) -> Option<QualType> {
        self.visit_node(idx_ref);
        let arr_ty = self.visit_node(arr_ref)?;
        let arr_kind = &self.get_type_ctx().get(arr_ty.ty).kind;

        match arr_kind {
            TypeKind::Array { element_type, .. } => Some(QualType::unqualified(*element_type)),
            TypeKind::Pointer { pointee } => Some(QualType::unqualified(*pointee)),
            _ => None,
        }
    }
}

impl<'a> SemanticVisitor for TypeResolver<'a> {
    fn get_ast(&self) -> &Ast {
        self.ast
    }

    fn get_type_ctx(&mut self) -> &mut TypeContext {
        self.type_ctx
    }

    fn get_current_function_ret_type(&self) -> Option<QualType> {
        self.current_function_ret_type
    }

    fn visit_node(&mut self, node_ref: NodeRef) -> Option<QualType> {
        let node = self.ast.get_node(node_ref);
        let result_type = match &node.kind {
            NodeKind::TranslationUnit(nodes) => {
                for child in nodes {
                    self.visit_node(*child);
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
            NodeKind::DeclarationList(nodes) => {
                for child in nodes {
                    self.visit_node(*child);
                }
                None
            }
            NodeKind::CompoundStatement(nodes) => {
                for child in nodes {
                    self.visit_node(*child);
                }
                None
            }
            NodeKind::If(stmt) => {
                self.visit_if_statement(stmt);
                None
            }
            NodeKind::While(stmt) => {
                self.visit_while_statement(stmt);
                None
            }
            NodeKind::For(stmt) => {
                self.visit_for_statement(stmt);
                None
            }
            NodeKind::Switch(cond, body) => {
                self.visit_node(*cond);
                self.visit_node(*body);
                None
            }
            NodeKind::Return(expr) => {
                self.visit_return_statement(expr, node.span);
                None
            }
            NodeKind::ExpressionStatement(expr) => {
                if let Some(expr_ref) = expr {
                    self.visit_node(*expr_ref);
                }
                None
            }
            NodeKind::LiteralInt(_) => Some(QualType::unqualified(self.type_ctx.type_int)),
            NodeKind::LiteralFloat(_) => Some(QualType::unqualified(self.type_ctx.type_double)),
            NodeKind::LiteralChar(_) => Some(QualType::unqualified(self.type_ctx.type_char)),
            NodeKind::LiteralString(name) => {
                let char_type = self.type_ctx.type_char;
                let array_size = name.as_str().len() + 1;
                let array_type = self.type_ctx.array_of(char_type, ArraySizeType::Constant(array_size));
                Some(QualType::unqualified(self.type_ctx.pointer_to(array_type)))
            }
            NodeKind::Ident(_, symbol_ref) => {
                let symbol = self.symbol_table.get_symbol(symbol_ref.get().unwrap());
                Some(QualType::unqualified(symbol.type_info))
            }
            NodeKind::UnaryOp(op, operand) => self.visit_unary_op(*op, *operand),
            NodeKind::BinaryOp(op, lhs, rhs) => self.visit_binary_op(*op, *lhs, *rhs),
            NodeKind::Assignment(_, lhs, rhs) => self.visit_assignment(*lhs, *rhs),
            NodeKind::FunctionCall(func, args) => self.visit_function_call(*func, args),
            NodeKind::MemberAccess(obj, _, is_arrow) => self.visit_member_access(*obj, *is_arrow),
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(*arr, *idx),
            NodeKind::Cast(ty, expr) => {
                self.visit_node(*expr);
                Some(*ty)
            }
            NodeKind::SizeOfExpr(expr) => {
                self.visit_node(*expr);
                Some(QualType::unqualified(self.type_ctx.type_long_unsigned))
            }
            NodeKind::SizeOfType(_) => Some(QualType::unqualified(self.type_ctx.type_long_unsigned)),
            NodeKind::AlignOf(_) => Some(QualType::unqualified(self.type_ctx.type_long_unsigned)),
            NodeKind::InitializerList(inits) => {
                for init in inits {
                    self.visit_node(init.initializer);
                }
                None
            }
            _ => None,
        };

        if let Some(ty) = result_type {
            node.resolved_type.set(Some(ty));
        }
        result_type
    }
}
