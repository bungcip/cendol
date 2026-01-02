use crate::{
    ast::{nodes::*, *},
    diagnostic::SemanticError,
    semantic::{
        ArraySizeType, ImplicitConversion, QualType, SymbolTable, TypeKind, TypeRegistry, ValueCategory,
        conversions::{integer_promotion, usual_arithmetic_conversions},
        utils::is_scalar_type,
    },
};

pub fn run_type_resolver(
    ast: &Ast,
    diag: &mut crate::diagnostic::DiagnosticEngine,
    symbol_table: &SymbolTable,
    registry: &mut TypeRegistry,
) -> crate::semantic::SemanticInfo {
    let mut semantic_info = crate::semantic::SemanticInfo::with_capacity(ast.nodes.len());
    let mut resolver = TypeResolver {
        ast,
        diag,
        symbol_table,
        registry,
        semantic_info: &mut semantic_info,
        current_function_ret_type: None,
        deferred_checks: Vec::new(),
    };
    let root = ast.get_root();
    resolver.visit_node(root);
    resolver.process_deferred_checks();
    semantic_info
}

enum DeferredCheck {
    StaticAssert(NodeRef),
}

struct TypeResolver<'a> {
    ast: &'a Ast,
    diag: &'a mut crate::diagnostic::DiagnosticEngine,
    symbol_table: &'a SymbolTable,
    registry: &'a mut TypeRegistry,
    semantic_info: &'a mut crate::semantic::SemanticInfo,
    current_function_ret_type: Option<QualType>,
    deferred_checks: Vec<DeferredCheck>,
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

    fn check_scalar_condition(&mut self, condition: NodeRef) {
        if let Some(cond_ty) = self.visit_node(condition)
            && !is_scalar_type(cond_ty, self.registry)
        {
            // report error
        }
    }

    fn visit_if_statement(&mut self, stmt: &IfStmt) {
        self.check_scalar_condition(stmt.condition);
        self.visit_node(stmt.then_branch);
        if let Some(else_branch) = stmt.else_branch {
            self.visit_node(else_branch);
        }
    }

    fn visit_while_statement(&mut self, stmt: &WhileStmt) {
        self.check_scalar_condition(stmt.condition);
        self.visit_node(stmt.body);
    }

    fn visit_for_statement(&mut self, stmt: &ForStmt) {
        if let Some(init) = stmt.init {
            self.visit_node(init);
        }
        if let Some(cond) = stmt.condition {
            self.check_scalar_condition(cond);
        }
        if let Some(inc) = stmt.increment {
            self.visit_node(inc);
        }
        self.visit_node(stmt.body);
    }

    fn visit_return_statement(&mut self, expr: &Option<NodeRef>, _span: SourceSpan) {
        let ret_ty = self.current_function_ret_type;
        let is_void_func = ret_ty.is_some_and(|ty| self.registry.get(ty.ty).kind == TypeKind::Void);

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
        let operand_kind = &self.registry.get(operand_ty.ty).kind;

        match op {
            UnaryOp::AddrOf => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span: full_span });
                    return None;
                }
                // If operand is array/function, record pointer decay conversion
                match &self.registry.get(operand_ty.ty).kind {
                    TypeKind::Array { .. } | TypeKind::Function { .. } => {
                        let idx = (operand_ref.get() - 1) as usize;
                        self.semantic_info.conversions[idx].push(ImplicitConversion::PointerDecay);
                    }
                    _ => {}
                }
                Some(self.registry.decay(operand_ty))
            }
            UnaryOp::Deref => match operand_kind {
                TypeKind::Pointer { pointee } => Some(QualType::unqualified(*pointee)),
                _ => None,
            },
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span: full_span });
                }
                if is_scalar_type(operand_ty, self.registry) {
                    Some(operand_ty)
                } else {
                    None
                }
            }
            UnaryOp::Plus | UnaryOp::Minus => {
                if is_scalar_type(operand_ty, self.registry) {
                    // Strip all qualifiers for unary plus/minus operations
                    let stripped = self.registry.strip_all(operand_ty);
                    if stripped.qualifiers != operand_ty.qualifiers {
                        let idx = (operand_ref.get() - 1) as usize;
                        self.semantic_info.conversions[idx].push(ImplicitConversion::QualifierAdjust {
                            from: operand_ty.qualifiers,
                            to: stripped.qualifiers,
                        });
                    }
                    Some(stripped)
                } else {
                    None
                }
            }
            UnaryOp::LogicNot => {
                // Logical NOT always returns bool type
                Some(QualType::unqualified(self.registry.type_bool))
            }
            _ => None,
        }
    }

    fn apply_and_record_integer_promotion(&mut self, node_ref: NodeRef, ty: QualType) -> QualType {
        let promoted = integer_promotion(self.registry, ty);
        if promoted.ty != ty.ty {
            let idx = (node_ref.get() - 1) as usize;
            self.semantic_info.conversions[idx].push(ImplicitConversion::IntegerPromotion {
                from: ty.ty,
                to: promoted.ty,
            });
        }
        promoted
    }

    fn visit_binary_op(&mut self, op: BinaryOp, lhs_ref: NodeRef, rhs_ref: NodeRef) -> Option<QualType> {
        let lhs_ty = self.visit_node(lhs_ref)?;
        let rhs_ty = self.visit_node(rhs_ref)?;

        // Perform integer promotions and record them
        let _lhs_promoted = self.apply_and_record_integer_promotion(lhs_ref, lhs_ty);
        let _rhs_promoted = self.apply_and_record_integer_promotion(rhs_ref, rhs_ty);

        // Handle pointer arithmetic
        // Re-borrow kinds after mutable borrows above
        let lhs_kind = &self.registry.get(lhs_ty.ty).kind;
        let rhs_kind = &self.registry.get(rhs_ty.ty).kind;

        match (op, lhs_kind, rhs_kind) {
            // Pointer + integer = pointer
            (BinaryOp::Add, TypeKind::Pointer { pointee }, TypeKind::Int { .. }) => {
                Some(QualType::unqualified(*pointee))
            }
            (BinaryOp::Add, TypeKind::Int { .. }, TypeKind::Pointer { pointee }) => {
                Some(QualType::unqualified(*pointee))
            }

            // Pointer - integer = pointer
            (BinaryOp::Sub, TypeKind::Pointer { pointee }, TypeKind::Int { .. }) => {
                Some(QualType::unqualified(*pointee))
            }

            // Pointer - pointer = integer (ptrdiff_t)
            (BinaryOp::Sub, TypeKind::Pointer { .. }, TypeKind::Pointer { .. }) => {
                Some(QualType::unqualified(self.registry.type_int))
            }

            // For other operations, use usual arithmetic conversions
            _ => usual_arithmetic_conversions(self.registry, lhs_ty, rhs_ty),
        }
    }

    fn visit_assignment(&mut self, lhs_ref: NodeRef, rhs_ref: NodeRef, full_span: SourceSpan) -> Option<QualType> {
        let lhs_ty = self.visit_node(lhs_ref)?;
        let rhs_result = self.visit_node(rhs_ref)?;

        if !self.is_lvalue(lhs_ref) {
            self.report_error(SemanticError::NotAnLvalue { span: full_span });
        }
        // Record potential implicit conversions from rhs -> lhs
        let lhs_kind = &self.registry.get(lhs_ty.ty).kind;
        let rhs_kind = &self.registry.get(rhs_result.ty).kind;

        // Array-to-pointer decay: array assigned to pointer
        if let (TypeKind::Pointer { .. }, TypeKind::Array { .. }) = (lhs_kind, rhs_kind) {
            let idx = (rhs_ref.get() - 1) as usize;
            self.semantic_info.conversions[idx].push(ImplicitConversion::PointerDecay);
        }

        // Qualifier adjustment: same canonical type but different qualifiers
        if lhs_ty.ty == rhs_result.ty && lhs_ty.qualifiers != rhs_result.qualifiers {
            let idx = (rhs_ref.get() - 1) as usize;
            self.semantic_info.conversions[idx].push(ImplicitConversion::QualifierAdjust {
                from: rhs_result.qualifiers,
                to: lhs_ty.qualifiers,
            });
        }

        // Integer casts
        match (lhs_kind, rhs_kind) {
            (
                TypeKind::Char { .. } | TypeKind::Short { .. } | TypeKind::Int { .. } | TypeKind::Long { .. },
                TypeKind::Char { .. } | TypeKind::Short { .. } | TypeKind::Int { .. } | TypeKind::Long { .. },
            ) => {
                if lhs_ty.ty != rhs_result.ty {
                    let idx = (rhs_ref.get() - 1) as usize;
                    self.semantic_info.conversions[idx].push(ImplicitConversion::IntegerCast {
                        from: rhs_result.ty,
                        to: lhs_ty.ty,
                    });
                }
            }
            // Pointer casts
            (TypeKind::Pointer { .. }, TypeKind::Pointer { .. }) => {
                if lhs_ty.ty != rhs_result.ty {
                    let idx = (rhs_ref.get() - 1) as usize;
                    self.semantic_info.conversions[idx].push(ImplicitConversion::PointerCast {
                        from: rhs_result.ty,
                        to: lhs_ty.ty,
                    });
                }
            }
            _ => {}
        }

        Some(lhs_ty)
    }

    fn visit_function_call(&mut self, func_ref: NodeRef, args: &[NodeRef]) -> Option<QualType> {
        for arg in args {
            self.visit_node(*arg);
        }

        let func_ty = self.visit_node(func_ref).unwrap();
        let func_kind = self.registry.get(func_ty.ty).kind.clone();

        match func_kind {
            TypeKind::Function { return_type, .. } => Some(QualType::unqualified(return_type)),
            TypeKind::Pointer { pointee } => {
                let pointee_kind = &self.registry.get(pointee).kind;
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
        let obj_kind = &self.registry.get(obj_ty.ty).kind;

        let record_ty_ref = if is_arrow {
            if let TypeKind::Pointer { pointee } = obj_kind {
                *pointee
            } else {
                return None; // Error: arrow access on non-pointer
            }
        } else {
            obj_ty.ty
        };

        // Ensure layout is computed for the record type
        let _ = self.registry.ensure_layout(record_ty_ref);

        if let TypeKind::Record { members, .. } = &self.registry.get(record_ty_ref).kind {
            // Find the member
            if let Some(member) = members.iter().find(|m| m.name == Some(field_name)) {
                return Some(member.member_type);
            }
        }

        None // Error: field not found or not a struct/union
    }

    fn visit_index_access(&mut self, arr_ref: NodeRef, idx_ref: NodeRef) -> Option<QualType> {
        self.visit_node(idx_ref);
        let arr_ty = self.visit_node(arr_ref)?;
        let arr_kind = self.registry.get(arr_ty.ty).kind.clone();

        match arr_kind {
            TypeKind::Array { element_type, .. } => {
                // Ensure layout is computed for array type
                let _ = self.registry.ensure_layout(arr_ty.ty);
                Some(QualType::unqualified(element_type))
            }
            TypeKind::Pointer { pointee } => Some(QualType::unqualified(pointee)),
            _ => None,
        }
    }

    fn visit_declaration_node(&mut self, _node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        match kind {
            NodeKind::TranslationUnit(nodes) => {
                for child in nodes {
                    self.visit_node(*child);
                }
                None
            }
            NodeKind::Function(data) => {
                let func_ty = self.registry.get(data.ty);
                if let TypeKind::Function { return_type, .. } = func_ty.kind.clone() {
                    self.current_function_ret_type = Some(QualType::unqualified(return_type));
                };
                self.visit_node(data.body);
                self.current_function_ret_type = None;
                None
            }
            NodeKind::VarDecl(data) => {
                let _ = self.registry.ensure_layout(data.ty.ty);
                if let Some(init) = data.init {
                    self.visit_node(init);
                }
                Some(data.ty)
            }
            NodeKind::DeclarationList(nodes) => {
                for child in nodes {
                    self.visit_node(*child);
                }
                None
            }
            NodeKind::EnumConstant(_, value_expr) => {
                if let Some(expr) = value_expr {
                    self.visit_node(*expr);
                }
                Some(QualType::unqualified(self.registry.type_int))
            }
            NodeKind::RecordDecl(_) | NodeKind::TypedefDecl(_) => None,
            NodeKind::FunctionDecl(data) => {
                let func_type = self.registry.get(data.ty).kind.clone();
                if let TypeKind::Function { parameters, .. } = func_type {
                    for param in parameters {
                        let _ = self.registry.ensure_layout(param.param_type.ty);
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn visit_statement_node(&mut self, node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        let node = self.ast.get_node(node_ref); // For span access if needed
        match kind {
            NodeKind::CompoundStatement(nodes) => {
                for child in nodes {
                    self.visit_node(*child);
                }
                self.process_deferred_checks();
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
            NodeKind::DoWhile(body, condition) => {
                self.visit_node(*body);
                self.visit_node(*condition);
                None
            }
            NodeKind::Switch(cond, body) => {
                self.visit_node(*cond);
                self.visit_node(*body);
                None
            }
            NodeKind::Case(expr, stmt) => {
                self.visit_node(*expr);
                self.visit_node(*stmt);
                None
            }
            NodeKind::CaseRange(start, end, stmt) => {
                self.visit_node(*start);
                self.visit_node(*end);
                self.visit_node(*stmt);
                None
            }
            NodeKind::Default(stmt) => {
                self.visit_node(*stmt);
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
            NodeKind::StaticAssert(..) => {
                self.deferred_checks.push(DeferredCheck::StaticAssert(node_ref));
                None
            }
            NodeKind::Break | NodeKind::Continue | NodeKind::Goto(_, _) | NodeKind::EmptyStatement => None,
            NodeKind::Label(_, stmt, _) => {
                self.visit_node(*stmt);
                None
            }
            _ => None,
        }
    }

    fn visit_expression_node(&mut self, node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        let node = self.ast.get_node(node_ref);
        match kind {
            NodeKind::LiteralInt(_) => Some(QualType::unqualified(self.registry.type_int)),
            NodeKind::LiteralFloat(_) => Some(QualType::unqualified(self.registry.type_double)),
            NodeKind::LiteralChar(_) => Some(QualType::unqualified(self.registry.type_char)),
            NodeKind::LiteralString(name) => {
                let char_type = self.registry.type_char;
                let array_size = name.as_str().len() + 1;
                let array_type = self.registry.array_of(char_type, ArraySizeType::Constant(array_size));
                let _ = self.registry.ensure_layout(array_type);
                Some(QualType::unqualified(array_type))
            }
            NodeKind::Ident(_, symbol_ref) => {
                let symbol = self.symbol_table.get_symbol(symbol_ref.get().unwrap());
                match &symbol.kind {
                    crate::semantic::SymbolKind::EnumConstant { .. } => {
                        Some(QualType::unqualified(self.registry.type_int))
                    }
                    _ => Some(QualType::unqualified(symbol.type_info)),
                }
            }
            NodeKind::UnaryOp(op, operand) => self.visit_unary_op(*op, *operand, node.span),
            NodeKind::BinaryOp(op, lhs, rhs) => self.visit_binary_op(*op, *lhs, *rhs),
            NodeKind::TernaryOp(cond, then, else_expr) => {
                self.visit_node(*cond);
                let then_ty = self.visit_node(*then);
                self.visit_node(*else_expr);
                then_ty
            }
            NodeKind::GnuStatementExpression(stmt, _) => {
                if let NodeKind::CompoundStatement(nodes) = &self.ast.get_node(*stmt).kind {
                    self.visit_node(*stmt);
                    if let Some(last_node) = nodes.last()
                        && let NodeKind::ExpressionStatement(Some(expr)) = self.ast.get_node(*last_node).kind.clone()
                    {
                        return self.visit_node(expr);
                    }
                }
                None
            }
            NodeKind::PostIncrement(expr) | NodeKind::PostDecrement(expr) => {
                let ty = self.visit_node(*expr);
                if !self.is_lvalue(*expr) {
                    self.report_error(SemanticError::NotAnLvalue { span: node.span });
                }
                ty
            }
            NodeKind::Assignment(_, lhs, rhs) => self.visit_assignment(*lhs, *rhs, node.span),
            NodeKind::FunctionCall(func, args) => self.visit_function_call(*func, args),
            NodeKind::MemberAccess(obj, field_name, is_arrow) => self.visit_member_access(*obj, *field_name, *is_arrow),
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(*arr, *idx),
            NodeKind::Cast(ty, expr) => {
                self.visit_node(*expr);
                Some(*ty)
            }
            NodeKind::SizeOfExpr(expr) => {
                self.visit_node(*expr);
                Some(QualType::unqualified(self.registry.type_long_unsigned))
            }
            NodeKind::SizeOfType(ty) => {
                let _ = self.registry.ensure_layout(ty.ty);
                Some(QualType::unqualified(self.registry.type_long_unsigned))
            }
            NodeKind::AlignOf(_) => Some(QualType::unqualified(self.registry.type_long_unsigned)),
            NodeKind::CompoundLiteral(ty, init) => {
                let _ = self.registry.ensure_layout(ty.ty);
                self.visit_node(*init);
                Some(*ty)
            }
            NodeKind::GenericSelection(ctrl, assocs) => self.visit_generic_selection(*ctrl, assocs),
            NodeKind::VaArg(expr, ty) => {
                self.visit_node(*expr);
                Some(QualType::unqualified(*ty))
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
            _ => None,
        }
    }

    fn visit_node(&mut self, node_ref: NodeRef) -> Option<QualType> {
        let node = self.ast.get_node(node_ref);
        let result_type = match &node.kind {
            // Declarations
            NodeKind::TranslationUnit(_) |
            NodeKind::Function(_) |
            NodeKind::VarDecl(_) |
            NodeKind::DeclarationList(_) |
            NodeKind::RecordDecl(_) |
            NodeKind::TypedefDecl(_) |
            NodeKind::EnumConstant(..) |
            NodeKind::FunctionDecl(_) => self.visit_declaration_node(node_ref, &node.kind),

            // Statements
            NodeKind::CompoundStatement(_) |
            NodeKind::If(_) |
            NodeKind::While(_) |
            NodeKind::DoWhile(..) |
            NodeKind::For(_) |
            NodeKind::Return(_) |
            NodeKind::ExpressionStatement(_) |
            NodeKind::StaticAssert(..) |
            NodeKind::Switch(..) |
            NodeKind::Case(..) |
            NodeKind::CaseRange(..) |
            NodeKind::Default(_) |
            NodeKind::Break |
            NodeKind::Continue |
            NodeKind::Goto(..) |
            NodeKind::Label(..) |
            NodeKind::EmptyStatement => self.visit_statement_node(node_ref, &node.kind),

            // Expressions (Catch-all)
            _ => self.visit_expression_node(node_ref, &node.kind),
        };

        // Debug: log certain nodes
        if node_ref.get() == 27 {
            eprintln!("type_resolver: node {} result_type={:?}", node_ref.get(), result_type);
        }

        if let Some(ty) = result_type {
            // set resolved type and value category for this node
            let idx = (node_ref.get() - 1) as usize;
            self.semantic_info.types[idx] = Some(ty);
            let vc = if self.is_lvalue(node_ref) {
                ValueCategory::LValue
            } else {
                ValueCategory::RValue
            };
            self.semantic_info.value_categories[idx] = vc;
        }
        result_type
    }

    fn process_deferred_checks(&mut self) {
        for check in self.deferred_checks.drain(..).collect::<Vec<_>>() {
            match check {
                DeferredCheck::StaticAssert(node_ref) => self.visit_static_assert(node_ref),
            }
        }
    }

    fn visit_static_assert(&mut self, node_ref: NodeRef) {
        let node = self.ast.get_node(node_ref);
        if let NodeKind::StaticAssert(cond, msg) = node.kind.clone() {
            self.visit_node(cond);
            let ctx = crate::semantic::const_eval::ConstEvalCtx { ast: self.ast };
            match crate::semantic::const_eval::eval_const_expr(&ctx, cond) {
                Some(0) => {
                    self.report_error(SemanticError::StaticAssertFailed {
                        message: msg.as_str().to_string(),
                        span: node.span,
                    });
                }
                None => {
                    self.report_error(SemanticError::StaticAssertNotConstant { span: node.span });
                }
                _ => {}
            }
        }
    }

    fn visit_generic_selection(
        &mut self,
        ctrl_ref: NodeRef,
        assocs: &[ResolvedGenericAssociation],
    ) -> Option<QualType> {
        // First, visit the controlling expression to determine its type.
        let ctrl_ty = self.visit_node(ctrl_ref)?;

        // It's crucial to visit *all* result expressions to ensure they are
        // fully type-checked, even if they are not the selected branch.
        // This resolves all identifier types within them.
        for assoc in assocs {
            self.visit_node(assoc.result_expr);
        }

        // Now, find the selected expression based on type compatibility.
        let mut selected_expr_ref = None;
        for assoc in assocs {
            if let Some(assoc_ty) = assoc.ty {
                // This is a type association.
                if self.registry.is_compatible(ctrl_ty, assoc_ty) {
                    selected_expr_ref = Some(assoc.result_expr);
                    break;
                }
            } else {
                // This is the 'default' association.
                selected_expr_ref = Some(assoc.result_expr);
                break;
            }
        }

        // The type of the _Generic expression is the type of the selected result expression.
        if let Some(expr_ref) = selected_expr_ref {
            // The type should already be resolved from the earlier pass.
            let idx = (expr_ref.get() - 1) as usize;
            self.semantic_info.types.get(idx).and_then(|t| *t)
        } else {
            // If no match is found and there's no default, it's a semantic error.
            self.report_error(SemanticError::GenericNoMatch {
                span: self.ast.get_node(ctrl_ref).span,
            });
            None
        }
    }
}
