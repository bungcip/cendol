use crate::{
    ast::{nodes::*, *},
    diagnostic::{DiagnosticEngine, SemanticError},
    semantic::{
        ArraySizeType, QualType, SymbolKind, SymbolTable, TypeKind, TypeQualifiers, TypeRef, TypeRegistry,
        conversions::{integer_promotion, usual_arithmetic_conversions},
    },
};

use smallvec::SmallVec;

/// Side table containing semantic information for AST nodes.
/// Parallel vectors indexed by node index (NodeRef.index()).
#[derive(Debug, Clone)]
pub struct SemanticInfo {
    pub types: Vec<Option<QualType>>,
    pub conversions: Vec<SmallVec<[ImplicitConversion; 1]>>,
    pub value_categories: Vec<ValueCategory>,
}

impl SemanticInfo {
    pub fn with_capacity(n: usize) -> Self {
        use smallvec::SmallVec;
        Self {
            types: vec![None; n],
            conversions: vec![SmallVec::new(); n],
            value_categories: vec![ValueCategory::RValue; n],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueCategory {
    LValue,
    RValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplicitConversion {
    /// LValue → RValue
    LValueToRValue,

    /// Array/function → pointer
    PointerDecay,

    /// char/short → int (store types as TypeRef)
    IntegerPromotion { from: TypeRef, to: TypeRef },

    /// int → long, unsigned → unsigned long, etc
    IntegerCast { from: TypeRef, to: TypeRef },

    /// void* ↔ T*
    PointerCast { from: TypeRef, to: TypeRef },

    /// add/remove const/volatile
    QualifierAdjust { from: TypeQualifiers, to: TypeQualifiers },

    /// 0 / NULL → T*
    NullPointerConstant,
}

/// Run Semantic Analyzer in our AST and return analysist result in SemanticInfo
/// which contains resolved type, conversion table, and value category
pub(crate) fn run_semantic_analyzer(
    ast: &Ast,
    diag: &mut DiagnosticEngine,
    symbol_table: &SymbolTable,
    registry: &mut TypeRegistry,
) -> SemanticInfo {
    let mut semantic_info = SemanticInfo::with_capacity(ast.kinds.len());
    let mut resolver = SemanticAnalyzer {
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

struct SemanticAnalyzer<'a> {
    ast: &'a Ast,
    diag: &'a mut DiagnosticEngine,
    symbol_table: &'a SymbolTable,
    registry: &'a mut TypeRegistry,
    semantic_info: &'a mut SemanticInfo,
    current_function_ret_type: Option<QualType>,
    deferred_checks: Vec<DeferredCheck>,
}

impl<'a> SemanticAnalyzer<'a> {
    fn report_error(&mut self, error: SemanticError) {
        self.diag.report(error);
    }

    fn is_lvalue(&self, node_ref: NodeRef) -> bool {
        let node_kind = self.ast.get_kind(node_ref);
        match node_kind {
            NodeKind::Ident(_, symbol_ref) => {
                let symbol = self.symbol_table.get_symbol(*symbol_ref);
                matches!(symbol.kind, SymbolKind::Variable { .. } | SymbolKind::Function)
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
            && !cond_ty.is_scalar()
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
        let is_void_func = ret_ty.is_some_and(|ty| ty.is_void());

        if let Some(expr_ref) = expr {
            if is_void_func {
                // self.report_error(SemanticError::VoidReturnWithValue { span });
            }
            if let Some(expr_ty) = self.visit_node(*expr_ref)
                && let Some(target_ty) = ret_ty
            {
                self.record_implicit_conversions(target_ty, expr_ty, *expr_ref);
            }
        } else if !is_void_func {
            // self.report_error(SemanticError::NonVoidReturnWithoutValue { span });
        }
    }

    fn visit_unary_op(&mut self, op: UnaryOp, operand_ref: NodeRef, full_span: SourceSpan) -> Option<QualType> {
        let operand_ty = self.visit_node(operand_ref)?;
        // let operand_kind = &self.registry.get(operand_ty.ty()).kind;

        match op {
            UnaryOp::AddrOf => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span: full_span });
                    return None;
                }
                if operand_ty.is_array() || operand_ty.is_function() {
                    self.semantic_info.conversions[operand_ref.index()].push(ImplicitConversion::PointerDecay);
                    return Some(self.registry.decay(operand_ty));
                }
                Some(QualType::unqualified(self.registry.pointer_to(operand_ty.ty())))
            }
            UnaryOp::Deref => {
                let mut actual_ty = operand_ty;
                if operand_ty.is_array() || operand_ty.is_function() {
                    self.semantic_info.conversions[operand_ref.index()].push(ImplicitConversion::PointerDecay);
                    actual_ty = self.registry.decay(operand_ty);
                }

                if actual_ty.is_pointer() {
                    match &self.registry.get(actual_ty.ty()).kind {
                        TypeKind::Pointer { pointee } => Some(QualType::unqualified(*pointee)),
                        _ => unreachable!("is_pointer() is true but kind is not Pointer"),
                    }
                } else {
                    None
                }
            }
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span: full_span });
                }
                if operand_ty.is_scalar() { Some(operand_ty) } else { None }
            }
            UnaryOp::Plus | UnaryOp::Minus => {
                if operand_ty.is_scalar() {
                    // Strip all qualifiers for unary plus/minus operations
                    let stripped = self.registry.strip_all(operand_ty);
                    if stripped.qualifiers() != operand_ty.qualifiers() {
                        self.semantic_info.conversions[operand_ref.index()].push(ImplicitConversion::QualifierAdjust {
                            from: operand_ty.qualifiers(),
                            to: stripped.qualifiers(),
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
            UnaryOp::BitNot => {
                if operand_ty.is_integer() {
                    Some(self.apply_and_record_integer_promotion(operand_ref, operand_ty))
                } else {
                    let type_kind = &self.registry.get(operand_ty.ty()).kind;
                    self.report_error(SemanticError::InvalidUnaryOperand {
                        ty: type_kind.to_string(),
                        span: full_span,
                    });
                    None
                }
            }
        }
    }

    fn apply_and_record_integer_promotion(&mut self, node_ref: NodeRef, ty: QualType) -> QualType {
        let promoted = integer_promotion(self.registry, ty);
        if promoted.ty() != ty.ty() {
            let idx = node_ref.index();
            self.semantic_info.conversions[idx].push(ImplicitConversion::IntegerPromotion {
                from: ty.ty(),
                to: promoted.ty(),
            });
        }
        promoted
    }

    fn visit_binary_op(
        &mut self,
        op: BinaryOp,
        lhs_ref: NodeRef,
        rhs_ref: NodeRef,
        full_span: SourceSpan,
    ) -> Option<QualType> {
        debug_assert!(
            !op.is_assignment(),
            "visit_binary_op called with assignment operator: {:?}",
            op
        );
        let lhs_ty = self.visit_node(lhs_ref)?;
        let rhs_ty = self.visit_node(rhs_ref)?;

        // Perform integer promotions and record them
        let lhs_promoted = self.apply_and_record_integer_promotion(lhs_ref, lhs_ty);
        let rhs_promoted = self.apply_and_record_integer_promotion(rhs_ref, rhs_ty);

        if op == BinaryOp::Mod && (!lhs_promoted.is_integer() || !rhs_promoted.is_integer()) {
            let lhs_kind = &self.registry.get(lhs_promoted.ty()).kind;
            let rhs_kind = &self.registry.get(rhs_promoted.ty()).kind;
            self.report_error(SemanticError::InvalidBinaryOperands {
                left_ty: lhs_kind.to_string(),
                right_ty: rhs_kind.to_string(),
                span: full_span,
            });
            return None;
        }

        // Handle pointer arithmetic
        // Re-borrow kinds after mutable borrows above
        // let lhs_kind = &self.registry.get(lhs_promoted.ty()).kind;
        // let rhs_kind = &self.registry.get(rhs_promoted.ty()).kind;

        let (result_ty, common_ty) = match op {
            // Pointer + integer = pointer
            BinaryOp::Add if lhs_promoted.is_pointer() && rhs_promoted.is_integer() => (lhs_promoted, lhs_promoted),
            BinaryOp::Add if lhs_promoted.is_integer() && rhs_promoted.is_pointer() => (rhs_promoted, rhs_promoted),

            // Pointer - integer = pointer
            BinaryOp::Sub if lhs_promoted.is_pointer() && rhs_promoted.is_integer() => (lhs_promoted, lhs_promoted),

            // Pointer - pointer = integer (ptrdiff_t)
            BinaryOp::Sub if lhs_promoted.is_pointer() && rhs_promoted.is_pointer() => {
                (QualType::unqualified(self.registry.type_int), lhs_promoted)
            }

            // Pointer/Integer comparisons
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual => {
                let common = if lhs_promoted.is_pointer() {
                    lhs_promoted
                } else if rhs_promoted.is_pointer() {
                    rhs_promoted
                } else {
                    usual_arithmetic_conversions(self.registry, lhs_promoted, rhs_promoted)?
                };
                (QualType::unqualified(self.registry.type_int), common)
            }

            // Logical operations
            BinaryOp::LogicAnd | BinaryOp::LogicOr => (QualType::unqualified(self.registry.type_bool), lhs_promoted),

            // For other operations, use usual arithmetic conversions
            _ => {
                let ty = usual_arithmetic_conversions(self.registry, lhs_promoted, rhs_promoted)?;
                (ty, ty)
            }
        };

        // For arithmetic/comparison operations, operands should be converted to a common type.
        let lhs_kind = self.ast.get_kind(lhs_ref);
        let rhs_kind = self.ast.get_kind(rhs_ref);

        let is_literal = |kind: &NodeKind| {
            matches!(
                kind,
                NodeKind::LiteralInt(_) | NodeKind::LiteralChar(_) | NodeKind::LiteralFloat(_)
            )
        };

        if lhs_promoted.ty() != common_ty.ty() || is_literal(lhs_kind) {
            let idx = lhs_ref.index();
            self.semantic_info.conversions[idx].push(ImplicitConversion::IntegerCast {
                from: lhs_promoted.ty(),
                to: common_ty.ty(),
            });
        }
        if rhs_promoted.ty() != common_ty.ty() || is_literal(rhs_kind) {
            let idx = rhs_ref.index();
            self.semantic_info.conversions[idx].push(ImplicitConversion::IntegerCast {
                from: rhs_promoted.ty(),
                to: common_ty.ty(),
            });
        }

        Some(result_ty)
    }

    fn visit_assignment(
        &mut self,
        op: BinaryOp,
        lhs_ref: NodeRef,
        rhs_ref: NodeRef,
        full_span: SourceSpan,
    ) -> Option<QualType> {
        debug_assert!(
            op.is_assignment(),
            "visit_assignment called with non-assignment operator: {:?}",
            op
        );

        let lhs_ty = self.visit_node(lhs_ref)?;
        let rhs_ty = self.visit_node(rhs_ref)?;

        if !self.is_lvalue(lhs_ref) {
            self.report_error(SemanticError::NotAnLvalue { span: full_span });
        }

        self.record_implicit_conversions(lhs_ty, rhs_ty, rhs_ref);

        Some(lhs_ty)
    }

    fn record_implicit_conversions(&mut self, lhs_ty: QualType, rhs_ty: QualType, rhs_ref: NodeRef) {
        // Array-to-pointer decay
        if lhs_ty.is_pointer() && rhs_ty.is_array() {
            let idx = rhs_ref.index();
            self.semantic_info.conversions[idx].push(ImplicitConversion::PointerDecay);
        }

        // Qualifier adjustment
        if lhs_ty.ty() == rhs_ty.ty() && lhs_ty.qualifiers() != rhs_ty.qualifiers() {
            let idx = rhs_ref.index();
            self.semantic_info.conversions[idx].push(ImplicitConversion::QualifierAdjust {
                from: rhs_ty.qualifiers(),
                to: lhs_ty.qualifiers(),
            });
        }

        // Integer casts
        let is_literal = matches!(
            self.ast.get_kind(rhs_ref),
            NodeKind::LiteralInt(_) | NodeKind::LiteralChar(_) | NodeKind::LiteralFloat(_)
        );

        if ((lhs_ty.is_arithmetic() && rhs_ty.is_arithmetic()) || (lhs_ty.is_pointer() && rhs_ty.is_pointer()))
            && (lhs_ty.ty() != rhs_ty.ty() || is_literal)
        {
            // For pointers, it's pointer cast. For arithmetic, integer/float cast.
            // We can distinguish if needed, but ImplicitConversion::IntegerCast naming might be misleading for floats.
            // However, check if PointerCast is distinct.
            if lhs_ty.is_pointer() && rhs_ty.is_pointer() {
                let idx = rhs_ref.index();
                self.semantic_info.conversions[idx].push(ImplicitConversion::PointerCast {
                    from: rhs_ty.ty(),
                    to: lhs_ty.ty(),
                });
            } else if lhs_ty.is_arithmetic() && rhs_ty.is_arithmetic() {
                let idx = rhs_ref.index();
                self.semantic_info.conversions[idx].push(ImplicitConversion::IntegerCast {
                    from: rhs_ty.ty(),
                    to: lhs_ty.ty(),
                });
            }
        }
    }

    fn visit_function_call(&mut self, call_expr: &crate::ast::nodes::CallExpr) -> Option<QualType> {
        let func_ty = self.visit_node(call_expr.callee)?;

        let func_ty_ref = func_ty.ty();
        // Resolve function type (might be pointer to function)
        let actual_func_ty_ref = if func_ty.is_pointer() {
            // Check if it's pointer to function
            match &self.registry.get(func_ty_ref).kind {
                TypeKind::Pointer { pointee } => *pointee,
                _ => func_ty_ref,
            }
        } else {
            func_ty_ref
        };

        // Get function kind
        let func_kind = self.registry.get(actual_func_ty_ref).kind.clone();

        if let TypeKind::Function {
            parameters,
            is_variadic: _,
            ..
        } = &func_kind
        {
            for (i, arg_node_ref) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
                // Visit the argument expression directly
                let arg_ty = self.visit_node(arg_node_ref);

                if i < parameters.len() {
                    let param_ty = parameters[i].param_type;
                    if let Some(actual_arg_ty) = arg_ty {
                        // Record implicit conversion on the argument node
                        self.record_implicit_conversions(param_ty, actual_arg_ty, arg_node_ref);
                    }
                }
            }
        } else {
            for arg_node_ref in call_expr.arg_start.range(call_expr.arg_len) {
                self.visit_node(arg_node_ref);
            }
        }

        match func_kind {
            TypeKind::Function { return_type, .. } => Some(QualType::unqualified(return_type)),
            // The pointer logic was already handled by resolving to actual_func_ty_ref above?
            // Wait, the original code returned `return_type` if `func_kind` was `Function`,
            // or checked `pointee` if `func_kind` was `Pointer`.
            // But I resolved `actual_func_ty_ref` to be the Function type.
            // So `func_kind` is the Function kind (or something else if invalid).
            _ => None,
        }
    }

    fn visit_member_access(&mut self, obj_ref: NodeRef, field_name: NameId, is_arrow: bool) -> Option<QualType> {
        let obj_ty = self.visit_node(obj_ref)?;

        let record_ty_ref = if is_arrow {
            if obj_ty.is_pointer() {
                match &self.registry.get(obj_ty.ty()).kind {
                    TypeKind::Pointer { pointee } => *pointee,
                    _ => return None,
                }
            } else {
                return None; // Error: arrow access on non-pointer
            }
        } else {
            obj_ty.ty()
        };

        // Ensure layout is computed for the record type
        let _ = self.registry.ensure_layout(record_ty_ref);

        // Recursive helper to find member (handling anonymous structs/unions)
        fn find_member(registry: &TypeRegistry, record_ty: crate::semantic::TypeRef, name: NameId) -> Option<QualType> {
            if !record_ty.is_record() {
                return None;
            }

            if let TypeKind::Record { members, .. } = &registry.get(record_ty).kind {
                // 1. Check direct members
                if let Some(member) = members.iter().find(|m| m.name == Some(name)) {
                    return Some(member.member_type);
                }

                // 2. Check anonymous members
                for member in members {
                    if member.name.is_none() {
                        let member_ty = member.member_type.ty();
                        if member_ty.is_record()
                            && let Some(found_ty) = find_member(registry, member_ty, name)
                        {
                            return Some(found_ty);
                        }
                    }
                }
            }
            None
        }

        if let Some(ty) = find_member(self.registry, record_ty_ref, field_name) {
            return Some(ty);
        }

        None // Error: field not found or not a struct/union
    }

    fn visit_index_access(&mut self, arr_ref: NodeRef, idx_ref: NodeRef) -> Option<QualType> {
        self.visit_node(idx_ref);
        let arr_ty = self.visit_node(arr_ref)?;

        if arr_ty.is_array() {
            // Ensure layout is computed for array type
            let _ = self.registry.ensure_layout(arr_ty.ty());
            match &self.registry.get(arr_ty.ty()).kind {
                TypeKind::Array { element_type, .. } => Some(QualType::unqualified(*element_type)),
                _ => unreachable!(),
            }
        } else if arr_ty.is_pointer() {
            match &self.registry.get(arr_ty.ty()).kind {
                TypeKind::Pointer { pointee } => Some(QualType::unqualified(*pointee)),
                _ => unreachable!(),
            }
        } else {
            None
        }
    }

    fn visit_declaration_node(&mut self, _node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        match kind {
            NodeKind::TranslationUnit(tu_data) => {
                for decl_ref in tu_data.decl_start.range(tu_data.decl_len) {
                    self.visit_node(decl_ref);
                }
                None
            }
            NodeKind::Function(data) => {
                let func_ty = self.registry.get(data.ty);
                if let TypeKind::Function { return_type, .. } = func_ty.kind.clone() {
                    self.current_function_ret_type = Some(QualType::unqualified(return_type));
                };

                for param_ref in data.param_start.range(data.param_len) {
                    self.visit_node(param_ref);
                }

                self.visit_node(data.body);
                self.current_function_ret_type = None;
                None
            }
            NodeKind::Param(_) => None,
            NodeKind::VarDecl(data) => {
                let _ = self.registry.ensure_layout(data.ty.ty());
                if let Some(init_ref) = data.init {
                    if let Some(init_ty) = self.visit_node(init_ref) {
                        self.record_implicit_conversions(data.ty, init_ty, init_ref);
                    } else if let NodeKind::InitializerList(_) = self.ast.get_kind(init_ref) {
                        // For InitializerList, it doesn't have an inherent type, but in a VarDecl
                        // we can treat it as having the target type for MIR lowering.
                        self.semantic_info.types[init_ref.index()] = Some(data.ty);
                    }
                }
                Some(data.ty)
            }
            NodeKind::EnumConstant(_, value_expr) => {
                if let Some(expr) = value_expr {
                    self.visit_node(*expr);
                }
                Some(QualType::unqualified(self.registry.type_int))
            }
            NodeKind::RecordDecl(_)
            | NodeKind::FieldDecl(_)
            | NodeKind::EnumDecl(_)
            | NodeKind::EnumMember(_)
            | NodeKind::TypedefDecl(_) => None,
            NodeKind::FunctionDecl(data) => {
                let func_type = self.registry.get(data.ty).kind.clone();
                if let TypeKind::Function { parameters, .. } = func_type {
                    for param in parameters {
                        let _ = self.registry.ensure_layout(param.param_type.ty());
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn visit_statement_node(&mut self, node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        // let node = self.ast.get_node(node_ref); // For span access if needed
        match kind {
            NodeKind::CompoundStatement(cs) => {
                for item_ref in cs.stmt_start.range(cs.stmt_len) {
                    self.visit_node(item_ref);
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
                let span = self.ast.get_span(node_ref);
                self.visit_return_statement(expr, span);
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
            NodeKind::Break | NodeKind::Continue | NodeKind::Goto(_, _) => None,
            NodeKind::Label(_, stmt, _) => {
                self.visit_node(*stmt);
                None
            }
            _ => None,
        }
    }

    fn visit_expression_node(&mut self, node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        // let node = self.ast.get_node(node_ref);
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
                let symbol = self.symbol_table.get_symbol(*symbol_ref);
                match &symbol.kind {
                    SymbolKind::EnumConstant { .. } => Some(QualType::unqualified(self.registry.type_int)),
                    _ => Some(QualType::unqualified(symbol.type_info)),
                }
            }
            NodeKind::UnaryOp(op, operand) => {
                let span = self.ast.get_span(node_ref);
                self.visit_unary_op(*op, *operand, span)
            }
            NodeKind::BinaryOp(op, lhs, rhs) => {
                let span = self.ast.get_span(node_ref);
                self.visit_binary_op(*op, *lhs, *rhs, span)
            }
            NodeKind::TernaryOp(cond, then, else_expr) => {
                self.visit_node(*cond);
                let then_ty = self.visit_node(*then);
                let else_ty = self.visit_node(*else_expr);
                if let (Some(t), Some(e)) = (then_ty, else_ty) {
                    usual_arithmetic_conversions(self.registry, t, e)
                } else {
                    None
                }
            }
            NodeKind::GnuStatementExpression(stmt, _) => {
                if let NodeKind::CompoundStatement(cs) = self.ast.get_kind(*stmt) {
                    self.visit_node(*stmt);
                    if cs.stmt_len > 0 {
                        let last_item_idx = cs.stmt_start.get() + (cs.stmt_len - 1) as u32;
                        let last_item_ref = NodeRef::new(last_item_idx).unwrap();
                        if let NodeKind::ExpressionStatement(Some(expr)) = self.ast.get_kind(last_item_ref).clone() {
                            return self.visit_node(expr);
                        }
                    }
                }
                None
            }
            NodeKind::PostIncrement(expr) | NodeKind::PostDecrement(expr) => {
                let ty = self.visit_node(*expr);
                if !self.is_lvalue(*expr) {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::NotAnLvalue { span });
                }
                ty
            }
            NodeKind::Assignment(op, lhs, rhs) => {
                let span = self.ast.get_span(node_ref);
                self.visit_assignment(*op, *lhs, *rhs, span)
            }
            NodeKind::FunctionCall(call_expr) => self.visit_function_call(call_expr),
            NodeKind::MemberAccess(obj, field_name, is_arrow) => self.visit_member_access(*obj, *field_name, *is_arrow),
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(*arr, *idx),
            NodeKind::Cast(ty, expr) => {
                self.visit_node(*expr);
                Some(*ty)
            }
            NodeKind::SizeOfExpr(expr) => {
                if let Some(ty) = self.visit_node(*expr)
                    && !self.registry.is_complete(ty.ty())
                {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::SizeOfIncompleteType { ty: ty.ty(), span });
                }
                Some(QualType::unqualified(self.registry.type_long_unsigned))
            }
            NodeKind::SizeOfType(ty) | NodeKind::AlignOf(ty) => {
                if !self.registry.is_complete(ty.ty()) {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::SizeOfIncompleteType { ty: ty.ty(), span });
                }
                Some(QualType::unqualified(self.registry.type_long_unsigned))
            }
            NodeKind::CompoundLiteral(ty, init) => {
                let _ = self.registry.ensure_layout(ty.ty());
                self.visit_node(*init);
                Some(*ty)
            }
            NodeKind::GenericSelection(gs) => self.visit_generic_selection(gs),
            NodeKind::GenericAssociation(ga) => self.visit_node(ga.result_expr),
            NodeKind::VaArg(expr, ty) => {
                self.visit_node(*expr);
                Some(QualType::unqualified(*ty))
            }
            NodeKind::InitializerList(list) => {
                for item_ref in list.init_start.range(list.init_len) {
                    self.visit_node(item_ref);
                }
                None
            }
            NodeKind::InitializerItem(init) => {
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
                None
            }
            _ => None,
        }
    }

    fn visit_node(&mut self, node_ref: NodeRef) -> Option<QualType> {
        let node_kind = self.ast.get_kind(node_ref);
        let result_type = match node_kind {
            // Declarations
            NodeKind::TranslationUnit(_)
            | NodeKind::Function(_)
            | NodeKind::VarDecl(_)
            | NodeKind::RecordDecl(_)
            | NodeKind::FieldDecl(_)
            | NodeKind::EnumDecl(_)
            | NodeKind::EnumMember(_)
            | NodeKind::TypedefDecl(_)
            | NodeKind::EnumConstant(..)
            | NodeKind::Param(_)
            | NodeKind::FunctionDecl(_) => self.visit_declaration_node(node_ref, node_kind),

            // Statements
            NodeKind::CompoundStatement(_)
            | NodeKind::If(_)
            | NodeKind::While(_)
            | NodeKind::DoWhile(..)
            | NodeKind::For(_)
            | NodeKind::Return(_)
            | NodeKind::ExpressionStatement(_)
            | NodeKind::StaticAssert(..)
            | NodeKind::Switch(..)
            | NodeKind::Case(..)
            | NodeKind::CaseRange(..)
            | NodeKind::Default(_)
            | NodeKind::Break
            | NodeKind::Continue
            | NodeKind::Goto(..)
            | NodeKind::Label(..) => self.visit_statement_node(node_ref, node_kind),

            // Expressions (Catch-all)
            _ => self.visit_expression_node(node_ref, node_kind),
        };

        if let Some(ty) = result_type {
            // set resolved type and value category for this node
            let idx = node_ref.index();
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
        let node_kind = self.ast.get_kind(node_ref).clone();
        if let NodeKind::StaticAssert(cond, msg) = node_kind {
            self.visit_node(cond);
            let ctx = crate::semantic::const_eval::ConstEvalCtx { ast: self.ast };
            match crate::semantic::const_eval::eval_const_expr(&ctx, cond) {
                Some(0) => {
                    self.report_error(SemanticError::StaticAssertFailed {
                        message: msg.as_str().to_string(),
                        span: self.ast.get_span(node_ref),
                    });
                }
                None => {
                    self.report_error(SemanticError::StaticAssertNotConstant {
                        span: self.ast.get_span(node_ref),
                    });
                }
                _ => {}
            }
        }
    }

    fn visit_generic_selection(&mut self, gs: &GenericSelectionData) -> Option<QualType> {
        // First, visit the controlling expression to determine its type.
        let ctrl_ty = self.visit_node(gs.control)?;

        // C11 6.5.1.1p3: The controlling expression of a generic selection is not evaluated.
        // C11 6.5.1.1p2: The type name in a generic association specifies a type compatible with the
        // controlling expression's type, after removing any top-level qualifiers.
        let unqualified_ctrl_ty = self.registry.strip_all(ctrl_ty);

        // It's crucial to visit *all* result expressions to ensure they are
        // fully type-checked, even if they are not the selected branch.
        // This resolves all identifier types within them.
        let mut selected_expr_ref = None;
        let mut default_expr_ref = None;

        for assoc_node_ref in gs.assoc_start.range(gs.assoc_len) {
            if let NodeKind::GenericAssociation(ga) = self.ast.get_kind(assoc_node_ref).clone() {
                self.visit_node(assoc_node_ref);

                if let Some(assoc_ty) = ga.ty {
                    // This is a type association.
                    if self.registry.is_compatible(unqualified_ctrl_ty, assoc_ty) {
                        selected_expr_ref = Some(ga.result_expr);
                    }
                } else {
                    // This is the 'default' association.
                    default_expr_ref = Some(ga.result_expr);
                }
            }
        }

        // If no specific type matches, use the default association if it exists.
        if selected_expr_ref.is_none() {
            selected_expr_ref = default_expr_ref;
        }

        // The type of the _Generic expression is the type of the selected result expression.
        if let Some(expr_ref) = selected_expr_ref {
            // The type should already be resolved from the earlier pass.
            let idx = expr_ref.index();
            self.semantic_info.types.get(idx).and_then(|t| *t)
        } else {
            // If no match is found and there's no default, it's a semantic error.
            self.report_error(SemanticError::GenericNoMatch {
                span: self.ast.get_span(gs.control),
            });
            None
        }
    }
}
