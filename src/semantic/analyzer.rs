use crate::{
    ast::{nodes::*, *},
    diagnostic::{DiagnosticEngine, SemanticError},
    semantic::{
        ArraySizeType, QualType, StructMember, SymbolKind, SymbolTable, TypeKind, TypeQualifiers, TypeRef,
        TypeRegistry,
        conversions::{integer_promotion, usual_arithmetic_conversions},
    },
};

use smallvec::SmallVec;
use std::collections::HashSet;

/// Side table containing semantic information for AST nodes.
/// Parallel vectors indexed by node index (NodeRef.index()).
#[derive(Debug, Clone)]
pub struct SemanticInfo {
    pub types: Vec<Option<QualType>>,
    pub conversions: Vec<SmallVec<[ImplicitConversion; 1]>>,
    pub value_categories: Vec<ValueCategory>,
}

impl SemanticInfo {
    pub(crate) fn with_capacity(n: usize) -> Self {
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
    PointerDecay { to: TypeRef },

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
        current_function_name: None,
        current_function_is_noreturn: false,
        deferred_checks: Vec::new(),
        switch_depth: 0,
        switch_cases: Vec::new(),
        switch_default_seen: Vec::new(),
        checked_types: HashSet::new(),
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
    current_function_name: Option<String>,
    current_function_is_noreturn: bool,
    deferred_checks: Vec<DeferredCheck>,
    switch_depth: usize,
    switch_cases: Vec<HashSet<i64>>,
    switch_default_seen: Vec<bool>,
    checked_types: HashSet<TypeRef>,
}

impl<'a> SemanticAnalyzer<'a> {
    fn report_error(&mut self, error: SemanticError) {
        self.diag.report(error);
    }

    /// Recursively visit type to find any expressions (e.g. VLA sizes) and resolve them.
    fn visit_type_expressions(&mut self, qt: QualType) {
        let ty = qt.ty();
        if self.checked_types.contains(&ty) {
            return;
        }
        self.checked_types.insert(ty);

        // To avoid infinite recursion on recursive types (e.g. struct A { struct A *next; }),
        // we rely on checked_types.
        // Note: We need to clone the kind to avoid borrowing self.registry while calling self methods
        let kind = self.registry.get(ty).kind.clone();

        match kind {
            TypeKind::Array { element_type, size } => {
                if let ArraySizeType::Variable(expr) = size {
                    self.visit_node(expr);
                }
                self.visit_type_expressions(QualType::unqualified(element_type));
            }
            TypeKind::Pointer { pointee } => {
                self.visit_type_expressions(pointee);
            }
            TypeKind::Function {
                return_type,
                parameters,
                ..
            } => {
                self.visit_type_expressions(QualType::unqualified(return_type));
                for param in parameters {
                    self.visit_type_expressions(param.param_type);
                }
            }
            TypeKind::Complex { base_type } => {
                self.visit_type_expressions(QualType::unqualified(base_type));
            }
            // For Records and Enums, we don't need to traverse members because
            // they cannot contain VLAs (C11 6.7.2.1).
            // Even if they did, the members would be visited during their declaration processing.
            _ => {}
        }
    }

    fn can_fall_through(&self, node_ref: NodeRef) -> bool {
        match self.ast.get_kind(node_ref) {
            NodeKind::Return(_) | NodeKind::Break | NodeKind::Continue | NodeKind::Goto(_, _) => false,
            NodeKind::If(if_stmt) => {
                let then_ft = self.can_fall_through(if_stmt.then_branch);
                let else_ft = if_stmt.else_branch.is_none_or(|e| self.can_fall_through(e));
                then_ft || else_ft
            }
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                if let NodeKind::FunctionCall(call) = self.ast.get_kind(*expr_ref)
                    && let Some(callee_type) = self.semantic_info.types[call.callee.index()]
                    && let TypeKind::Function { is_noreturn, .. } = &self.registry.get(callee_type.ty()).kind
                {
                    return !*is_noreturn;
                }
                true
            }
            NodeKind::While(_) => {
                // While loop can only be exited via break, so it can fall through.
                true
            }
            NodeKind::For(for_stmt) => {
                // A for loop without a condition is infinite unless there's a break.
                for_stmt.condition.is_some()
            }
            NodeKind::CompoundStatement(cs) => {
                if cs.stmt_len > 0 {
                    let last_item_idx = cs.stmt_start.get() + (cs.stmt_len - 1) as u32;
                    let last_item_ref = NodeRef::new(last_item_idx).unwrap();
                    self.can_fall_through(last_item_ref)
                } else {
                    true
                }
            }
            _ => true,
        }
    }

    fn is_lvalue(&self, node_ref: NodeRef) -> bool {
        let node_kind = self.ast.get_kind(node_ref);
        match node_kind {
            NodeKind::Ident(_, symbol_ref) => {
                let symbol = self.symbol_table.get_symbol(*symbol_ref);
                matches!(symbol.kind, SymbolKind::Variable { .. } | SymbolKind::Function { .. })
            }
            NodeKind::UnaryOp(op, _) => matches!(*op, UnaryOp::Deref),
            NodeKind::IndexAccess(..) => true,
            NodeKind::MemberAccess(obj_ref, _, is_arrow) => *is_arrow || self.is_lvalue(*obj_ref),
            NodeKind::LiteralString(..) => true,
            NodeKind::CompoundLiteral(..) => true,
            _ => false,
        }
    }

    fn is_null_pointer_constant(&self, node_ref: NodeRef) -> bool {
        let node_kind = self.ast.get_kind(node_ref);
        match node_kind {
            NodeKind::LiteralInt(0) => true,
            NodeKind::Cast(ty, inner) if ty.ty() == self.registry.type_void_ptr => {
                self.is_null_pointer_constant(*inner)
            }
            _ => false,
        }
    }

    /// Checks if the node is an LValue and is not const-qualified.
    /// Reports errors if check fails.
    fn check_lvalue_and_modifiable(&mut self, node_ref: NodeRef, ty: QualType, span: SourceSpan) -> bool {
        if !self.is_lvalue(node_ref) {
            self.report_error(SemanticError::NotAnLvalue { span });
            false
        } else if self.registry.is_const_recursive(ty) {
            self.report_error(SemanticError::AssignmentToReadOnly { span });
            false
        } else {
            true
        }
    }

    /// Validates assignment constraints and records implicit conversions.
    /// Returns true if assignment is valid, false otherwise.
    fn validate_and_record_assignment(
        &mut self,
        lhs_ty: QualType,
        rhs_ty: QualType,
        rhs_ref: NodeRef,
        span: SourceSpan,
    ) -> bool {
        if self.check_assignment_constraints(lhs_ty, rhs_ty, rhs_ref) {
            self.record_implicit_conversions(lhs_ty, rhs_ty, rhs_ref);
            true
        } else {
            let lhs_kind = &self.registry.get(lhs_ty.ty()).kind;
            let rhs_kind = &self.registry.get(rhs_ty.ty()).kind;
            self.report_error(SemanticError::TypeMismatch {
                expected: lhs_kind.to_string(),
                found: rhs_kind.to_string(),
                span,
            });
            false
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
        if self.current_function_is_noreturn {
            self.report_error(SemanticError::NoreturnFunctionReturns {
                name: self.current_function_name.clone().unwrap(),
                span: _span,
            });
        }

        let ret_ty = self.current_function_ret_type;
        let is_void_func = ret_ty.is_some_and(|ty| ty.is_void());
        let func_name = self
            .current_function_name
            .clone()
            .unwrap_or_else(|| "<unknown>".to_string());

        if let Some(expr_ref) = expr {
            if is_void_func {
                let err_span = self.ast.get_span(*expr_ref);
                self.report_error(SemanticError::VoidReturnWithValue {
                    name: func_name.clone(),
                    span: err_span,
                });
            }
            if let Some(expr_ty) = self.visit_node(*expr_ref)
                && let Some(target_ty) = ret_ty
            {
                self.record_implicit_conversions(target_ty, expr_ty, *expr_ref);
            }
        } else if !is_void_func {
            self.report_error(SemanticError::NonVoidReturnWithoutValue {
                name: func_name,
                span: _span,
            });
        }
    }

    fn visit_unary_op(&mut self, op: UnaryOp, operand_ref: NodeRef, full_span: SourceSpan) -> Option<QualType> {
        let operand_ty = self.visit_node(operand_ref)?;

        match op {
            UnaryOp::AddrOf => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span: full_span });
                    return None;
                }
                if operand_ty.is_array() || operand_ty.is_function() {
                    let decayed = self.registry.decay(operand_ty, TypeQualifiers::empty());
                    self.semantic_info.conversions[operand_ref.index()]
                        .push(ImplicitConversion::PointerDecay { to: decayed.ty() });
                    return Some(decayed);
                }
                Some(QualType::unqualified(self.registry.pointer_to(operand_ty)))
            }
            UnaryOp::Deref => {
                let actual_ty = if operand_ty.is_array() || operand_ty.is_function() {
                    let decayed = self.registry.decay(operand_ty, TypeQualifiers::empty());
                    self.semantic_info.conversions[operand_ref.index()]
                        .push(ImplicitConversion::PointerDecay { to: decayed.ty() });
                    decayed
                } else {
                    operand_ty
                };

                if actual_ty.is_pointer() {
                    self.registry.get_pointee(actual_ty.ty())
                } else {
                    None
                }
            }
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                self.check_lvalue_and_modifiable(operand_ref, operand_ty, full_span);
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

    fn analyze_binary_operation_types(
        &mut self,
        op: BinaryOp,
        lhs_promoted: QualType,
        rhs_promoted: QualType,
        full_span: SourceSpan,
    ) -> Option<(QualType, QualType)> {
        match op {
            // Pointer + integer = pointer
            BinaryOp::Add if lhs_promoted.is_pointer() && rhs_promoted.is_integer() => {
                Some((lhs_promoted, lhs_promoted))
            }
            BinaryOp::Add if lhs_promoted.is_integer() && rhs_promoted.is_pointer() => {
                Some((rhs_promoted, rhs_promoted))
            }

            // Pointer - integer = pointer
            BinaryOp::Sub if lhs_promoted.is_pointer() && rhs_promoted.is_integer() => {
                Some((lhs_promoted, lhs_promoted))
            }

            // Pointer - pointer = integer (ptrdiff_t)
            BinaryOp::Sub if lhs_promoted.is_pointer() && rhs_promoted.is_pointer() => {
                Some((QualType::unqualified(self.registry.type_int), lhs_promoted))
            }

            // Pointer/Integer comparisons
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual => {
                let common = if lhs_promoted.is_pointer() && rhs_promoted.is_pointer() {
                    let lhs_base = self.registry.get_pointee(lhs_promoted.ty()).unwrap();
                    let rhs_base = self.registry.get_pointee(rhs_promoted.ty()).unwrap();

                    if lhs_base.ty() == self.registry.type_void || rhs_base.ty() == self.registry.type_void {
                        QualType::unqualified(self.registry.type_void_ptr)
                    } else if lhs_base == rhs_base {
                        lhs_promoted
                    } else {
                        let lhs_str = self.registry.display_type(lhs_promoted.ty());
                        let rhs_str = self.registry.display_type(rhs_promoted.ty());
                        self.report_error(SemanticError::IncompatiblePointerComparison {
                            lhs: lhs_str,
                            rhs: rhs_str,
                            span: full_span,
                        });
                        lhs_promoted
                    }
                } else if lhs_promoted.is_pointer() {
                    lhs_promoted
                } else if rhs_promoted.is_pointer() {
                    rhs_promoted
                } else {
                    usual_arithmetic_conversions(self.registry, lhs_promoted, rhs_promoted)?
                };
                Some((QualType::unqualified(self.registry.type_int), common))
            }

            // Logical operations
            BinaryOp::LogicAnd | BinaryOp::LogicOr => {
                Some((QualType::unqualified(self.registry.type_bool), lhs_promoted))
            }

            // For other operations, use usual arithmetic conversions
            _ => {
                let ty = usual_arithmetic_conversions(self.registry, lhs_promoted, rhs_promoted)?;
                Some((ty, ty))
            }
        }
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

        let (result_ty, common_ty) = self.analyze_binary_operation_types(op, lhs_promoted, rhs_promoted, full_span)?;

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
        node_ref: NodeRef,
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

        if !self.check_lvalue_and_modifiable(lhs_ref, lhs_ty, full_span) {
            return None;
        }

        // For compound assignments like +=, we need to check if the underlying arithmetic is valid.
        let (effective_rhs_ty, final_assignment_cast_target) = if let Some(arithmetic_op) = op.without_assignment() {
            // Reuse visit_binary_op logic conceptually, but for compound assignment operands.
            // For p += 1, LHS is pointer, RHS is integer.
            let lhs_promoted = self.apply_and_record_integer_promotion(lhs_ref, lhs_ty);
            let rhs_promoted = self.apply_and_record_integer_promotion(rhs_ref, rhs_ty);

            if let Some((_, common_ty)) =
                self.analyze_binary_operation_types(arithmetic_op, lhs_promoted, rhs_promoted, full_span)
            {
                // Record conversions from promoted operands to the common type.
                // This is what the binary operation will actually work with.
                if lhs_promoted.ty() != common_ty.ty() {
                    self.semantic_info.conversions[lhs_ref.index()].push(ImplicitConversion::IntegerCast {
                        from: lhs_promoted.ty(),
                        to: common_ty.ty(),
                    });
                }
                if rhs_promoted.ty() != common_ty.ty() {
                    self.semantic_info.conversions[rhs_ref.index()].push(ImplicitConversion::IntegerCast {
                        from: rhs_promoted.ty(),
                        to: common_ty.ty(),
                    });
                }

                // For compound assignment, the result of (lhs op rhs) is converted back to lhs type.
                // We record this conversion on the assignment node itself.
                (common_ty, Some(lhs_ty))
            } else {
                let lhs_kind = &self.registry.get(lhs_promoted.ty()).kind;
                let rhs_kind = &self.registry.get(rhs_promoted.ty()).kind;
                self.report_error(SemanticError::InvalidBinaryOperands {
                    left_ty: lhs_kind.to_string(),
                    right_ty: rhs_kind.to_string(),
                    span: full_span,
                });
                return None;
            }
        } else {
            (rhs_ty, None)
        };

        // For compound assignment, we record the final cast on the assignment node.
        if let Some(target_ty) = final_assignment_cast_target {
            // Check assignment constraints (C11 6.5.16.1)
            if !self.check_assignment_constraints(lhs_ty, effective_rhs_ty, rhs_ref) {
                let lhs_kind = &self.registry.get(lhs_ty.ty()).kind;
                let rhs_kind = &self.registry.get(effective_rhs_ty.ty()).kind;

                self.report_error(SemanticError::TypeMismatch {
                    expected: lhs_kind.to_string(),
                    found: rhs_kind.to_string(),
                    span: full_span,
                });
                return None;
            }

            if target_ty.ty() != effective_rhs_ty.ty() {
                self.semantic_info.conversions[node_ref.index()].push(ImplicitConversion::IntegerCast {
                    from: effective_rhs_ty.ty(),
                    to: target_ty.ty(),
                });
            }
        } else {
            // Simple assignment
            if !self.validate_and_record_assignment(lhs_ty, effective_rhs_ty, rhs_ref, full_span) {
                return None;
            }
        }

        Some(lhs_ty)
    }

    fn check_assignment_constraints(&self, lhs_ty: QualType, rhs_ty: QualType, rhs_ref: NodeRef) -> bool {
        // 1. Arithmetic types
        if lhs_ty.is_arithmetic() && rhs_ty.is_arithmetic() {
            return true;
        }

        // 2. Structure or Union types
        if lhs_ty.is_record() || rhs_ty.is_record() {
            return lhs_ty.is_record() && rhs_ty.is_record() && lhs_ty.ty() == rhs_ty.ty();
        }

        // 3. Pointers
        if lhs_ty.is_pointer() {
            if self.is_null_pointer_constant(rhs_ref) {
                return true;
            }

            // Resolve implicit decay for RHS to check compatibility
            let rhs_pointer_base = if rhs_ty.is_array() {
                match &self.registry.get(rhs_ty.ty()).kind {
                    TypeKind::Array { element_type, .. } => Some(*element_type),
                    _ => None,
                }
            } else if rhs_ty.is_function() {
                Some(rhs_ty.ty()) // Function decays to pointer
            } else if rhs_ty.is_pointer() {
                self.registry.get_pointee(rhs_ty.ty()).map(|qt| qt.ty())
            } else {
                None
            };

            if let Some(rhs_base) = rhs_pointer_base {
                // Check compatibility
                let lhs_base = self.registry.get_pointee(lhs_ty.ty()).unwrap();

                // void* wildcard
                if lhs_base.ty() == self.registry.type_void || rhs_base == self.registry.type_void {
                    return true;
                }

                return lhs_base.ty() == rhs_base;
            }

            return false;
        }

        // 4. _Bool = Pointer
        if lhs_ty.ty() == self.registry.type_bool && (rhs_ty.is_pointer() || rhs_ty.is_array() || rhs_ty.is_function())
        {
            return true;
        }

        false
    }

    fn record_implicit_conversions(&mut self, lhs_ty: QualType, rhs_ty: QualType, rhs_ref: NodeRef) {
        let idx = rhs_ref.index();
        let mut current_rhs_ty = rhs_ty;

        // Null pointer constant conversion (0 or (void*)0 -> T*)
        if lhs_ty.is_pointer() && self.is_null_pointer_constant(rhs_ref) {
            self.semantic_info.conversions[idx].push(ImplicitConversion::NullPointerConstant);
            // If it's still not the same type, we might need a PointerCast after NullPointerConstant desugaring?
            // Actually NullPointerConstant desugars to (T*)0 in many cases.
            if lhs_ty.ty() != self.registry.type_void_ptr {
                self.semantic_info.conversions[idx].push(ImplicitConversion::PointerCast {
                    from: self.registry.type_void_ptr,
                    to: lhs_ty.ty(),
                });
            }
            return;
        }

        // Array/Function-to-pointer decay
        if lhs_ty.is_pointer() && (current_rhs_ty.is_array() || current_rhs_ty.is_function()) {
            let decayed = self.registry.decay(current_rhs_ty, TypeQualifiers::empty());
            self.semantic_info.conversions[idx].push(ImplicitConversion::PointerDecay { to: decayed.ty() });
            current_rhs_ty = decayed; // Update current type for subsequent checks
        }

        // Qualifier adjustment
        if lhs_ty.ty() == current_rhs_ty.ty() && lhs_ty.qualifiers() != current_rhs_ty.qualifiers() {
            self.semantic_info.conversions[idx].push(ImplicitConversion::QualifierAdjust {
                from: current_rhs_ty.qualifiers(),
                to: lhs_ty.qualifiers(),
            });
        }

        // Integer casts
        let is_literal = matches!(
            self.ast.get_kind(rhs_ref),
            NodeKind::LiteralInt(_) | NodeKind::LiteralChar(_) | NodeKind::LiteralFloat(_)
        );

        if ((lhs_ty.is_arithmetic() && current_rhs_ty.is_arithmetic())
            || (lhs_ty.is_pointer() && current_rhs_ty.is_pointer()))
            && (lhs_ty.ty() != current_rhs_ty.ty() || is_literal)
        {
            // For pointers, it's pointer cast. For arithmetic, integer/float cast.
            if lhs_ty.is_pointer() && current_rhs_ty.is_pointer() {
                self.semantic_info.conversions[idx].push(ImplicitConversion::PointerCast {
                    from: current_rhs_ty.ty(),
                    to: lhs_ty.ty(),
                });
            } else if lhs_ty.is_arithmetic() && current_rhs_ty.is_arithmetic() {
                self.semantic_info.conversions[idx].push(ImplicitConversion::IntegerCast {
                    from: current_rhs_ty.ty(),
                    to: lhs_ty.ty(),
                });
            }
        }
    }

    fn check_assignment_and_record(&mut self, target_ty: QualType, init_ty: QualType, init_ref: NodeRef) {
        if !self.check_assignment_constraints(target_ty, init_ty, init_ref) {
            let lhs_kind = &self.registry.get(target_ty.ty()).kind;
            let rhs_kind = &self.registry.get(init_ty.ty()).kind;
            let span = self.ast.get_span(init_ref);

            self.report_error(SemanticError::TypeMismatch {
                expected: lhs_kind.to_string(),
                found: rhs_kind.to_string(),
                span,
            });
        } else {
            self.record_implicit_conversions(target_ty, init_ty, init_ref);
        }
    }

    fn check_initializer(&mut self, init_ref: NodeRef, target_ty: QualType) {
        let node_kind = self.ast.get_kind(init_ref);
        match node_kind {
            NodeKind::InitializerList(list) => {
                self.semantic_info.types[init_ref.index()] = Some(target_ty);
                let list = *list; // Clone to avoid borrow check issues
                self.check_initializer_list(&list, target_ty);
            }
            NodeKind::LiteralString(_) => {
                // Visit to resolve type
                if let Some(init_ty) = self.visit_node(init_ref) {
                    // Check if array string init
                    let is_array_string_init = target_ty.is_array() && init_ty.is_array();
                    if is_array_string_init {
                        // Check element compatibility
                        let lhs_elem = match &self.registry.get(target_ty.ty()).kind {
                            TypeKind::Array { element_type, .. } => *element_type,
                            _ => unreachable!(),
                        };
                        let is_char_type = lhs_elem == self.registry.type_char
                            || lhs_elem == self.registry.type_schar
                            || lhs_elem == self.registry.type_char_unsigned;

                        if is_char_type {
                            self.record_implicit_conversions(target_ty, init_ty, init_ref);
                        } else {
                            let lhs_kind = &self.registry.get(target_ty.ty()).kind;
                            let rhs_kind = &self.registry.get(init_ty.ty()).kind;
                            let span = self.ast.get_span(init_ref);
                            self.report_error(SemanticError::TypeMismatch {
                                expected: lhs_kind.to_string(),
                                found: rhs_kind.to_string(),
                                span,
                            });
                        }
                    } else {
                        // Normal assignment check
                        self.check_assignment_and_record(target_ty, init_ty, init_ref);
                    }
                }
            }
            _ => {
                if let Some(init_ty) = self.visit_node(init_ref) {
                    self.check_assignment_and_record(target_ty, init_ty, init_ref);
                }
            }
        }
    }

    fn check_initializer_list(&mut self, list: &InitializerListData, target_ty: QualType) {
        if target_ty.is_scalar() {
            if list.init_len > 1 {
                let second_idx = list.init_start.get() + 1;
                let second_ref = NodeRef::new(second_idx).unwrap();
                let span = self.ast.get_span(second_ref);
                self.report_error(SemanticError::ExcessElements {
                    kind: "scalar".to_string(),
                    span,
                });
            }

            if list.init_len > 0 {
                let first_item_ref = list.init_start;
                let first_item_kind = self.ast.get_kind(first_item_ref);

                if let NodeKind::InitializerItem(item) = first_item_kind {
                    let expr = item.initializer;
                    if let Some(init_ty) = self.visit_node(expr) {
                        self.check_assignment_and_record(target_ty, init_ty, expr);
                    }
                } else if let Some(init_ty) = self.visit_node(first_item_ref) {
                    self.check_assignment_and_record(target_ty, init_ty, first_item_ref);
                }
            }

            // Visit remaining elements to resolve symbols
            if list.init_len > 1 {
                for i in 1..list.init_len {
                    let item_ref = NodeRef::new(list.init_start.get() + i as u32).unwrap();
                    let item_kind = self.ast.get_kind(item_ref);
                    if let NodeKind::InitializerItem(item) = item_kind {
                        self.visit_node(item.initializer);
                    } else {
                        self.visit_node(item_ref);
                    }
                }
            }
            return;
        }

        let target_type = self.registry.get(target_ty.ty()).clone();
        match target_type.kind {
            TypeKind::Record { .. } => {
                // Flatten members for initialization, handling anonymous structs/unions
                let mut flat_members = Vec::new();
                target_type.flatten_members(self.registry, &mut flat_members);

                for item_ref in list.init_start.range(list.init_len) {
                    self.check_initializer_item_record(item_ref, &flat_members, target_ty);
                }
            }
            _ => {
                // Fallback: just visit children to resolve symbols/types
                for item_ref in list.init_start.range(list.init_len) {
                    let kind = self.ast.get_kind(item_ref);
                    if let NodeKind::InitializerItem(init) = kind {
                        let init = *init;
                        for designator_ref in init.designator_start.range(init.designator_len) {
                            if let NodeKind::Designator(d) = self.ast.get_kind(designator_ref) {
                                match d {
                                    Designator::ArrayIndex(e) => {
                                        self.visit_node(*e);
                                    }
                                    Designator::GnuArrayRange(s, e) => {
                                        self.visit_node(*s);
                                        self.visit_node(*e);
                                    }
                                    Designator::FieldName(_) => {}
                                }
                            }
                        }
                        self.visit_node(init.initializer);
                    } else {
                        self.visit_node(item_ref);
                    }
                }
            }
        }
    }

    fn check_initializer_item_record(&mut self, item_ref: NodeRef, members: &[StructMember], record_ty: QualType) {
        let node_kind = self.ast.get_kind(item_ref);
        if let NodeKind::InitializerItem(init) = node_kind {
            // 1. Validate designators
            if init.designator_len > 0 {
                let first_des_ref = init.designator_start;
                if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(first_des_ref) {
                    // Check if member exists
                    // TODO: recursive search for anonymous members if not found directly
                    let found = members.iter().any(|m| m.name == Some(*name));

                    if !found {
                        let ty_str = self.registry.display_type(record_ty.ty());
                        let span = self.ast.get_span(first_des_ref);
                        self.report_error(SemanticError::MemberNotFound {
                            name: *name,
                            ty: ty_str,
                            span,
                        });
                    }
                }
            }

            // 2. Visit children (initializer and designators)
            for designator_ref in init.designator_start.range(init.designator_len) {
                if let NodeKind::Designator(d) = self.ast.get_kind(designator_ref) {
                    match d {
                        Designator::ArrayIndex(e) => {
                            self.visit_node(*e);
                        }
                        Designator::GnuArrayRange(s, e) => {
                            self.visit_node(*s);
                            self.visit_node(*e);
                        }
                        Designator::FieldName(_) => {}
                    }
                }
            }
            // Visit initializer value
            // Ideally we would recurse with correct member type, but for now just visit
            self.visit_node(init.initializer);
        }
    }

    fn visit_function_call(&mut self, call_expr: &crate::ast::nodes::CallExpr) -> Option<QualType> {
        let func_ty = self.visit_node(call_expr.callee)?;

        let func_ty_ref = func_ty.ty();
        // Resolve function type (might be pointer to function)
        let actual_func_ty_ref = if func_ty.is_pointer() {
            // Check if it's pointer to function
            self.registry
                .get_pointee(func_ty_ref)
                .map(|qt| qt.ty())
                .unwrap_or(func_ty_ref)
        } else {
            func_ty_ref
        };

        // Get function kind
        let func_kind = self.registry.get(actual_func_ty_ref).kind.clone();

        if let TypeKind::Function { .. } = &func_kind {
            if let TypeKind::Function {
                parameters,
                is_variadic,
                ..
            } = &func_kind
            {
                let is_variadic = *is_variadic;
                for (i, arg_node_ref) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
                    // Visit the argument expression directly
                    let arg_ty = self.visit_node(arg_node_ref);

                    if i < parameters.len() {
                        let param_ty = parameters[i].param_type;
                        if let Some(actual_arg_ty) = arg_ty {
                            // Record implicit conversion on the argument node
                            self.record_implicit_conversions(param_ty, actual_arg_ty, arg_node_ref);
                        }
                    } else if is_variadic {
                        // C11 6.5.2.2: "If the expression that denotes the called function has a type that
                        // includes a prototype, the arguments are implicitly converted, as if by assignment,
                        // to the types of the corresponding parameters... The ellipsis notation in a function
                        // prototype declarator causes argument type conversion to stop after the last declared
                        // parameter. The default argument promotions are performed on trailing arguments."
                        if let Some(mut actual_arg_ty) = arg_ty {
                            // Explicitly handle array/function decay for variadic arguments first
                            if actual_arg_ty.is_array() || actual_arg_ty.is_function() {
                                let decayed = self.registry.decay(actual_arg_ty, TypeQualifiers::empty());
                                self.semantic_info.conversions[arg_node_ref.index()]
                                    .push(ImplicitConversion::PointerDecay { to: decayed.ty() });
                                actual_arg_ty = decayed;
                            }

                            let promoted_ty =
                                crate::semantic::conversions::default_argument_promotions(self.registry, actual_arg_ty);

                            // Only record additional conversions if promotion actually changed the type
                            // (Note: record_implicit_conversions handles IntegerCast/PointerCast etc)
                            if promoted_ty.ty() != actual_arg_ty.ty() {
                                self.record_implicit_conversions(promoted_ty, actual_arg_ty, arg_node_ref);
                            }
                        }
                    }
                }
            }
        } else {
            // This is not a function or function pointer, report an error.
            let ty_str = self.registry.display_type(actual_func_ty_ref);
            let span = self.ast.get_span(call_expr.callee);
            self.report_error(SemanticError::CalledNonFunctionType { ty: ty_str, span });

            // Still visit arguments to catch other potential errors within them.
            for arg_node_ref in call_expr.arg_start.range(call_expr.arg_len) {
                self.visit_node(arg_node_ref);
            }
            return None; // Return None as the call is invalid
        }

        match func_kind {
            TypeKind::Function { return_type, .. } => Some(QualType::unqualified(return_type)),
            _ => None,
        }
    }

    fn visit_member_access(
        &mut self,
        obj_ref: NodeRef,
        field_name: NameId,
        is_arrow: bool,
        span: SourceSpan,
    ) -> Option<QualType> {
        let obj_ty = self.visit_node(obj_ref)?;

        let record_ty_ref = if is_arrow {
            self.registry.get_pointee(obj_ty.ty()).map(|qt| qt.ty())?
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

        if !record_ty_ref.is_record() {
            let ty_str = self.registry.get(record_ty_ref).kind.to_string();
            self.report_error(SemanticError::MemberAccessOnNonRecord { ty: ty_str, span });
            return None;
        }

        // Check if record is complete
        if let TypeKind::Record { is_complete: false, .. } = &self.registry.get(record_ty_ref).kind {
            let ty_str = self.registry.get(record_ty_ref).kind.to_string();
            self.report_error(SemanticError::IncompleteType { ty: ty_str, span });
            return None;
        }

        if let Some(ty) = find_member(self.registry, record_ty_ref, field_name) {
            return Some(ty);
        }

        let ty_str = self.registry.get(record_ty_ref).kind.to_string();
        self.report_error(SemanticError::MemberNotFound {
            name: field_name,
            ty: ty_str,
            span,
        });
        None
    }

    fn visit_index_access(&mut self, arr_ref: NodeRef, idx_ref: NodeRef) -> Option<QualType> {
        self.visit_node(idx_ref);
        let arr_ty = self.visit_node(arr_ref)?;

        if arr_ty.is_array() {
            // Ensure layout is computed for array type
            let _ = self.registry.ensure_layout(arr_ty.ty());
            match &self.registry.get(arr_ty.ty()).kind {
                TypeKind::Array { element_type, .. } => Some(QualType::new(*element_type, arr_ty.qualifiers())),
                _ => unreachable!(),
            }
        } else {
            self.registry.get_pointee(arr_ty.ty())
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
                let func_ty = self.registry.get(data.ty).kind.clone();
                if let TypeKind::Function { return_type, .. } = func_ty {
                    self.current_function_ret_type = Some(QualType::unqualified(return_type));
                    self.current_function_is_noreturn = data.is_noreturn;
                };

                let symbol = self.symbol_table.get_symbol(data.symbol);
                let prev_func_name = self.current_function_name.take();
                self.current_function_name = Some(symbol.name.to_string());

                for param_ref in data.param_start.range(data.param_len) {
                    self.visit_node(param_ref);
                }

                self.visit_node(data.body);

                if self.current_function_is_noreturn && self.can_fall_through(data.body) {
                    let span = self.ast.get_span(_node_ref);
                    self.report_error(SemanticError::NoreturnFunctionReturns {
                        name: self.current_function_name.clone().unwrap(),
                        span,
                    });
                }

                self.current_function_ret_type = None;
                self.current_function_name = prev_func_name;
                self.current_function_is_noreturn = false;
                None
            }
            NodeKind::Param(data) => {
                self.visit_type_expressions(data.ty);
                Some(data.ty)
            }
            NodeKind::VarDecl(data) => {
                self.visit_type_expressions(data.ty);
                let _ = self.registry.ensure_layout(data.ty.ty());
                if data.init.is_some()
                    && matches!(data.storage, Some(StorageClass::Extern))
                    && self.current_function_name.is_some()
                {
                    let span = self.ast.get_span(_node_ref);
                    self.report_error(SemanticError::InvalidInitializer { span });
                }

                if let Some(init_ref) = data.init {
                    self.check_initializer(init_ref, data.ty);
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
            | NodeKind::EnumDecl(_)
            | NodeKind::EnumMember(_) => None,
            NodeKind::FieldDecl(data) => {
                self.visit_type_expressions(data.ty);
                None
            }
            NodeKind::TypedefDecl(data) => {
                self.visit_type_expressions(data.ty);
                None
            }
            NodeKind::FunctionDecl(data) => {
                self.visit_type_expressions(QualType::unqualified(data.ty));
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
                self.switch_depth += 1;
                self.switch_cases.push(HashSet::new());
                self.switch_default_seen.push(false);
                self.visit_node(*body);
                self.switch_default_seen.pop();
                self.switch_cases.pop();
                self.switch_depth -= 1;
                None
            }
            NodeKind::Case(expr, stmt) => {
                if self.switch_depth == 0 {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::CaseNotInSwitch { span });
                } else {
                    let ctx = crate::semantic::const_eval::ConstEvalCtx {
                        ast: self.ast,
                        symbol_table: self.symbol_table,
                    };
                    if let Some(val) = crate::semantic::const_eval::eval_const_expr(&ctx, *expr) {
                        let is_duplicate = if let Some(cases) = self.switch_cases.last_mut() {
                            !cases.insert(val)
                        } else {
                            false
                        };

                        if is_duplicate {
                            let span = self.ast.get_span(node_ref);
                            self.report_error(SemanticError::DuplicateCase {
                                value: val.to_string(),
                                span,
                            });
                        }
                    }
                }
                self.visit_node(*expr);
                self.visit_node(*stmt);
                None
            }
            NodeKind::CaseRange(start, end, stmt) => {
                if self.switch_depth == 0 {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::CaseNotInSwitch { span });
                } else {
                    let ctx = crate::semantic::const_eval::ConstEvalCtx {
                        ast: self.ast,
                        symbol_table: self.symbol_table,
                    };
                    if let (Some(start_val), Some(end_val)) = (
                        crate::semantic::const_eval::eval_const_expr(&ctx, *start),
                        crate::semantic::const_eval::eval_const_expr(&ctx, *end),
                    ) {
                        let mut duplicate_val = None;
                        if let Some(cases) = self.switch_cases.last_mut() {
                            for val in start_val..=end_val {
                                if !cases.insert(val) {
                                    duplicate_val = Some(val);
                                    break;
                                }
                            }
                        }

                        if let Some(val) = duplicate_val {
                            let span = self.ast.get_span(node_ref);
                            self.report_error(SemanticError::DuplicateCase {
                                value: val.to_string(),
                                span,
                            });
                        }
                    }
                }
                self.visit_node(*start);
                self.visit_node(*end);
                self.visit_node(*stmt);
                None
            }
            NodeKind::Default(stmt) => {
                if self.switch_depth == 0 {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::CaseNotInSwitch { span });
                } else {
                    let is_duplicate = if let Some(seen) = self.switch_default_seen.last_mut() {
                        let was_seen = *seen;
                        *seen = true;
                        was_seen
                    } else {
                        false
                    };

                    if is_duplicate {
                        let span = self.ast.get_span(node_ref);
                        self.report_error(SemanticError::MultipleDefaultLabels { span });
                    }
                }
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
        match kind {
            NodeKind::LiteralInt(val) => {
                // Determine the correct type for the integer literal based on its value.
                // According to C11 6.4.4.1, the type of an integer constant is the first of the corresponding
                // list in which its value can be represented.
                // For a hexadecimal or octal constant without suffix, the list is:
                // int, unsigned int, long int, unsigned long int, long long int, unsigned long long int.
                // For decimal constant without suffix: int, long int, long long int.
                // Since we don't have the original base or suffix information here, we use a heuristic.
                // If it fits in signed int, use int.
                // If it doesn't fit in signed int, but fits in unsigned int, use unsigned int.
                // Otherwise, use long long.
                let ty = if *val >= i32::MIN as i64 && *val <= i32::MAX as i64 {
                    self.registry.type_int
                } else if *val >= 0 && *val <= u32::MAX as i64 {
                    self.registry.type_int_unsigned
                } else {
                    self.registry.type_long_long
                };
                Some(QualType::unqualified(ty))
            }
            NodeKind::LiteralFloat(_) => Some(QualType::unqualified(self.registry.type_double)),
            NodeKind::LiteralChar(_) => Some(QualType::unqualified(self.registry.type_int)),
            NodeKind::LiteralString(name) => {
                let char_type = self.registry.type_char;
                let array_size = name.as_str().len() + 1;
                let array_type = self.registry.array_of(char_type, ArraySizeType::Constant(array_size));
                let _ = self.registry.ensure_layout(array_type);
                Some(QualType::new(array_type, TypeQualifiers::CONST))
            }
            NodeKind::Ident(_, symbol_ref) => {
                let symbol = self.symbol_table.get_symbol(*symbol_ref);
                match &symbol.kind {
                    SymbolKind::EnumConstant { .. } => Some(QualType::unqualified(self.registry.type_int)),
                    _ => Some(symbol.type_info),
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
                    let result_ty = match (t, e) {
                        (t, e) if t.is_arithmetic() && e.is_arithmetic() => {
                            usual_arithmetic_conversions(self.registry, t, e)
                        }
                        (t, e) if t.ty() == e.ty() => Some(t),
                        (t, _) if t.is_pointer() && self.is_null_pointer_constant(*else_expr) => Some(t),
                        (_, e) if e.is_pointer() && self.is_null_pointer_constant(*then) => Some(e),
                        (t, e) if t.is_pointer() && e.is_pointer() => {
                            // C11 6.5.15: pointer to void and pointer to object -> pointer to void
                            if t.ty() == self.registry.type_void_ptr || e.ty() == self.registry.type_void_ptr {
                                Some(QualType::unqualified(self.registry.type_void_ptr))
                            } else {
                                // Should check compatibility, for now just use one or common
                                Some(t)
                            }
                        }
                        _ => usual_arithmetic_conversions(self.registry, t, e),
                    };

                    if let Some(res) = result_ty {
                        self.record_implicit_conversions(res, t, *then);
                        self.record_implicit_conversions(res, e, *else_expr);
                        return Some(res);
                    }
                    None
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
                if self.check_lvalue_and_modifiable(*expr, ty.unwrap(), self.ast.get_span(node_ref)) {
                    // ok
                }
                ty
            }
            NodeKind::Assignment(op, lhs, rhs) => {
                let span = self.ast.get_span(node_ref);
                self.visit_assignment(node_ref, *op, *lhs, *rhs, span)
            }
            NodeKind::FunctionCall(call_expr) => self.visit_function_call(call_expr),
            NodeKind::MemberAccess(obj, field_name, is_arrow) => {
                let span = self.ast.get_span(node_ref);
                self.visit_member_access(*obj, *field_name, *is_arrow, span)
            }
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(*arr, *idx),
            NodeKind::Cast(ty, expr) => {
                self.visit_type_expressions(*ty);
                self.visit_node(*expr);
                Some(*ty)
            }
            NodeKind::SizeOfExpr(expr) => {
                if let Some(ty) = self.visit_node(*expr) {
                    if ty.is_function() {
                        let span = self.ast.get_span(node_ref);
                        self.report_error(SemanticError::SizeOfFunctionType { span });
                    } else {
                        let type_ref = ty.ty();
                        if !self.registry.is_complete(type_ref) {
                            let span = self.ast.get_span(node_ref);
                            self.report_error(SemanticError::SizeOfIncompleteType { ty: type_ref, span });
                        } else {
                            let _ = self.registry.ensure_layout(type_ref);
                        }
                    }
                }
                Some(QualType::unqualified(self.registry.type_long_unsigned))
            }
            NodeKind::SizeOfType(ty) | NodeKind::AlignOf(ty) => {
                self.visit_type_expressions(*ty);
                let type_ref = ty.ty();
                if !self.registry.is_complete(type_ref) {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::SizeOfIncompleteType { ty: type_ref, span });
                } else {
                    let _ = self.registry.ensure_layout(type_ref);
                }
                Some(QualType::unqualified(self.registry.type_long_unsigned))
            }
            NodeKind::CompoundLiteral(ty, init) => {
                self.visit_type_expressions(*ty);
                let _ = self.registry.ensure_layout(ty.ty());
                self.check_initializer(*init, *ty);
                Some(*ty)
            }
            NodeKind::GenericSelection(gs) => self.visit_generic_selection(gs),
            NodeKind::GenericAssociation(ga) => {
                if let Some(ty) = ga.ty {
                    self.visit_type_expressions(ty);
                }
                self.visit_node(ga.result_expr)
            }
            NodeKind::InitializerList(list) => {
                for item_ref in list.init_start.range(list.init_len) {
                    self.visit_node(item_ref);
                }
                None
            }
            NodeKind::InitializerItem(init) => {
                for designator_ref in init.designator_start.range(init.designator_len) {
                    if let NodeKind::Designator(d) = self.ast.get_kind(designator_ref) {
                        match d {
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
                }
                self.visit_node(init.initializer);
                None
            }
            NodeKind::BuiltinVaArg(ty, expr) => {
                self.visit_type_expressions(*ty);
                self.visit_node(*expr);
                Some(*ty)
            }
            NodeKind::BuiltinVaStart(ap, last) => {
                self.visit_node(*ap);
                self.visit_node(*last);
                Some(QualType::unqualified(self.registry.type_void))
            }
            NodeKind::BuiltinVaEnd(ap) => {
                self.visit_node(*ap);
                Some(QualType::unqualified(self.registry.type_void))
            }
            NodeKind::BuiltinVaCopy(dst, src) => {
                self.visit_node(*dst);
                self.visit_node(*src);
                Some(QualType::unqualified(self.registry.type_void))
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
            let ctx = crate::semantic::const_eval::ConstEvalCtx {
                ast: self.ast,
                symbol_table: self.symbol_table,
            };
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
