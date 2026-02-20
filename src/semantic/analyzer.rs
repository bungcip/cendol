use crate::{
    ast::{nodes::*, *},
    diagnostic::{DiagnosticEngine, SemanticError},
    semantic::{
        ArraySizeType, BuiltinType, QualType, StructMember, SymbolKind, SymbolTable, TypeKind, TypeQualifiers, TypeRef,
        TypeRegistry,
        const_eval::ConstEvalCtx,
        conversions::{integer_promotion, usual_arithmetic_conversions},
    },
};

use smallvec::{SmallVec, smallvec};
use std::collections::{HashMap, HashSet};

/// Side table containing semantic information for AST nodes.
/// Parallel vectors indexed by node index (NodeRef.index()).
#[derive(Debug, Clone)]
pub struct SemanticInfo {
    pub types: Vec<Option<QualType>>,
    pub conversions: Vec<SmallVec<[Conversion; 1]>>,
    pub value_categories: Vec<ValueCategory>,
    pub generic_selections: HashMap<usize, NodeRef>, // Maps NodeIndex of GenericSelection to selected result_expr
    pub offsetof_results: HashMap<usize, i64>,       // Maps NodeIndex of BuiltinOffsetof to computed offset
}

impl SemanticInfo {
    pub(crate) fn with_capacity(n: usize) -> Self {
        Self {
            types: vec![None; n],
            conversions: vec![SmallVec::new(); n],
            value_categories: vec![ValueCategory::RValue; n],
            generic_selections: HashMap::new(),
            offsetof_results: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueCategory {
    LValue,
    RValue,
}

/// Implicit Conversions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conversion {
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
pub(crate) fn visit_ast(
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
        loop_depth: 0,
        switch_depth: 0,
        switch_cases: SmallVec::new(),
        switch_default_seen: SmallVec::new(),
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
    loop_depth: usize,
    switch_depth: usize,
    // Bolt ⚡: Use SmallVec for switch state to avoid heap allocations for nested switches.
    switch_cases: SmallVec<[HashSet<i64>; 4]>,
    switch_default_seen: SmallVec<[bool; 4]>,
    checked_types: HashSet<TypeRef>,
}

impl<'a> SemanticAnalyzer<'a> {
    fn report_error(&mut self, error: SemanticError) {
        self.diag.report(error);
    }

    fn push_conversion(&mut self, node_ref: NodeRef, conv: Conversion) {
        self.semantic_info.conversions[node_ref.index()].push(conv);
    }

    fn unwrap_initializer_item(&self, node_ref: NodeRef) -> (NodeRef, NodeRef, u16) {
        if let NodeKind::InitializerItem(item) = self.ast.get_kind(node_ref) {
            (item.initializer, item.designator_start, item.designator_len)
        } else {
            (node_ref, NodeRef::new(1).unwrap(), 0)
        }
    }

    fn const_ctx(&self) -> ConstEvalCtx<'_> {
        ConstEvalCtx {
            ast: self.ast,
            symbol_table: self.symbol_table,
            registry: self.registry,
            semantic_info: Some(self.semantic_info),
        }
    }

    /// Recursively visit type to find any expressions (e.g. VLA sizes) and resolve them.
    fn visit_type_expressions(&mut self, qt: QualType) {
        let ty = qt.ty();
        // ⚡ Bolt: Optimized duplicate check.
        // `HashSet::insert` returns `false` if the value was already present.
        // This is faster than calling `contains` and then `insert`, as it
        // performs a single lookup instead of two.
        if !self.checked_types.insert(ty) {
            return;
        }

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
                for param in parameters.iter() {
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

    fn is_always_true(&self, expr: NodeRef) -> bool {
        crate::semantic::const_eval::eval_const_expr(&self.const_ctx(), expr).is_some_and(|v| v != 0)
    }

    fn contains_break(&self, node_ref: NodeRef) -> bool {
        match self.ast.get_kind(node_ref) {
            NodeKind::Break => true,
            NodeKind::CompoundStatement(cs) => cs.stmt_start.range(cs.stmt_len).any(|s| self.contains_break(s)),
            NodeKind::If(if_stmt) => {
                self.contains_break(if_stmt.then_branch) || if_stmt.else_branch.is_some_and(|e| self.contains_break(e))
            }
            // Do not recurse into nested loops or switches as their breaks belong to them.
            NodeKind::While(_) | NodeKind::For(_) | NodeKind::DoWhile(_, _) | NodeKind::Switch(_, _) => false,
            NodeKind::Label(_, stmt, _) => self.contains_break(*stmt),
            _ => false,
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
            NodeKind::While(while_stmt) => {
                !self.is_always_true(while_stmt.condition) || self.contains_break(while_stmt.body)
            }
            NodeKind::DoWhile(body, condition) => !self.is_always_true(*condition) || self.contains_break(*body),
            NodeKind::For(for_stmt) => {
                for_stmt.condition.is_some_and(|c| !self.is_always_true(c)) || self.contains_break(for_stmt.body)
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
            NodeKind::Label(_, stmt, _) => self.can_fall_through(*stmt),
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
            NodeKind::Literal(literal::Literal::String(_)) => true,
            NodeKind::CompoundLiteral(..) => true,
            NodeKind::GenericSelection(_) => {
                if let Some(&selected) = self.semantic_info.generic_selections.get(&node_ref.index()) {
                    self.is_lvalue(selected)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn is_bitfield(&self, node_ref: NodeRef) -> bool {
        let node_kind = self.ast.get_kind(node_ref);
        match node_kind {
            NodeKind::MemberAccess(obj_ref, field_name, is_arrow) => {
                let Some(obj_ty) = self.semantic_info.types[obj_ref.index()] else {
                    return false;
                };
                let record_ty_ref = if *is_arrow {
                    let Some(pointee) = self.registry.get_pointee(obj_ty.ty()) else {
                        return false;
                    };
                    pointee.ty()
                } else {
                    obj_ty.ty()
                };

                fn find_bitfield(registry: &TypeRegistry, record_ty: TypeRef, name: NameId) -> bool {
                    if let TypeKind::Record { members, .. } = &registry.get(record_ty).kind {
                        if let Some(member) = members.iter().find(|m| m.name == Some(name)) {
                            return member.bit_field_size.is_some();
                        }
                        for member in members.iter() {
                            if member.name.is_none() && find_bitfield(registry, member.member_type.ty(), name) {
                                return true;
                            }
                        }
                    }
                    false
                }

                find_bitfield(self.registry, record_ty_ref, *field_name)
            }
            NodeKind::GenericSelection(_) => {
                if let Some(&selected) = self.semantic_info.generic_selections.get(&node_ref.index()) {
                    self.is_bitfield(selected)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn is_register_variable(&self, node_ref: NodeRef) -> bool {
        let node_kind = self.ast.get_kind(node_ref);
        match node_kind {
            NodeKind::Ident(_, symbol_ref) => {
                let symbol = self.symbol_table.get_symbol(*symbol_ref);
                if let SymbolKind::Variable { storage, .. } = &symbol.kind {
                    return *storage == Some(StorageClass::Register);
                }
                false
            }
            NodeKind::GenericSelection(_) => {
                if let Some(&selected) = self.semantic_info.generic_selections.get(&node_ref.index()) {
                    self.is_register_variable(selected)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn is_null_pointer_constant(&self, node_ref: NodeRef) -> bool {
        let node_kind = self.ast.get_kind(node_ref);
        match node_kind {
            NodeKind::Literal(literal::Literal::Int { val: 0, .. }) => true,
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
        self.loop_depth += 1;
        self.visit_node(stmt.body);
        self.loop_depth -= 1;
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
        self.loop_depth += 1;
        self.visit_node(stmt.body);
        self.loop_depth -= 1;
    }

    fn visit_return_statement(&mut self, expr: &Option<NodeRef>, span: SourceSpan) {
        if self.current_function_is_noreturn {
            self.report_error(SemanticError::NoreturnFunctionHasReturn {
                name: self.current_function_name.clone().unwrap(),
                span,
            });
        }

        let ret_ty = self.current_function_ret_type;
        let is_void_func = ret_ty.is_some_and(|ty| ty.is_void());
        let func_name = self.current_function_name.as_deref().unwrap_or("<unknown>");

        let Some(expr_ref) = expr else {
            if !is_void_func {
                self.report_error(SemanticError::NonVoidReturnWithoutValue {
                    name: func_name.to_string(),
                    span,
                });
            }
            return;
        };

        if is_void_func {
            let err_span = self.ast.get_span(*expr_ref);
            self.report_error(SemanticError::VoidReturnWithValue {
                name: func_name.to_string(),
                span: err_span,
            });
        }

        if let Some(expr_ty) = self.visit_node(*expr_ref)
            && let Some(target_ty) = ret_ty
        {
            self.record_implicit_conversions(target_ty, expr_ty, *expr_ref);
        }
    }

    fn visit_unary_op(&mut self, op: UnaryOp, operand_ref: NodeRef, span: SourceSpan) -> Option<QualType> {
        let operand_ty = self.visit_node(operand_ref)?;

        match op {
            UnaryOp::AddrOf => {
                if !self.is_lvalue(operand_ref) {
                    self.report_error(SemanticError::NotAnLvalue { span });
                    return None;
                }
                if self.is_bitfield(operand_ref) {
                    self.report_error(SemanticError::AddressOfBitfield { span });
                    return None;
                }
                if self.is_register_variable(operand_ref) {
                    self.report_error(SemanticError::AddressOfRegister { span });
                    return None;
                }
                if operand_ty.is_array() || operand_ty.is_function() {
                    let decayed = self.registry.decay(operand_ty, TypeQualifiers::empty());
                    self.push_conversion(operand_ref, Conversion::PointerDecay { to: decayed.ty() });
                    return Some(decayed);
                }
                Some(QualType::unqualified(self.registry.pointer_to(operand_ty)))
            }
            UnaryOp::Deref => {
                let actual_ty = if operand_ty.is_array() || operand_ty.is_function() {
                    let decayed = self.registry.decay(operand_ty, TypeQualifiers::empty());
                    self.push_conversion(operand_ref, Conversion::PointerDecay { to: decayed.ty() });
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
            UnaryOp::Real | UnaryOp::Imag => {
                if let TypeKind::Complex { base_type } = &self.registry.get(operand_ty.ty()).kind {
                    Some(QualType::new(*base_type, operand_ty.qualifiers()))
                } else if operand_ty.is_real() {
                    if op == UnaryOp::Real {
                        Some(operand_ty)
                    } else {
                        // __imag__ on real type returns zero of that type
                        Some(self.registry.strip_all(operand_ty))
                    }
                } else {
                    let type_kind = &self.registry.get(operand_ty.ty()).kind;
                    self.report_error(SemanticError::InvalidUnaryOperand {
                        ty: type_kind.to_string(),
                        span,
                    });
                    None
                }
            }
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                self.check_lvalue_and_modifiable(operand_ref, operand_ty, span);
                if operand_ty.is_scalar() { Some(operand_ty) } else { None }
            }
            UnaryOp::Plus | UnaryOp::Minus => {
                if operand_ty.is_arithmetic() {
                    // C11 6.5.3.3: The integer promotions are performed on the operand,
                    // and the result has the promoted type.
                    let promoted = self.apply_and_record_integer_promotion(operand_ref, operand_ty);

                    // Strip all qualifiers for unary plus/minus operations
                    let stripped = self.registry.strip_all(promoted);
                    if stripped.qualifiers() != promoted.qualifiers() {
                        self.push_conversion(
                            operand_ref,
                            Conversion::QualifierAdjust {
                                from: promoted.qualifiers(),
                                to: stripped.qualifiers(),
                            },
                        );
                    }
                    Some(stripped)
                } else {
                    let type_kind = &self.registry.get(operand_ty.ty()).kind;
                    self.report_error(SemanticError::InvalidUnaryOperand {
                        ty: type_kind.to_string(),
                        span,
                    });
                    None
                }
            }
            UnaryOp::LogicNot => {
                // Logical NOT always returns int type (C11 6.5.3.3)
                Some(QualType::unqualified(self.registry.type_int))
            }
            UnaryOp::BitNot => {
                if operand_ty.is_integer() {
                    Some(self.apply_and_record_integer_promotion(operand_ref, operand_ty))
                } else if operand_ty.is_complex() {
                    Some(operand_ty)
                } else {
                    let type_kind = &self.registry.get(operand_ty.ty()).kind;
                    self.report_error(SemanticError::InvalidUnaryOperand {
                        ty: type_kind.to_string(),
                        span,
                    });
                    None
                }
            }
        }
    }

    fn apply_and_record_integer_promotion(&mut self, node_ref: NodeRef, ty: QualType) -> QualType {
        let promoted = integer_promotion(self.registry, ty);
        if promoted.ty() != ty.ty() {
            self.push_conversion(
                node_ref,
                Conversion::IntegerPromotion {
                    from: ty.ty(),
                    to: promoted.ty(),
                },
            );
        }
        promoted
    }

    fn analyze_binary_operation_types(
        &mut self,
        op: BinaryOp,
        lhs_promoted: QualType,
        rhs_promoted: QualType,
        span: SourceSpan,
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
            BinaryOp::Equal | BinaryOp::NotEqual => {
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
                            span,
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

            BinaryOp::Less | BinaryOp::LessEqual | BinaryOp::Greater | BinaryOp::GreaterEqual => {
                let common = if lhs_promoted.is_pointer() && rhs_promoted.is_pointer() {
                    let lhs_base = self.registry.get_pointee(lhs_promoted.ty()).unwrap();
                    let rhs_base = self.registry.get_pointee(rhs_promoted.ty()).unwrap();
                    if lhs_base != rhs_base {
                        let lhs_str = self.registry.display_type(lhs_promoted.ty());
                        let rhs_str = self.registry.display_type(rhs_promoted.ty());
                        self.report_error(SemanticError::IncompatiblePointerComparison {
                            lhs: lhs_str,
                            rhs: rhs_str,
                            span,
                        });
                    }
                    lhs_promoted
                } else if lhs_promoted.is_real() && rhs_promoted.is_real() {
                    usual_arithmetic_conversions(self.registry, lhs_promoted, rhs_promoted)?
                } else {
                    let lhs_str = self.registry.display_qual_type(lhs_promoted);
                    let rhs_str = self.registry.display_qual_type(rhs_promoted);
                    self.report_error(SemanticError::InvalidBinaryOperands {
                        left_ty: lhs_str,
                        right_ty: rhs_str,
                        span,
                    });
                    return None;
                };
                Some((QualType::unqualified(self.registry.type_int), common))
            }

            // Logical operations
            BinaryOp::LogicAnd | BinaryOp::LogicOr => {
                // Result has type int (C11 6.5.13/6.5.14)
                Some((QualType::unqualified(self.registry.type_int), lhs_promoted))
            }

            // Shift operations
            BinaryOp::LShift | BinaryOp::RShift => {
                // C11 6.5.7: result is type of promoted left operand
                Some((lhs_promoted, lhs_promoted))
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
        span: SourceSpan,
    ) -> Option<QualType> {
        debug_assert!(
            !op.is_assignment(),
            "visit_binary_op called with assignment operator: {:?}",
            op
        );
        let lhs_ty = self.visit_node(lhs_ref)?;
        let rhs_ty = self.visit_node(rhs_ref)?;

        // Perform array/function decay first
        let mut lhs_decayed = lhs_ty;
        if lhs_ty.is_array() || lhs_ty.is_function() {
            lhs_decayed = self.registry.decay(lhs_ty, TypeQualifiers::empty());
            self.push_conversion(lhs_ref, Conversion::PointerDecay { to: lhs_decayed.ty() });
        }

        let mut rhs_decayed = rhs_ty;
        if rhs_ty.is_array() || rhs_ty.is_function() {
            rhs_decayed = self.registry.decay(rhs_ty, TypeQualifiers::empty());
            self.push_conversion(rhs_ref, Conversion::PointerDecay { to: rhs_decayed.ty() });
        }

        if op == BinaryOp::Comma {
            return Some(rhs_decayed);
        }

        // Perform integer promotions and record them
        let lhs_promoted = self.apply_and_record_integer_promotion(lhs_ref, lhs_decayed);
        let rhs_promoted = self.apply_and_record_integer_promotion(rhs_ref, rhs_decayed);

        if op == BinaryOp::Mod && (!lhs_promoted.is_integer() || !rhs_promoted.is_integer()) {
            let lhs_kind = &self.registry.get(lhs_promoted.ty()).kind;
            let rhs_kind = &self.registry.get(rhs_promoted.ty()).kind;
            self.report_error(SemanticError::InvalidBinaryOperands {
                left_ty: lhs_kind.to_string(),
                right_ty: rhs_kind.to_string(),
                span,
            });
            return None;
        }

        let (result_ty, common_ty) = self.analyze_binary_operation_types(op, lhs_promoted, rhs_promoted, span)?;

        // For arithmetic/comparison operations, operands should be converted to a common type.
        let lhs_kind = self.ast.get_kind(lhs_ref);
        let rhs_kind = self.ast.get_kind(rhs_ref);

        let is_literal = |kind: &NodeKind| {
            matches!(
                kind,
                NodeKind::Literal(literal::Literal::Int { .. })
                    | NodeKind::Literal(literal::Literal::Char(_))
                    | NodeKind::Literal(literal::Literal::Float { .. })
            )
        };

        if lhs_promoted.ty() != common_ty.ty() || is_literal(lhs_kind) {
            self.push_conversion(
                lhs_ref,
                Conversion::IntegerCast {
                    from: lhs_promoted.ty(),
                    to: common_ty.ty(),
                },
            );
        }
        if rhs_promoted.ty() != common_ty.ty() || is_literal(rhs_kind) {
            self.push_conversion(
                rhs_ref,
                Conversion::IntegerCast {
                    from: rhs_promoted.ty(),
                    to: common_ty.ty(),
                },
            );
        }

        Some(result_ty)
    }

    fn visit_assignment(
        &mut self,
        node_ref: NodeRef,
        op: BinaryOp,
        lhs_ref: NodeRef,
        rhs_ref: NodeRef,
        span: SourceSpan,
    ) -> Option<QualType> {
        debug_assert!(
            op.is_assignment(),
            "visit_assignment called with non-assignment operator: {:?}",
            op
        );

        let lhs_ty = self.visit_node(lhs_ref)?;
        let rhs_ty = self.visit_node(rhs_ref)?;

        if !self.check_lvalue_and_modifiable(lhs_ref, lhs_ty, span) {
            return None;
        }

        if let Some(arithmetic_op) = op.without_assignment() {
            return self.visit_compound_assignment(node_ref, arithmetic_op, lhs_ref, rhs_ref, lhs_ty, rhs_ty, span);
        }

        // Simple assignment
        if !self.validate_and_record_assignment(lhs_ty, rhs_ty, rhs_ref, span) {
            return None;
        }

        Some(lhs_ty)
    }

    fn visit_compound_assignment(
        &mut self,
        node_ref: NodeRef,
        arithmetic_op: BinaryOp,
        lhs_ref: NodeRef,
        rhs_ref: NodeRef,
        lhs_ty: QualType,
        rhs_ty: QualType,
        span: SourceSpan,
    ) -> Option<QualType> {
        // Reuse visit_binary_op logic conceptually, but for compound assignment operands.
        // For p += 1, LHS is pointer, RHS is integer.
        let lhs_promoted = self.apply_and_record_integer_promotion(lhs_ref, lhs_ty);
        let rhs_promoted = self.apply_and_record_integer_promotion(rhs_ref, rhs_ty);

        let (common_ty, target_ty) = if let Some((_, common_ty)) =
            self.analyze_binary_operation_types(arithmetic_op, lhs_promoted, rhs_promoted, span)
        {
            // Record conversions from promoted operands to the common type.
            // This is what the binary operation will actually work with.
            if lhs_promoted.ty() != common_ty.ty() {
                self.push_conversion(
                    lhs_ref,
                    Conversion::IntegerCast {
                        from: lhs_promoted.ty(),
                        to: common_ty.ty(),
                    },
                );
            }
            if rhs_promoted.ty() != common_ty.ty() {
                self.push_conversion(
                    rhs_ref,
                    Conversion::IntegerCast {
                        from: rhs_promoted.ty(),
                        to: common_ty.ty(),
                    },
                );
            }

            // For compound assignment, the result of (lhs op rhs) is converted back to lhs type.
            // We record this conversion on the assignment node itself.
            (common_ty, lhs_ty)
        } else {
            let lhs_kind = &self.registry.get(lhs_promoted.ty()).kind;
            let rhs_kind = &self.registry.get(rhs_promoted.ty()).kind;
            self.report_error(SemanticError::InvalidBinaryOperands {
                left_ty: lhs_kind.to_string(),
                right_ty: rhs_kind.to_string(),
                span,
            });
            return None;
        };

        // Check assignment constraints (C11 6.5.16.1)
        // Note: For compound assignment, the RHS is the result of the binary operation (common_ty).
        // BUT, `check_assignment_constraints` expects the RHS expression ref for some specific checks (like NULL pointer constants).
        // Here, rhs_ref is the original RHS of the +=. This might be slightly inaccurate if check_assignment_constraints relies heavily on the node structure for value checks,
        // but for type checks it uses `common_ty` (which is the effective RHS).
        // The previous code passed `effective_rhs_ty` which was `common_ty`.
        if !self.check_assignment_constraints(lhs_ty, common_ty, rhs_ref) {
            let lhs_kind = &self.registry.get(lhs_ty.ty()).kind;
            let rhs_kind = &self.registry.get(common_ty.ty()).kind;

            self.report_error(SemanticError::TypeMismatch {
                expected: lhs_kind.to_string(),
                found: rhs_kind.to_string(),
                span,
            });
            return None;
        }

        if target_ty.ty() != common_ty.ty() {
            self.push_conversion(
                node_ref,
                Conversion::IntegerCast {
                    from: common_ty.ty(),
                    to: target_ty.ty(),
                },
            );
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
                self.registry.get_array_element(rhs_ty.ty())
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
        let mut current_rhs_ty = rhs_ty;

        // 1. Null pointer constant conversion (0 or (void*)0 -> T*)
        if lhs_ty.is_pointer() && self.is_null_pointer_constant(rhs_ref) {
            self.push_conversion(rhs_ref, Conversion::NullPointerConstant);
            if lhs_ty.ty() != self.registry.type_void_ptr {
                self.push_conversion(
                    rhs_ref,
                    Conversion::PointerCast {
                        from: self.registry.type_void_ptr,
                        to: lhs_ty.ty(),
                    },
                );
            }
            return;
        }

        // 2. Array/Function-to-pointer decay
        if lhs_ty.is_pointer() && (current_rhs_ty.is_array() || current_rhs_ty.is_function()) {
            current_rhs_ty = self.registry.decay(current_rhs_ty, TypeQualifiers::empty());
            self.push_conversion(
                rhs_ref,
                Conversion::PointerDecay {
                    to: current_rhs_ty.ty(),
                },
            );
        }

        // 3. Qualifier adjustment
        if lhs_ty.ty() == current_rhs_ty.ty() && lhs_ty.qualifiers() != current_rhs_ty.qualifiers() {
            self.push_conversion(
                rhs_ref,
                Conversion::QualifierAdjust {
                    from: current_rhs_ty.qualifiers(),
                    to: lhs_ty.qualifiers(),
                },
            );
        }

        // 4. Casts (Integer or Pointer)
        let is_literal = matches!(
            self.ast.get_kind(rhs_ref),
            NodeKind::Literal(literal::Literal::Int { .. })
                | NodeKind::Literal(literal::Literal::Char(_))
                | NodeKind::Literal(literal::Literal::Float { .. })
        );

        let is_arithmetic_cast = lhs_ty.is_arithmetic() && current_rhs_ty.is_arithmetic();
        let is_pointer_cast = lhs_ty.is_pointer() && current_rhs_ty.is_pointer();

        if (is_arithmetic_cast || is_pointer_cast) && (lhs_ty.ty() != current_rhs_ty.ty() || is_literal) {
            let conv = if is_pointer_cast {
                Conversion::PointerCast {
                    from: current_rhs_ty.ty(),
                    to: lhs_ty.ty(),
                }
            } else {
                Conversion::IntegerCast {
                    from: current_rhs_ty.ty(),
                    to: lhs_ty.ty(),
                }
            };
            self.push_conversion(rhs_ref, conv);
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

    fn visit_initializer(&mut self, init_ref: NodeRef, target_ty: QualType) {
        match self.ast.get_kind(init_ref) {
            NodeKind::InitializerList(list) => {
                self.semantic_info.types[init_ref.index()] = Some(target_ty);
                let list = *list;
                self.visit_initializer_list(&list, target_ty);
            }
            NodeKind::Literal(literal::Literal::String(_)) if target_ty.is_array() => {
                let Some(init_ty) = self.visit_node(init_ref) else {
                    return;
                };

                let lhs_elem = self.registry.get_array_element(target_ty.ty()).unwrap();
                let rhs_elem = self.registry.get_array_element(init_ty.ty()).unwrap();

                let is_rhs_char = rhs_elem == self.registry.type_char;
                let is_lhs_char_type = [
                    self.registry.type_char,
                    self.registry.type_schar,
                    self.registry.type_char_unsigned,
                ]
                .contains(&lhs_elem);

                let compatible = if is_rhs_char {
                    is_lhs_char_type
                } else {
                    self.registry
                        .is_compatible(QualType::unqualified(lhs_elem), QualType::unqualified(rhs_elem))
                };

                if compatible {
                    self.record_implicit_conversions(target_ty, init_ty, init_ref);
                } else {
                    self.report_error(SemanticError::TypeMismatch {
                        expected: self.registry.get(target_ty.ty()).kind.to_string(),
                        found: self.registry.get(init_ty.ty()).kind.to_string(),
                        span: self.ast.get_span(init_ref),
                    });
                }
            }
            _ => {
                if let Some(init_ty) = self.visit_node(init_ref) {
                    self.check_assignment_and_record(target_ty, init_ty, init_ref);
                }
            }
        }
    }

    fn visit_initializer_list(&mut self, list: &InitializerListData, target_ty: QualType) {
        if target_ty.is_scalar() {
            let mut items = list.init_start.range(list.init_len);

            if let Some(first_ref) = items.next() {
                let (expr, _, _) = self.unwrap_initializer_item(first_ref);
                if let Some(init_ty) = self.visit_node(expr) {
                    self.check_assignment_and_record(target_ty, init_ty, expr);
                }
            }

            for (i, item_ref) in items.enumerate() {
                if i == 0 {
                    self.report_error(SemanticError::ExcessElements {
                        kind: "scalar".to_string(),
                        span: self.ast.get_span(item_ref),
                    });
                }
                let (expr, _, _) = self.unwrap_initializer_item(item_ref);
                self.visit_node(expr);
            }
            return;
        }

        let target_type = self.registry.get(target_ty.ty()).clone();
        match target_type.kind {
            TypeKind::Record { .. } => {
                let mut flat_members = Vec::new();
                target_type.flatten_members(self.registry, &mut flat_members);

                for item_ref in list.init_start.range(list.init_len) {
                    self.visit_initializer_item_record(item_ref, &flat_members, target_ty);
                }
            }
            _ => {
                for item_ref in list.init_start.range(list.init_len) {
                    let (expr, d_start, d_len) = self.unwrap_initializer_item(item_ref);
                    for designator_ref in d_start.range(d_len) {
                        let NodeKind::Designator(d) = self.ast.get_kind(designator_ref) else {
                            continue;
                        };
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
                    self.visit_node(expr);
                }
            }
        }
    }

    fn visit_initializer_item_record(&mut self, item_ref: NodeRef, members: &[StructMember], record_ty: QualType) {
        let node_kind = self.ast.get_kind(item_ref);
        if let NodeKind::InitializerItem(init) = node_kind {
            // 1. Validate designators
            if init.designator_len > 0 {
                let first_des_ref = init.designator_start;
                if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(first_des_ref) {
                    // Check if member exists
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

        if let TypeKind::Function {
            parameters,
            is_variadic,
            ..
        } = &func_kind
        {
            let is_variadic = *is_variadic;
            for (i, arg_node_ref) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
                let Some(arg_ty) = self.visit_node(arg_node_ref) else {
                    continue;
                };

                if i < parameters.len() {
                    let mut actual_arg_ty = arg_ty;
                    if arg_ty.is_array() || arg_ty.is_function() {
                        actual_arg_ty = self.registry.decay(arg_ty, TypeQualifiers::empty());
                        self.push_conversion(arg_node_ref, Conversion::PointerDecay { to: actual_arg_ty.ty() });
                    }
                    self.record_implicit_conversions(parameters[i].param_type, actual_arg_ty, arg_node_ref);
                } else if is_variadic {
                    let mut actual_arg_ty = arg_ty;
                    if arg_ty.is_array() || arg_ty.is_function() {
                        actual_arg_ty = self.registry.decay(arg_ty, TypeQualifiers::empty());
                        self.push_conversion(arg_node_ref, Conversion::PointerDecay { to: actual_arg_ty.ty() });
                    }

                    let promoted_ty =
                        crate::semantic::conversions::default_argument_promotions(self.registry, actual_arg_ty);

                    if promoted_ty.ty() != actual_arg_ty.ty() {
                        self.record_implicit_conversions(promoted_ty, actual_arg_ty, arg_node_ref);
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

        let (record_ty_ref, base_quals) = if is_arrow {
            let pointee = self.registry.get_pointee(obj_ty.ty())?;
            (pointee.ty(), pointee.qualifiers())
        } else {
            (obj_ty.ty(), obj_ty.qualifiers())
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
                for member in members.iter() {
                    if member.name.is_none() {
                        let member_ty = member.member_type.ty();
                        if member_ty.is_record()
                            && let Some(found_ty) = find_member(registry, member_ty, name)
                        {
                            // Note: C11 6.7.2.1p13: "An unnamed member of structure type with no tag is called an anonymous structure;
                            // an unnamed member of union type with no tag is called an anonymous union."
                            // We don't need to merge qualifiers of the anonymous member ITSELF here because
                            // they will be merged with base_quals later.
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

        if let Some(mut ty) = find_member(self.registry, record_ty_ref, field_name) {
            // C11 6.5.2.3p4: if the first expression has qualified type, the result has the so-qualified
            // version of the type of the designated member.
            if !base_quals.is_empty() {
                ty = self.registry.merge_qualifiers(ty, base_quals);
            }
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
            let element_type = self.registry.get_array_element(arr_ty.ty()).unwrap();
            Some(QualType::new(element_type, arr_ty.qualifiers()))
        } else {
            self.registry.get_pointee(arr_ty.ty())
        }
    }

    fn visit_declaration_node(&mut self, node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        match kind {
            NodeKind::TranslationUnit(tu_data) => {
                for decl_ref in tu_data.decl_start.range(tu_data.decl_len) {
                    self.visit_node(decl_ref);
                }
                None
            }
            NodeKind::Function(data) => self.visit_function_definition(data, node_ref),
            NodeKind::Param(data) => {
                self.visit_type_expressions(data.ty);
                Some(data.ty)
            }
            NodeKind::VarDecl(data) => self.visit_var_declaration(data, node_ref),
            NodeKind::EnumConstant(_, value_expr) => {
                if let Some(expr) = value_expr {
                    self.visit_node(*expr);
                }
                Some(QualType::unqualified(self.registry.type_int))
            }
            NodeKind::EnumDecl(data) => {
                for member_ref in data.member_start.range(data.member_len) {
                    self.visit_node(member_ref);
                }
                None
            }
            NodeKind::EnumMember(data) => {
                if let Some(expr) = data.init_expr {
                    self.visit_node(expr);
                }
                Some(QualType::unqualified(self.registry.type_int))
            }
            NodeKind::RecordDecl(_) => None,
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
                if let TypeKind::Function {
                    return_type,
                    parameters,
                    ..
                } = func_type
                {
                    if !self.registry.is_complete(return_type) && return_type != self.registry.type_void {
                        let span = self.ast.get_span(node_ref);
                        self.report_error(SemanticError::IncompleteReturnType { span });
                    }

                    for param in parameters.iter() {
                        let _ = self.registry.ensure_layout(param.param_type.ty());
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn visit_function_definition(&mut self, data: &FunctionData, node_ref: NodeRef) -> Option<QualType> {
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
            let span = self.ast.get_span(node_ref);
            self.report_error(SemanticError::NoreturnFunctionFallsOff {
                name: self.current_function_name.clone().unwrap(),
                span,
            });
        }

        self.current_function_ret_type = None;
        self.current_function_name = prev_func_name;
        self.current_function_is_noreturn = false;
        None
    }

    fn visit_var_declaration(&mut self, data: &VarDeclData, node_ref: NodeRef) -> Option<QualType> {
        if data.ty.ty() == self.registry.type_void {
            let span = self.ast.get_span(node_ref);
            self.report_error(SemanticError::VariableOfVoidType { span });
        }
        self.visit_type_expressions(data.ty);
        let _ = self.registry.ensure_layout(data.ty.ty());
        if data.init.is_some()
            && matches!(data.storage, Some(StorageClass::Extern))
            && self.current_function_name.is_some()
        {
            let span = self.ast.get_span(node_ref);
            self.report_error(SemanticError::InvalidInitializer { span });
        }

        if let Some(init_ref) = data.init {
            self.visit_initializer(init_ref, data.ty);
        }
        Some(data.ty)
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
                self.loop_depth += 1;
                self.visit_node(*body);
                self.loop_depth -= 1;
                self.visit_node(*condition);
                None
            }
            NodeKind::Switch(cond, body) => self.visit_switch_statement(*cond, *body),
            NodeKind::Case(expr, stmt) => {
                let span = self.ast.get_span(node_ref);
                self.visit_case_statement(Some(*expr), None, *stmt, span)
            }
            NodeKind::CaseRange(start, end, stmt) => {
                let span = self.ast.get_span(node_ref);
                self.visit_case_statement(Some(*start), Some(*end), *stmt, span)
            }
            NodeKind::Default(stmt) => {
                let span = self.ast.get_span(node_ref);
                self.visit_default_statement(*stmt, span)
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
            NodeKind::Break => {
                if self.loop_depth == 0 && self.switch_depth == 0 {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::BreakNotInLoop { span });
                }
                None
            }
            NodeKind::Continue => {
                if self.loop_depth == 0 {
                    let span = self.ast.get_span(node_ref);
                    self.report_error(SemanticError::ContinueNotInLoop { span });
                }
                None
            }
            NodeKind::Goto(_, _) => None,
            NodeKind::Label(_, stmt, _) => {
                self.visit_node(*stmt);
                None
            }
            _ => None,
        }
    }

    fn visit_switch_statement(&mut self, cond: NodeRef, body: NodeRef) -> Option<QualType> {
        self.visit_node(cond);
        self.switch_depth += 1;
        self.switch_cases.push(HashSet::new());
        self.switch_default_seen.push(false);
        self.visit_node(body);
        self.switch_default_seen.pop();
        self.switch_cases.pop();
        self.switch_depth -= 1;
        None
    }

    fn visit_case_statement(
        &mut self,
        start: Option<NodeRef>,
        end: Option<NodeRef>,
        stmt: NodeRef,
        span: SourceSpan,
    ) -> Option<QualType> {
        if self.switch_depth == 0 {
            self.report_error(SemanticError::CaseNotInSwitch { span });
        } else if let Some(start_ref) = start {
            let start_val = crate::semantic::const_eval::eval_const_expr(&self.const_ctx(), start_ref);
            let end_val = if let Some(end_ref) = end {
                crate::semantic::const_eval::eval_const_expr(&self.const_ctx(), end_ref)
            } else {
                start_val
            };

            if let (Some(start_v), Some(end_v)) = (start_val, end_val) {
                let mut duplicate_val = None;
                if let Some(cases) = self.switch_cases.last_mut() {
                    for val in start_v..=end_v {
                        if !cases.insert(val) {
                            duplicate_val = Some(val);
                            break;
                        }
                    }
                }
                if let Some(val) = duplicate_val {
                    self.report_error(SemanticError::DuplicateCase {
                        value: val.to_string(),
                        span,
                    });
                }
            }
        }

        if let Some(s) = start {
            self.visit_node(s);
        }
        if let Some(e) = end {
            self.visit_node(e);
        }
        self.visit_node(stmt);
        None
    }

    fn visit_default_statement(&mut self, stmt: NodeRef, span: SourceSpan) -> Option<QualType> {
        if self.switch_depth == 0 {
            self.report_error(SemanticError::CaseNotInSwitch { span });
        } else {
            let is_duplicate = self
                .switch_default_seen
                .last_mut()
                .is_some_and(|seen| std::mem::replace(seen, true));
            if is_duplicate {
                self.report_error(SemanticError::MultipleDefaultLabels { span });
            }
        }
        self.visit_node(stmt);
        None
    }

    fn visit_expression_node(&mut self, node_ref: NodeRef, kind: &NodeKind) -> Option<QualType> {
        match kind {
            NodeKind::Literal(literal) => self.visit_literal(literal),
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
            NodeKind::TernaryOp(cond, then, else_expr) => self.visit_ternary_op(*cond, *then, *else_expr),
            NodeKind::GnuStatementExpression(stmt, result_expr) => {
                self.visit_node(*stmt);

                if let NodeKind::Dummy = self.ast.get_kind(*result_expr) {
                    Some(QualType::unqualified(self.registry.type_void))
                } else {
                    self.visit_node(*result_expr)
                }
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
            NodeKind::SizeOfExpr(expr) => self.visit_sizeof_alignof(Some(*expr), None, false, node_ref),
            NodeKind::SizeOfType(ty) => self.visit_sizeof_alignof(None, Some(*ty), false, node_ref),
            NodeKind::AlignOf(ty) => self.visit_sizeof_alignof(None, Some(*ty), true, node_ref),
            NodeKind::CompoundLiteral(ty, init) => {
                self.visit_type_expressions(*ty);
                let _ = self.registry.ensure_layout(ty.ty());
                self.visit_initializer(*init, *ty);
                Some(*ty)
            }
            NodeKind::GenericSelection(gs) => self.visit_generic_selection(gs, node_ref),
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
            NodeKind::BuiltinExpect(exp, c) => {
                let ty = self.visit_node(*exp);
                self.visit_node(*c);
                ty
            }
            NodeKind::BuiltinOffsetof(ty, expr) => self.visit_builtin_offsetof(*ty, *expr, node_ref),
            NodeKind::AtomicOp(op, args_start, args_len) => {
                let span = self.ast.get_span(node_ref);
                self.visit_atomic_op(*op, *args_start, *args_len, span)
            }
            _ => None,
        }
    }

    fn visit_ternary_op(&mut self, cond: NodeRef, then: NodeRef, else_expr: NodeRef) -> Option<QualType> {
        self.visit_node(cond);
        let then_ty = self.visit_node(then);
        let else_ty = self.visit_node(else_expr);

        if let (Some(t), Some(e)) = (then_ty, else_ty) {
            let result_ty = match (t, e) {
                (t, e) if t.is_arithmetic() && e.is_arithmetic() => usual_arithmetic_conversions(self.registry, t, e),
                (t, e) if t.ty() == e.ty() => Some(t),
                (t, _) if t.ty() == self.registry.type_void => Some(t),
                (_, e) if e.ty() == self.registry.type_void => Some(e),
                (t, _) if t.is_pointer() && self.is_null_pointer_constant(else_expr) => Some(t),
                (_, e) if e.is_pointer() && self.is_null_pointer_constant(then) => Some(e),
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
                // Don't record conversions for void types
                if !res.is_void() {
                    self.record_implicit_conversions(res, t, then);
                    self.record_implicit_conversions(res, e, else_expr);
                }
                return Some(res);
            }
            None
        } else {
            None
        }
    }

    fn visit_sizeof_alignof(
        &mut self,
        expr: Option<NodeRef>,
        ty: Option<QualType>,
        is_alignof: bool,
        node_ref: NodeRef,
    ) -> Option<QualType> {
        let type_ref = if let Some(t) = ty {
            self.visit_type_expressions(t);
            Some(t.ty())
        } else if let Some(e) = expr {
            self.visit_node(e).map(|qt| qt.ty())
        } else {
            None
        };

        if let Some(type_ref) = type_ref {
            // function type check
            let is_function = matches!(self.registry.get(type_ref).kind, TypeKind::Function { .. });

            if is_function {
                let span = self.ast.get_span(node_ref);
                if is_alignof {
                    self.report_error(SemanticError::AlignOfFunctionType { span });
                } else {
                    self.report_error(SemanticError::SizeOfFunctionType { span });
                }
            } else if !self.registry.is_complete(type_ref) {
                let span = self.ast.get_span(node_ref);
                if is_alignof {
                    self.report_error(SemanticError::AlignOfIncompleteType { ty: type_ref, span });
                } else {
                    self.report_error(SemanticError::SizeOfIncompleteType { ty: type_ref, span });
                }
            } else if !is_alignof && expr.is_some() && self.is_bitfield(expr.unwrap()) {
                let span = self.ast.get_span(node_ref);
                self.report_error(SemanticError::SizeOfBitfield { span });
            } else {
                let _ = self.registry.ensure_layout(type_ref);
            }
        }

        Some(QualType::unqualified(self.registry.type_long_unsigned))
    }

    fn visit_atomic_op(
        &mut self,
        op: AtomicOp,
        args_start: NodeRef,
        args_len: u16,
        span: SourceSpan,
    ) -> Option<QualType> {
        // Bolt ⚡: Optimized argument processing by using SmallVec and a single pass.
        // This avoids three Vec allocations and multiple iterations over the arguments.
        // Atomic operations have at most 6 arguments (CompareExchangeN).
        let mut args = SmallVec::<[NodeRef; 6]>::new();
        let mut arg_tys = SmallVec::<[QualType; 6]>::new();
        let mut has_error = false;

        for arg_ref in args_start.range(args_len) {
            args.push(arg_ref);
            if let Some(ty) = self.visit_node(arg_ref) {
                arg_tys.push(ty);
            } else {
                has_error = true;
            }
        }

        if has_error {
            return None;
        }

        let expected_args = match op {
            AtomicOp::LoadN => 2,
            AtomicOp::CompareExchangeN => 6,
            _ => 3,
        };

        if args.len() != expected_args {
            self.report_error(SemanticError::InvalidNumberOfArguments {
                expected: expected_args,
                found: args.len(),
                span,
            });
            return None;
        }

        // Validate memory order arguments
        let memorder_indices: SmallVec<[usize; 2]> = match op {
            AtomicOp::LoadN => smallvec![1],
            AtomicOp::CompareExchangeN => smallvec![4, 5],
            _ => smallvec![2],
        };

        for &idx in &memorder_indices {
            if !arg_tys[idx].is_integer() {
                let ty_str = self.registry.display_qual_type(arg_tys[idx]);
                self.report_error(SemanticError::InvalidAtomicArgument {
                    ty: ty_str,
                    span: self.ast.get_span(args[idx]),
                });
            }
        }

        // Validate pointer argument (always index 0)
        let pointee = if let Some(pointee) = self.registry.get_pointee(arg_tys[0].ty()) {
            pointee
        } else {
            let ty_str = self.registry.display_qual_type(arg_tys[0]);
            self.report_error(SemanticError::InvalidAtomicArgument {
                ty: ty_str,
                span: self.ast.get_span(args[0]),
            });
            return None; // Cannot proceed without valid pointer
        };

        match op {
            AtomicOp::LoadN => Some(pointee),
            AtomicOp::StoreN => {
                if !self.check_assignment_constraints(pointee, arg_tys[1], args[1]) {
                    let ty_str = self.registry.display_qual_type(arg_tys[1]);
                    self.report_error(SemanticError::InvalidAtomicArgument {
                        ty: ty_str,
                        span: self.ast.get_span(args[1]),
                    });
                } else {
                    self.record_implicit_conversions(pointee, arg_tys[1], args[1]);
                }
                Some(QualType::unqualified(self.registry.type_void))
            }
            AtomicOp::ExchangeN => {
                self.record_implicit_conversions(pointee, arg_tys[1], args[1]);
                Some(pointee)
            }
            AtomicOp::CompareExchangeN => {
                let expected_ptr_ty = arg_tys[1];
                let desired_ty = arg_tys[2];

                if let Some(expected_pointee) = self.registry.get_pointee(expected_ptr_ty.ty()) {
                    if !self
                        .registry
                        .is_compatible(QualType::unqualified(pointee.ty()), expected_pointee)
                    {
                        let expected_str = self.registry.display_qual_type(expected_pointee);
                        self.report_error(SemanticError::InvalidAtomicArgument {
                            ty: expected_str,
                            span: self.ast.get_span(args[1]),
                        });
                    }
                } else {
                    let ty_str = self.registry.display_qual_type(expected_ptr_ty);
                    self.report_error(SemanticError::InvalidAtomicArgument {
                        ty: ty_str,
                        span: self.ast.get_span(args[1]),
                    });
                }
                self.record_implicit_conversions(pointee, desired_ty, args[2]);
                Some(QualType::unqualified(self.registry.type_bool))
            }
            AtomicOp::FetchAdd | AtomicOp::FetchSub | AtomicOp::FetchAnd | AtomicOp::FetchOr | AtomicOp::FetchXor => {
                if matches!(op, AtomicOp::FetchAnd | AtomicOp::FetchOr | AtomicOp::FetchXor) && !pointee.is_integer() {
                    let ty_str = self.registry.display_qual_type(pointee);
                    self.report_error(SemanticError::InvalidAtomicArgument {
                        ty: ty_str,
                        span: self.ast.get_span(args[0]),
                    });
                }

                if pointee.is_integer() {
                    self.record_implicit_conversions(pointee, arg_tys[1], args[1]);
                }
                Some(pointee)
            }
        }
    }

    fn visit_literal(&mut self, literal: &literal::Literal) -> Option<QualType> {
        match literal {
            literal::Literal::Int { val, suffix } => {
                let ty = match suffix {
                    Some(literal::IntegerSuffix::L) => self.registry.type_long,
                    Some(literal::IntegerSuffix::LL) => self.registry.type_long_long,
                    Some(literal::IntegerSuffix::U) => self.registry.type_int_unsigned,
                    Some(literal::IntegerSuffix::UL) => self.registry.type_long_unsigned,
                    Some(literal::IntegerSuffix::ULL) => self.registry.type_long_long_unsigned,
                    None => {
                        let _ = self.registry.ensure_layout(self.registry.type_int);
                        let _ = self.registry.ensure_layout(self.registry.type_long);

                        let int_layout = self.registry.get_layout(self.registry.type_int);
                        let int_max = if int_layout.size >= 8 {
                            i64::MAX
                        } else {
                            (1i64 << (int_layout.size * 8 - 1)) - 1
                        };

                        let long_layout = self.registry.get_layout(self.registry.type_long);
                        let long_max = if long_layout.size >= 8 {
                            i64::MAX
                        } else {
                            (1i64 << (long_layout.size * 8 - 1)) - 1
                        };

                        if *val >= 0 && *val <= int_max {
                            self.registry.type_int
                        } else if *val >= 0 && *val <= long_max {
                            self.registry.type_long
                        } else {
                            self.registry.type_long_long
                        }
                    }
                };
                Some(QualType::unqualified(ty))
            }
            literal::Literal::Float { suffix, .. } => {
                let ty = match suffix {
                    Some(literal::FloatSuffix::F) => self.registry.type_float,
                    Some(literal::FloatSuffix::L) => self.registry.type_long_double,
                    None => self.registry.type_double,
                };
                Some(QualType::unqualified(ty))
            }
            literal::Literal::Char(_) => Some(QualType::unqualified(self.registry.type_int)),
            literal::Literal::String(name) => {
                let parsed = crate::semantic::literal_utils::parse_string_literal(*name);
                let element_type = match parsed.builtin_type {
                    BuiltinType::Char => self.registry.type_char,
                    BuiltinType::Int => self.registry.type_int,
                    BuiltinType::UShort => self.registry.type_short_unsigned,
                    BuiltinType::UInt => self.registry.type_int_unsigned,
                    _ => self.registry.type_char,
                };

                let array_type = self
                    .registry
                    .array_of(element_type, ArraySizeType::Constant(parsed.size));
                let _ = self.registry.ensure_layout(array_type);
                Some(QualType::new(array_type, TypeQualifiers::empty()))
            }
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
        if self.deferred_checks.is_empty() {
            return;
        }

        // Bolt ⚡: Use std::mem::take and iterate to avoid heap allocation and copy from collect()
        let checks = std::mem::take(&mut self.deferred_checks);
        for check in checks {
            match check {
                DeferredCheck::StaticAssert(node_ref) => self.visit_static_assert(node_ref),
            }
        }
    }

    fn visit_static_assert(&mut self, node_ref: NodeRef) {
        let NodeKind::StaticAssert(cond, msg_ref) = *self.ast.get_kind(node_ref) else {
            return;
        };

        self.visit_node(cond);

        match crate::semantic::const_eval::eval_const_expr(&self.const_ctx(), cond) {
            Some(0) => {
                let message = match self.ast.get_kind(msg_ref) {
                    NodeKind::Literal(literal::Literal::String(s)) => s.as_str().to_string(),
                    _ => String::new(),
                };

                self.report_error(SemanticError::StaticAssertFailed {
                    message,
                    span: self.ast.get_span(node_ref),
                });
            }
            None => self.report_error(SemanticError::StaticAssertNotConstant {
                span: self.ast.get_span(node_ref),
            }),
            _ => {}
        }
    }

    fn visit_generic_selection(&mut self, gs: &GenericSelectionData, node_ref: NodeRef) -> Option<QualType> {
        // First, visit the controlling expression to determine its type.
        let ctrl_ty = self.visit_node(gs.control)?;

        // C11 6.5.1.1p3: The controlling expression of a generic selection is not evaluated.
        // C11 6.5.1.1p2: The type of the controlling expression is compared with the type name of each generic
        // association. Before comparison, array and function types decay to pointers.
        let decayed_ctrl_ty = if ctrl_ty.is_array() || ctrl_ty.is_function() {
            // Qualifiers on the array/function type itself are discarded during decay.
            self.registry.decay(ctrl_ty, TypeQualifiers::empty())
        } else {
            ctrl_ty
        };

        // After decay, top-level qualifiers are removed for the compatibility check.
        let unqualified_ctrl_ty = self.registry.strip_all(decayed_ctrl_ty);

        // C11 6.5.1.1p2: The controlling expression shall be an expression of a complete object type,
        // or the void type.
        if !self.registry.is_complete(decayed_ctrl_ty.ty()) && decayed_ctrl_ty.ty() != self.registry.type_void {
            self.report_error(SemanticError::GenericIncompleteControl {
                ty: self.registry.display_qual_type(ctrl_ty),
                span: self.ast.get_span(gs.control),
            });
        }

        // It's crucial to visit *all* result expressions to ensure they are
        // fully type-checked, even if they are not the selected branch.
        // This resolves all identifier types within them.
        let mut selected_expr_ref = None;
        let mut default_expr_ref = None;
        let mut default_first_span = None;
        // Bolt ⚡: Use SmallVec to avoid heap allocation for small generic selection lists.
        let mut seen_types: SmallVec<[(QualType, SourceSpan); 8]> = SmallVec::new();

        for assoc_node_ref in gs.assoc_start.range(gs.assoc_len) {
            let NodeKind::GenericAssociation(ga) = *self.ast.get_kind(assoc_node_ref) else {
                continue;
            };

            let assoc_span = self.ast.get_span(assoc_node_ref);
            self.visit_node(assoc_node_ref);

            let Some(assoc_ty) = ga.ty else {
                // This is the 'default' association.
                // Constraint 2: If a generic selection has a default association, there shall be only one such association.
                if let Some(first_span) = default_first_span {
                    self.report_error(SemanticError::GenericMultipleDefault {
                        span: assoc_span,
                        first_def: first_span,
                    });
                } else {
                    default_first_span = Some(assoc_span);
                    default_expr_ref = Some(ga.result_expr);
                }
                continue;
            };

            // C11 6.5.1.1p2: The type name in a generic association shall specify a complete object type
            // other than a variably modified type.
            let assoc_ty_kind = &self.registry.get(assoc_ty.ty()).kind;
            if matches!(assoc_ty_kind, TypeKind::Function { .. }) {
                self.report_error(SemanticError::GenericFunctionAssociation {
                    ty: self.registry.display_qual_type(assoc_ty),
                    span: assoc_span,
                });
            } else if !self.registry.is_complete(assoc_ty.ty()) {
                self.report_error(SemanticError::GenericIncompleteAssociation {
                    ty: self.registry.display_qual_type(assoc_ty),
                    span: assoc_span,
                });
            } else if self.registry.is_variably_modified(assoc_ty.ty()) {
                self.report_error(SemanticError::GenericVlaAssociation {
                    ty: self.registry.display_qual_type(assoc_ty),
                    span: assoc_span,
                });
            }

            // C11 6.5.1.1p2: The controlling expression... shall have type compatible with at most one...
            // "No two generic associations in the same generic selection shall specify compatible types."

            // Constraint 2: No two generic associations in the same generic selection shall specify compatible types.
            let mut duplicate = false;
            for (prev_ty, prev_span) in &seen_types {
                if self.registry.is_compatible(assoc_ty, *prev_ty) {
                    self.report_error(SemanticError::GenericDuplicateMatch {
                        ty: self.registry.display_qual_type(assoc_ty),
                        prev_ty: self.registry.display_qual_type(*prev_ty),
                        span: assoc_span,
                        first_def: *prev_span,
                    });
                    duplicate = true;
                    break;
                }
            }

            if !duplicate {
                seen_types.push((assoc_ty, assoc_span));
            }

            // Constraint 1: The controlling expression... shall have type compatible with at most one...
            // unqualified_ctrl_ty is the controlling expression type after lvalue conversion (which strips qualifiers).
            // It is compared against the association type (which keeps qualifiers).
            if self.registry.is_compatible(unqualified_ctrl_ty, assoc_ty) && selected_expr_ref.is_none() {
                selected_expr_ref = Some(ga.result_expr);
                self.semantic_info
                    .generic_selections
                    .insert(node_ref.index(), ga.result_expr);
            }
        }

        // If no specific type matches, use the default association if it exists.
        if selected_expr_ref.is_none() {
            selected_expr_ref = default_expr_ref;
            if let Some(expr) = default_expr_ref {
                self.semantic_info.generic_selections.insert(node_ref.index(), expr);
            }
        }

        // The type of the _Generic expression is the type of the selected result expression.
        if let Some(expr_ref) = selected_expr_ref {
            // The type should already be resolved from the earlier pass.
            let idx = expr_ref.index();
            self.semantic_info.types.get(idx).and_then(|t| *t)
        } else {
            // If no match is found and there's no default, it's a semantic error.
            self.report_error(SemanticError::GenericNoMatch {
                ty: self.registry.display_qual_type(ctrl_ty),
                span: self.ast.get_span(node_ref),
            });
            None
        }
    }

    fn visit_builtin_offsetof(&mut self, ty: QualType, expr_ref: NodeRef, node_ref: NodeRef) -> Option<QualType> {
        self.visit_type_expressions(ty);

        let mut current_ty = ty;
        let mut offset = 0i64;

        if !self.compute_offsetof_recursive(expr_ref, &mut current_ty, &mut offset) {
            let res_ty = QualType::unqualified(self.registry.type_long_unsigned);
            return Some(res_ty);
        }

        self.semantic_info.offsetof_results.insert(node_ref.index(), offset);
        let res_ty = QualType::unqualified(self.registry.type_long_unsigned);
        Some(res_ty)
    }

    fn compute_offsetof_recursive(&mut self, node_ref: NodeRef, current_ty: &mut QualType, offset: &mut i64) -> bool {
        let kind = *self.ast.get_kind(node_ref);
        match kind {
            NodeKind::Dummy => true,
            NodeKind::MemberAccess(base, member_name, is_arrow) => {
                if !self.compute_offsetof_recursive(base, current_ty, offset) {
                    return false;
                }

                let record_ty = if is_arrow {
                    self.registry.get_pointee(current_ty.ty()).map(|qt| qt.ty())
                } else {
                    Some(current_ty.ty())
                };

                let Some(record_ty) = record_ty else {
                    self.report_error(SemanticError::MemberAccessOnNonRecord {
                        ty: self.registry.display_qual_type(*current_ty),
                        span: self.ast.get_span(node_ref),
                    });
                    return false;
                };

                if !record_ty.is_record() {
                    self.report_error(SemanticError::MemberAccessOnNonRecord {
                        ty: self.registry.display_qual_type(QualType::unqualified(record_ty)),
                        span: self.ast.get_span(node_ref),
                    });
                    return false;
                }

                let mut flat_members = Vec::new();
                let mut flat_offsets = Vec::new();
                let ty_obj = self.registry.get(record_ty);
                ty_obj.flatten_members_with_layouts(self.registry, &mut flat_members, &mut flat_offsets, 0);

                if let Some(idx) = flat_members.iter().position(|m| m.name == Some(member_name)) {
                    *offset += flat_offsets[idx] as i64;
                    *current_ty = flat_members[idx].member_type;
                    true
                } else {
                    self.report_error(SemanticError::MemberNotFound {
                        name: member_name,
                        ty: self.registry.display_type(record_ty),
                        span: self.ast.get_span(node_ref),
                    });
                    false
                }
            }
            NodeKind::IndexAccess(base, index) => {
                if !self.compute_offsetof_recursive(base, current_ty, offset) {
                    return false;
                }

                let elem_ty = self.registry.get_array_element(current_ty.ty());
                let Some(elem_ty) = elem_ty else {
                    self.report_error(SemanticError::ExpectedArrayType {
                        found: self.registry.display_qual_type(*current_ty),
                        span: self.ast.get_span(node_ref),
                    });
                    return false;
                };

                self.visit_node(index);
                let index_val = crate::semantic::const_eval::eval_const_expr(&self.const_ctx(), index);
                let Some(index_val) = index_val else {
                    // C11 7.19p3: "integer constant expression"
                    self.report_error(SemanticError::NonConstantInitializer {
                        span: self.ast.get_span(index),
                    });
                    return false;
                };

                let layout = self.registry.get_layout(elem_ty);
                *offset += index_val * (layout.size as i64);
                *current_ty = QualType::unqualified(elem_ty);
                true
            }
            _ => {
                self.report_error(SemanticError::InvalidOffsetofDesignator {
                    span: self.ast.get_span(node_ref),
                });
                false
            }
        }
    }
}
