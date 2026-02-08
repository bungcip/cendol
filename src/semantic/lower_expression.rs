use crate::ast::nodes::AtomicOp;
use crate::ast::{BinaryOp, NodeKind, NodeRef, UnaryOp};
use crate::mir::{
    AtomicMemOrder, BinaryIntOp, CallTarget, ConstValue, ConstValueKind, MirStmt, Operand, Place, Rvalue, Terminator,
    TypeId,
};
use crate::semantic::ast_to_mir::AstToMirLowerer;
use crate::semantic::const_eval::eval_const_expr;
use crate::semantic::{QualType, SymbolKind, SymbolRef, TypeKind, ValueCategory, mir_ops};
use crate::{ast, semantic};

impl<'a> AstToMirLowerer<'a> {
    pub(crate) fn lower_expression_as_place(&mut self, expr_ref: NodeRef) -> Place {
        let op = self.lower_expression(expr_ref, true);
        let ty = self.ast.get_resolved_type(expr_ref).unwrap();
        let mir_ty = self.lower_qual_type(ty);
        self.ensure_place(op, mir_ty)
    }

    pub(crate) fn lower_expression(&mut self, expr_ref: NodeRef, need_value: bool) -> Operand {
        let ty = self.ast.get_resolved_type(expr_ref).unwrap_or_else(|| {
            let node_kind = self.ast.get_kind(expr_ref);
            let node_span = self.ast.get_span(expr_ref);
            panic!("Type not resolved for node {:?} at {:?}", node_kind, node_span);
        });
        let node_kind = *self.ast.get_kind(expr_ref);

        let mir_ty = self.lower_qual_type(ty);

        if let Some(const_op) = self.try_constant_fold(expr_ref, &node_kind, ty) {
            return const_op;
        }

        match &node_kind {
            NodeKind::Literal(_) => self.lower_literal(&node_kind, ty).expect("Failed to lower literal"),
            NodeKind::Ident(_, symbol_ref) => self.lower_ident(*symbol_ref),
            NodeKind::UnaryOp(op, operand_ref) => self.lower_unary_op_expr(op, *operand_ref, mir_ty),
            NodeKind::PostIncrement(operand_ref) => self.lower_inc_dec_expression(*operand_ref, true, true, need_value),
            NodeKind::PostDecrement(operand_ref) => {
                self.lower_inc_dec_expression(*operand_ref, false, true, need_value)
            }
            NodeKind::BinaryOp(op, left_ref, right_ref) => self.lower_binary_op_expr(op, *left_ref, *right_ref, mir_ty),
            NodeKind::Assignment(op, left_ref, right_ref) => {
                self.lower_assignment_expr(expr_ref, op, *left_ref, *right_ref, mir_ty)
            }
            NodeKind::FunctionCall(call_expr) => {
                // Check for builtin float constant functions
                if let Some(builtin_op) = self.try_lower_builtin_float_const(call_expr, mir_ty) {
                    return builtin_op;
                }

                let is_void = self.mir_builder.get_type(mir_ty).is_void();
                let temp_place = if need_value && !is_void {
                    let (_, temp_place) = self.create_temp_local(mir_ty);
                    Some(temp_place)
                } else {
                    None
                };

                self.lower_function_call(call_expr, temp_place.clone());

                if need_value {
                    if is_void {
                        self.create_dummy_operand()
                    } else {
                        Operand::Copy(Box::new(temp_place.unwrap()))
                    }
                } else {
                    self.create_dummy_operand()
                }
            }
            NodeKind::MemberAccess(obj_ref, field_name, is_arrow) => {
                self.lower_member_access(*obj_ref, field_name, *is_arrow)
            }
            NodeKind::IndexAccess(arr_ref, idx_ref) => self.lower_index_access(*arr_ref, *idx_ref),
            NodeKind::TernaryOp(cond, then, else_expr) => self.lower_ternary_op(*cond, *then, *else_expr, mir_ty),
            NodeKind::SizeOfExpr(expr) => {
                let ty = self
                    .ast
                    .get_resolved_type(*expr)
                    .expect("SizeOf operand type missing")
                    .ty();
                self.lower_type_query(ty, true)
            }
            NodeKind::SizeOfType(ty) => self.lower_type_query(ty.ty(), true),
            NodeKind::AlignOf(ty) => self.lower_type_query(ty.ty(), false),
            NodeKind::GenericSelection(gs) => self.lower_generic_selection(gs, need_value, expr_ref),
            NodeKind::GnuStatementExpression(stmt, result_expr) => {
                self.lower_gnu_statement_expression(*stmt, *result_expr, need_value)
            }
            NodeKind::Cast(_ty, operand_ref) => self.lower_cast(*operand_ref, mir_ty),
            NodeKind::CompoundLiteral(ty, init_ref) => self.lower_compound_literal(*ty, *init_ref),
            NodeKind::BuiltinVaArg(ty, expr) => self.lower_builtin_va_arg(*ty, *expr),
            NodeKind::BuiltinExpect(exp, c) => {
                let _ = self.lower_expression(*c, true); // lower 'c' for side effects or just to process it
                self.lower_expression(*exp, need_value)
            }
            NodeKind::AtomicOp(op, args_start, args_len) => self.lower_atomic_op(*op, *args_start, *args_len, mir_ty),
            NodeKind::BuiltinVaStart(..) | NodeKind::BuiltinVaEnd(..) | NodeKind::BuiltinVaCopy(..) => {
                self.lower_builtin_void(&node_kind)
            }
            NodeKind::InitializerList(_) | NodeKind::InitializerItem(_) => {
                panic!("InitializerList or InitializerItem not implemented");
            }
            _ => unreachable!(),
        }
    }

    fn try_constant_fold(&mut self, expr_ref: NodeRef, node_kind: &NodeKind, ty: QualType) -> Option<Operand> {
        // Attempt constant folding for arithmetic/logical operations that are not simple literals
        if matches!(
            node_kind,
            NodeKind::BinaryOp(..) | NodeKind::UnaryOp(..) | NodeKind::TernaryOp(..)
        ) && let Some(val) = eval_const_expr(&self.const_ctx(), expr_ref)
        {
            let ty_id = self.lower_qual_type(ty);
            return Some(Operand::Constant(self.create_constant(ty_id, ConstValueKind::Int(val))));
        }
        None
    }

    pub(crate) fn lower_gnu_statement_expression(
        &mut self,
        stmt: NodeRef,
        result_expr: NodeRef,
        need_value: bool,
    ) -> Operand {
        let stmt_kind = self.ast.get_kind(stmt);
        if let NodeKind::CompoundStatement(cs) = stmt_kind {
            let old_scope = self.current_scope_id;
            self.current_scope_id = cs.scope_id;

            for stmt_ref in cs.stmt_start.range(cs.stmt_len) {
                let is_last_stmt_expr = if let NodeKind::ExpressionStatement(Some(e)) = self.ast.get_kind(stmt_ref) {
                    *e == result_expr
                } else {
                    false
                };

                if is_last_stmt_expr {
                    continue;
                }

                let node_kind = self.ast.get_kind(stmt_ref);
                if self.mir_builder.current_block_has_terminator() {
                    if let NodeKind::Label(..) = node_kind {
                        // OK
                    } else {
                        continue;
                    }
                }
                self.lower_node_ref(stmt_ref);
            }

            let op = if let NodeKind::Dummy = self.ast.get_kind(result_expr) {
                self.create_dummy_operand()
            } else {
                self.lower_expression(result_expr, need_value)
            };

            self.current_scope_id = old_scope;
            op
        } else {
            panic!("GnuStatementExpression stmt is not CompoundStatement");
        }
    }

    pub(crate) fn lower_ternary_op(
        &mut self,
        cond: NodeRef,
        then_expr: NodeRef,
        else_expr: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        let is_void = matches!(self.mir_builder.get_type(mir_ty), crate::mir::MirType::Void);

        let cond_op = self.lower_expression(cond, true);

        let then_block = self.mir_builder.create_block();
        let else_block = self.mir_builder.create_block();
        let exit_block = self.mir_builder.create_block();

        self.mir_builder
            .set_terminator(Terminator::If(cond_op, then_block, else_block));

        // Result local
        let result_local = if !is_void {
            Some(self.mir_builder.create_local(None, mir_ty, false))
        } else {
            None
        };

        for (target_block, expr_ref) in [(then_block, then_expr), (else_block, else_expr)] {
            self.mir_builder.set_current_block(target_block);
            let val = self.lower_expression(expr_ref, !is_void);
            if let Some(local) = result_local {
                let val_conv = self.apply_conversions(val, expr_ref, mir_ty);
                self.emit_assignment(Place::Local(local), val_conv);
            }
            self.mir_builder.set_terminator(Terminator::Goto(exit_block));
        }

        self.mir_builder.set_current_block(exit_block);

        if let Some(local) = result_local {
            Operand::Copy(Box::new(Place::Local(local)))
        } else {
            self.create_dummy_operand()
        }
    }

    pub(crate) fn lower_type_query(&mut self, ty: semantic::TypeRef, is_size: bool) -> Operand {
        let layout = self.registry.get_layout(ty);
        let val = if is_size { layout.size } else { layout.alignment };
        self.create_int_operand(val as i64)
    }

    pub(crate) fn lower_generic_selection(
        &mut self,
        _gs: &ast::nodes::GenericSelectionData,
        need_value: bool,
        node_ref: NodeRef,
    ) -> Operand {
        let expr_to_lower = *self
            .ast
            .semantic_info
            .as_ref()
            .unwrap()
            .generic_selections
            .get(&node_ref.index())
            .expect("Generic selection failed (should be caught by Analyzer)");
        self.lower_expression(expr_to_lower, need_value)
    }

    pub(crate) fn lower_cast(&mut self, operand_ref: NodeRef, mir_ty: TypeId) -> Operand {
        let is_void = self.mir_builder.get_type(mir_ty).is_void();
        if is_void {
            self.lower_expression(operand_ref, false);
            return self.create_dummy_operand();
        }
        let operand = self.lower_expression(operand_ref, true);
        if self.get_operand_type(&operand) == mir_ty {
            return operand;
        }
        Operand::Cast(mir_ty, Box::new(operand))
    }

    pub(crate) fn lower_literal(&mut self, node_kind: &NodeKind, ty: QualType) -> Option<Operand> {
        let mir_ty = self.lower_qual_type(ty);
        match node_kind {
            NodeKind::Literal(literal) => match literal {
                crate::ast::literal::Literal::Int { val, .. } => Some(Operand::Constant(
                    self.create_constant(mir_ty, ConstValueKind::Int(*val)),
                )),
                crate::ast::literal::Literal::Float { val, .. } => Some(Operand::Constant(
                    self.create_constant(mir_ty, ConstValueKind::Float(*val)),
                )),
                crate::ast::literal::Literal::Char(val) => Some(Operand::Constant(
                    self.create_constant(mir_ty, ConstValueKind::Int(*val as i64)),
                )),
                crate::ast::literal::Literal::String(val) => Some(self.lower_literal_string(val, ty)),
            },
            _ => None,
        }
    }

    pub(crate) fn lower_unary_op_expr(&mut self, op: &UnaryOp, operand_ref: NodeRef, mir_ty: TypeId) -> Operand {
        let ty = self.ast.get_resolved_type(operand_ref).unwrap();
        if ty.is_complex() && !matches!(op, UnaryOp::AddrOf | UnaryOp::Deref) {
            return self.lower_complex_unary_op(op, operand_ref, mir_ty);
        }

        match op {
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                let is_inc = matches!(op, UnaryOp::PreIncrement);
                self.lower_inc_dec_expression(operand_ref, is_inc, false, true)
            }
            UnaryOp::AddrOf => self.lower_unary_addrof(operand_ref),
            UnaryOp::Deref => self.lower_unary_deref(operand_ref),
            _ => {
                let operand = self.lower_expression(operand_ref, true);
                let operand_converted = self.apply_conversions(operand, operand_ref, mir_ty);
                let operand_ty = self.get_operand_type(&operand_converted);
                let mir_type_info = self.mir_builder.get_type(operand_ty);

                let rval = mir_ops::emit_unary_rvalue(op, operand_converted, mir_type_info.is_float());
                self.emit_rvalue_to_operand(rval, mir_ty)
            }
        }
    }

    pub(crate) fn lower_unary_addrof(&mut self, operand_ref: NodeRef) -> Operand {
        let operand = self.lower_expression(operand_ref, true);
        if let Operand::Copy(place) = operand {
            Operand::AddressOf(place)
        } else if let Operand::Constant(const_id) = operand
            && self.ast.get_value_category(operand_ref) == Some(ValueCategory::LValue)
            && matches!(
                self.mir_builder.get_constants().get(&const_id),
                Some(ConstValue {
                    kind: ConstValueKind::FunctionAddress(_),
                    ..
                })
            )
        {
            Operand::Constant(const_id)
        } else {
            panic!("Cannot take address of a non-lvalue");
        }
    }

    pub(crate) fn lower_unary_deref(&mut self, operand_ref: NodeRef) -> Operand {
        let operand = self.lower_expression(operand_ref, true);
        let operand_ty = self.ast.get_resolved_type(operand_ref).unwrap();
        let target_mir_ty = self.lower_qual_type(operand_ty);
        let operand_converted = self.apply_conversions(operand, operand_ref, target_mir_ty);

        let place = self.deref_operand(operand_converted);
        Operand::Copy(Box::new(place))
    }

    pub(crate) fn lower_ident(&mut self, resolved_ref: SymbolRef) -> Operand {
        let entry = self.symbol_table.get_symbol(resolved_ref);

        match &entry.kind {
            SymbolKind::Variable { is_global, storage, .. } => {
                let is_static_local = *storage == Some(crate::ast::StorageClass::Static);
                if *is_global || is_static_local {
                    // Lazy lowering for globals/statics (e.g. __func__) that might not be lowered yet
                    if !self.global_map.contains_key(&resolved_ref) {
                        let ty_info = entry.type_info;
                        let mir_type_id = self.lower_qual_type(ty_info);
                        self.lower_variable_symbol(resolved_ref, mir_type_id);
                    }

                    let global_id = match self.global_map.get(&resolved_ref) {
                        Some(id) => id,
                        None => {
                            panic!(
                                "Global variable '{}' not found in MIR map even after lazy lowering attempt. Visited? {:?}",
                                entry.name,
                                self.global_map.keys()
                            );
                        }
                    };
                    Operand::Copy(Box::new(Place::Global(*global_id)))
                } else {
                    let local_id = self.local_map.get(&resolved_ref).unwrap();
                    Operand::Copy(Box::new(Place::Local(*local_id)))
                }
            }
            SymbolKind::Function { .. } => {
                let func_id = self
                    .mir_builder
                    .get_functions()
                    .iter()
                    .find(|(_, f)| f.name == entry.name)
                    .map(|(id, _)| *id)
                    .unwrap();
                let func_type = self.get_function_type(func_id);
                Operand::Constant(self.create_constant(func_type, ConstValueKind::FunctionAddress(func_id)))
            }
            SymbolKind::EnumConstant { value } => self.create_int_operand(*value),
            _ => panic!("Unexpected symbol kind"),
        }
    }

    pub(crate) fn unify_binary_operands(
        &mut self,
        mut lhs: Operand,
        mut rhs: Operand,
        lhs_mir_ty: TypeId,
        rhs_mir_ty: TypeId,
    ) -> (Operand, Operand) {
        if lhs_mir_ty != rhs_mir_ty {
            let lhs_mir = self.mir_builder.get_type(lhs_mir_ty);
            let rhs_mir = self.mir_builder.get_type(rhs_mir_ty);

            if lhs_mir.is_int() && rhs_mir.is_int() {
                let w1 = lhs_mir.width();
                let w2 = rhs_mir.width();
                if w1 > w2 {
                    rhs = Operand::Cast(lhs_mir_ty, Box::new(rhs));
                } else if w2 > w1 {
                    lhs = Operand::Cast(rhs_mir_ty, Box::new(lhs));
                }
            } else if lhs_mir.is_pointer() && rhs_mir.is_int() {
                rhs = Operand::Cast(lhs_mir_ty, Box::new(rhs));
            } else if lhs_mir.is_int() && rhs_mir.is_pointer() {
                lhs = Operand::Cast(rhs_mir_ty, Box::new(lhs));
            } else if lhs_mir.is_float() && rhs_mir.is_float() {
                let w1 = lhs_mir.width();
                let w2 = rhs_mir.width();
                if w1 > w2 {
                    rhs = Operand::Cast(lhs_mir_ty, Box::new(rhs));
                } else if w2 > w1 {
                    lhs = Operand::Cast(rhs_mir_ty, Box::new(lhs));
                }
            } else if lhs_mir.is_float() && rhs_mir.is_int() {
                rhs = Operand::Cast(lhs_mir_ty, Box::new(rhs));
            } else if lhs_mir.is_int() && rhs_mir.is_float() {
                lhs = Operand::Cast(rhs_mir_ty, Box::new(lhs));
            }
        }
        (lhs, rhs)
    }

    pub(crate) fn lower_binary_op_expr(
        &mut self,
        op: &BinaryOp,
        left_ref: NodeRef,
        right_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        debug_assert!(
            !op.is_assignment(),
            "lower_binary_op_expr called with assignment operator: {:?}",
            op
        );
        if matches!(op, BinaryOp::LogicAnd | BinaryOp::LogicOr) {
            return self.lower_logical_op(op, left_ref, right_ref, mir_ty);
        }

        if matches!(op, BinaryOp::Comma) {
            self.lower_expression(left_ref, false);
            let rhs = self.lower_expression(right_ref, true);
            // Apply conversions for RHS to match result type (comma result type is RHS type)
            let rhs_converted = self.apply_conversions(rhs, right_ref, mir_ty);
            return self.ensure_explicit_cast(rhs_converted, right_ref);
        }

        let lhs = self.lower_expression(left_ref, true);
        let rhs = self.lower_expression(right_ref, true);

        let (rval, _op_ty) = self.lower_binary_arithmetic_logic(op, lhs, rhs, left_ref, right_ref, mir_ty);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    fn lower_binary_arithmetic_logic(
        &mut self,
        op: &BinaryOp,
        lhs: Operand,
        rhs: Operand,
        left_ref: NodeRef,
        right_ref: NodeRef,
        context_ty: TypeId,
    ) -> (Rvalue, TypeId) {
        // Handle pointer arithmetic
        if let Some(rval) = self.lower_pointer_arithmetic(op, lhs.clone(), rhs.clone(), left_ref, right_ref) {
            let res_ty = match &rval {
                Rvalue::PtrAdd(base, _) | Rvalue::PtrSub(base, _) => self.get_operand_type(base),
                Rvalue::PtrDiff(..) => self.lower_type(self.registry.type_long),
                _ => unreachable!(),
            };
            return (rval, res_ty);
        }

        // Apply implicit conversions from semantic info first to match AST
        let lhs_converted = self.apply_conversions(lhs, left_ref, context_ty);
        let rhs_converted = self.apply_conversions(rhs, right_ref, context_ty);

        let lhs_mir_ty = self.get_operand_type(&lhs_converted);
        let rhs_mir_ty = self.get_operand_type(&rhs_converted);

        let lhs_is_complex = self.mir_builder.get_type(lhs_mir_ty).is_aggregate()
            && self.ast.get_resolved_type(left_ref).is_some_and(|t| t.is_complex());
        let rhs_is_complex = self.mir_builder.get_type(rhs_mir_ty).is_aggregate()
            && self.ast.get_resolved_type(right_ref).is_some_and(|t| t.is_complex());

        if lhs_is_complex || rhs_is_complex {
            let op = self.lower_complex_binary_op(op, lhs_converted, rhs_converted, context_ty);
            return (Rvalue::Use(op), context_ty);
        }

        // Ensure both operands have the same type for MIR operations.
        let (lhs_unified, rhs_unified) =
            self.unify_binary_operands(lhs_converted, rhs_converted, lhs_mir_ty, rhs_mir_ty);

        let lhs_final = self.ensure_explicit_cast(lhs_unified, left_ref);
        let rhs_final = self.ensure_explicit_cast(rhs_unified, right_ref);

        let common_ty = self.get_operand_type(&lhs_final);

        let common_mir_type = self.mir_builder.get_type(common_ty);
        let rval = mir_ops::emit_binary_rvalue(op, lhs_final, rhs_final, common_mir_type.is_float());

        let result_ty = match op {
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual => self.get_int_type(),
            _ => common_ty,
        };

        (rval, result_ty)
    }

    pub(crate) fn ensure_explicit_cast(&mut self, operand: Operand, node_ref: NodeRef) -> Operand {
        match operand {
            Operand::Constant(_) => {
                if let Some(ty) = self.ast.get_resolved_type(node_ref) {
                    let mir_type_id = self.lower_qual_type(ty);
                    Operand::Cast(mir_type_id, Box::new(operand))
                } else {
                    operand
                }
            }
            _ => operand,
        }
    }

    pub(crate) fn emit_bool_normalization(
        &mut self,
        value_op: Operand,
        result_place: Place,
        merge_block: crate::mir::MirBlockId,
    ) {
        let true_block = self.mir_builder.create_block();
        let false_block = self.mir_builder.create_block();

        self.mir_builder
            .set_terminator(Terminator::If(value_op, true_block, false_block));

        self.mir_builder.set_current_block(true_block);
        let one_op = self.create_int_operand(1);
        self.mir_builder
            .add_statement(MirStmt::Assign(result_place.clone(), Rvalue::Use(one_op)));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        self.mir_builder.set_current_block(false_block);
        let zero_op = self.create_int_operand(0);
        self.mir_builder
            .add_statement(MirStmt::Assign(result_place.clone(), Rvalue::Use(zero_op)));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));
    }

    pub(crate) fn lower_logical_op(
        &mut self,
        op: &BinaryOp,
        left_ref: NodeRef,
        right_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        // Short-circuiting logic for && and ||
        let (_res_local, res_place) = self.create_temp_local(mir_ty);

        let eval_rhs_block = self.mir_builder.create_block();
        let merge_block = self.mir_builder.create_block();
        let short_circuit_block = self.mir_builder.create_block();

        // 1. Evaluate LHS
        let lhs_op = self.lower_condition(left_ref);

        // Pre-create constants to avoid double borrow
        let zero_op = self.create_int_operand(0);
        let one_op = self.create_int_operand(1);

        let (short_circuit_val, true_target, false_target) = match op {
            BinaryOp::LogicAnd => (zero_op.clone(), eval_rhs_block, short_circuit_block),
            BinaryOp::LogicOr => (one_op.clone(), short_circuit_block, eval_rhs_block),
            _ => unreachable!(),
        };

        // if lhs { goto true_target } else { goto false_target }
        self.mir_builder
            .set_terminator(Terminator::If(lhs_op, true_target, false_target));

        // Short circuit case
        self.mir_builder.set_current_block(short_circuit_block);
        self.mir_builder
            .add_statement(MirStmt::Assign(res_place.clone(), Rvalue::Use(short_circuit_val)));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        // 2. Evaluate RHS
        self.mir_builder.set_current_block(eval_rhs_block);
        let rhs_val = self.lower_condition(right_ref);

        self.emit_bool_normalization(rhs_val, res_place.clone(), merge_block);

        // Merge
        self.mir_builder.set_current_block(merge_block);
        self.current_block = Some(merge_block);

        Operand::Copy(Box::new(res_place))
    }

    fn unwrap_cast_if_int(&mut self, op: Operand) -> Operand {
        if let Operand::Cast(_, inner) = &op {
            let inner_op = *inner.clone();
            let ty_id = self.get_operand_type(&inner_op);
            if self.mir_builder.get_type(ty_id).is_int() {
                return inner_op;
            }
            // Recursive check
            let unwrapped = self.unwrap_cast_if_int(inner_op.clone());
            let unwrapped_ty_id = self.get_operand_type(&unwrapped);
            if self.mir_builder.get_type(unwrapped_ty_id).is_int() {
                return unwrapped;
            }
        } else if let Operand::Constant(const_id) = &op {
            // Handle integer constants that were typed as pointers
            let const_val = self.mir_builder.get_constants().get(const_id).unwrap();
            if let ConstValueKind::Int(val) = const_val.kind {
                // Re-create as proper integer operand
                return self.create_int_operand(val);
            }
        }
        op
    }

    pub(crate) fn lower_pointer_arithmetic(
        &mut self,
        op: &BinaryOp,
        lhs: Operand,
        rhs: Operand,
        left_ref: NodeRef,
        right_ref: NodeRef,
    ) -> Option<Rvalue> {
        // Lower types and apply conversions locally to check for pointer arithmetic
        // We use the operand's own type as the target for conversion to avoid forcing
        // implicit casts to the result type (which causes issues for Ptr + Int -> Ptr)
        let lhs_ty = self.ast.get_resolved_type(left_ref).unwrap();
        let rhs_ty = self.ast.get_resolved_type(right_ref).unwrap();

        let lhs_mir_target = self.lower_qual_type(lhs_ty);
        let rhs_mir_target = self.lower_qual_type(rhs_ty);

        let lhs_converted = self.apply_conversions(lhs, left_ref, lhs_mir_target);
        let rhs_converted = self.apply_conversions(rhs, right_ref, rhs_mir_target);

        let lhs_mir_ty = self.get_operand_type(&lhs_converted);
        let rhs_mir_ty = self.get_operand_type(&rhs_converted);

        let lhs_type_info = self.mir_builder.get_type(lhs_mir_ty);
        let rhs_type_info = self.mir_builder.get_type(rhs_mir_ty);

        match op {
            BinaryOp::Add => {
                if lhs_type_info.is_pointer() && rhs_type_info.is_int() {
                    Some(self.create_pointer_arithmetic_rvalue(lhs_converted, rhs_converted, BinaryOp::Add))
                } else if rhs_type_info.is_pointer() && lhs_type_info.is_int() {
                    Some(self.create_pointer_arithmetic_rvalue(rhs_converted, lhs_converted, BinaryOp::Add))
                } else if lhs_type_info.is_pointer() && rhs_type_info.is_pointer() {
                    // Try unwrapping implicit casts (Analyzer might have casted Int to Ptr)
                    let lhs_unwrapped = self.unwrap_cast_if_int(lhs_converted.clone());
                    let rhs_unwrapped = self.unwrap_cast_if_int(rhs_converted.clone());

                    let lhs_u_ty = self.get_operand_type(&lhs_unwrapped);
                    let rhs_u_ty = self.get_operand_type(&rhs_unwrapped);

                    if self.mir_builder.get_type(lhs_u_ty).is_pointer() && self.mir_builder.get_type(rhs_u_ty).is_int()
                    {
                        Some(self.create_pointer_arithmetic_rvalue(lhs_unwrapped, rhs_unwrapped, BinaryOp::Add))
                    } else if self.mir_builder.get_type(rhs_u_ty).is_pointer()
                        && self.mir_builder.get_type(lhs_u_ty).is_int()
                    {
                        Some(self.create_pointer_arithmetic_rvalue(rhs_unwrapped, lhs_unwrapped, BinaryOp::Add))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            BinaryOp::Sub => {
                if lhs_type_info.is_pointer() {
                    if rhs_type_info.is_pointer() {
                        // Check if rhs is casted from int (Analyzer might have casted Int to Ptr)
                        let rhs_unwrapped = self.unwrap_cast_if_int(rhs_converted.clone());
                        let rhs_u_ty_id = self.get_operand_type(&rhs_unwrapped);

                        if self.mir_builder.get_type(rhs_u_ty_id).is_int() {
                            Some(self.create_pointer_arithmetic_rvalue(lhs_converted, rhs_unwrapped, BinaryOp::Sub))
                        } else {
                            Some(Rvalue::PtrDiff(lhs_converted, rhs_converted))
                        }
                    } else if rhs_type_info.is_int() {
                        Some(self.create_pointer_arithmetic_rvalue(lhs_converted, rhs_converted, BinaryOp::Sub))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub(crate) fn lower_assignment_expr(
        &mut self,
        node_ref: NodeRef,
        op: &BinaryOp,
        left_ref: NodeRef,
        right_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        debug_assert!(
            op.is_assignment(),
            "lower_assignment_expr called with non-assignment operator: {:?}",
            op
        );

        // Ensure the LHS is a place. If not, this is a semantic error.
        if self.ast.get_value_category(left_ref) != Some(ValueCategory::LValue) {
            panic!("LHS of assignment must be an lvalue");
        }

        // Use lower_expression_as_place to properly resolve the destination place
        let place = self.lower_expression_as_place(left_ref);

        let rhs_op = self.lower_expression(right_ref, true);

        let final_rhs = if let Some(compound_op) = op.without_assignment() {
            self.lower_compound_assignment(
                node_ref,
                compound_op,
                place.clone(),
                rhs_op,
                left_ref,
                right_ref,
                mir_ty,
            )
        } else {
            // Simple assignment, just use the RHS
            self.apply_conversions(rhs_op, right_ref, mir_ty)
        };

        self.emit_assignment(place, final_rhs.clone());
        final_rhs // C assignment expressions evaluate to the assigned value
    }

    pub(crate) fn lower_compound_assignment(
        &mut self,
        node_ref: NodeRef,
        compound_op: BinaryOp,
        place: Place,
        rhs_op: Operand,
        left_ref: NodeRef,
        right_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        // This is a compound assignment, e.g., a += b
        // Use the already-evaluated place to read the current value.
        let lhs_copy = Operand::Copy(Box::new(place));

        let (rval, op_ty) =
            self.lower_binary_arithmetic_logic(&compound_op, lhs_copy, rhs_op, left_ref, right_ref, mir_ty);
        let result_op = self.emit_rvalue_to_operand(rval, op_ty);
        self.apply_conversions(result_op, node_ref, mir_ty)
    }

    pub(crate) fn lower_function_call(&mut self, call_expr: &ast::nodes::CallExpr, dest_place: Option<Place>) {
        let callee = self.lower_expression(call_expr.callee, true);

        let arg_operands = self.lower_function_call_args(call_expr);

        let call_target = if let Operand::Constant(const_id) = callee {
            if let ConstValue {
                kind: ConstValueKind::FunctionAddress(func_id),
                ..
            } = self.mir_builder.get_constants().get(&const_id).unwrap()
            {
                CallTarget::Direct(*func_id)
            } else {
                panic!("Expected function address");
            }
        } else {
            CallTarget::Indirect(callee)
        };

        let stmt = MirStmt::Call {
            target: call_target,
            args: arg_operands,
            dest: dest_place,
        };
        self.mir_builder.add_statement(stmt);
    }

    fn lower_function_call_args(&mut self, call_expr: &ast::nodes::CallExpr) -> Vec<Operand> {
        let mut arg_operands = Vec::new();

        // Get the function type to determine parameter types for conversions
        let func_node_kind = self.ast.get_kind(call_expr.callee);
        let func_type_kind = if let NodeKind::Ident(_, symbol_ref) = func_node_kind {
            let resolved_symbol = *symbol_ref;
            let func_entry = self.symbol_table.get_symbol(resolved_symbol);
            Some(self.registry.get(func_entry.type_info.ty()).kind.clone())
        } else {
            None
        };

        let param_types = if let Some(TypeKind::Function { parameters, .. }) = func_type_kind.as_ref() {
            Some(
                parameters
                    .iter()
                    .map(|param| self.lower_qual_type(param.param_type))
                    .collect::<Vec<_>>(),
            )
        } else {
            None
        };

        for (i, arg_ref) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
            // Note: lower_expression(CallArg) will just lower the inner expression.
            // But we use arg_ref (the CallArg node) for implicit conversion lookup.
            let arg_operand = self.lower_expression(arg_ref, true);

            // Apply conversions for function arguments if needed
            // The resolved type of CallArg is same as inner expr.
            let arg_ty = self.ast.get_resolved_type(arg_ref).unwrap();
            let arg_mir_ty = self.lower_qual_type(arg_ty);

            // Use the parameter type as the target type for conversions, if available
            let target_mir_ty = if let Some(ref param_types_vec) = param_types {
                if i < param_types_vec.len() {
                    param_types_vec[i]
                } else {
                    // Variadic argument: Logic handled by implicit conversions (Promotion/Decay) calculated in analyzer.rs
                    // We just need a placeholder type, or the promoted type if we could calculate it.
                    // Since semantic analysis has inserted promoted type casts/conversions, we can start with the argument's own type.
                    arg_mir_ty
                }
            } else {
                // Unprototyped function: Logic handled by implicit conversions
                arg_mir_ty
            };

            let converted_arg = self.apply_conversions(arg_operand, arg_ref, target_mir_ty);

            arg_operands.push(converted_arg);
        }
        arg_operands
    }

    pub(crate) fn find_member_path(&self, record_ty: semantic::TypeRef, field_name: ast::NameId) -> Option<Vec<usize>> {
        let mut flat_members = Vec::new();
        let ty = self.registry.get(record_ty);
        ty.flatten_members(self.registry, &mut flat_members);

        if let Some(idx) = flat_members.iter().position(|m| m.name == Some(field_name)) {
            return Some(vec![idx]);
        }
        None
    }

    pub(crate) fn lower_member_access(
        &mut self,
        obj_ref: NodeRef,
        field_name: &ast::NameId,
        is_arrow: bool,
    ) -> Operand {
        let obj_ty = self.ast.get_resolved_type(obj_ref).unwrap();
        let record_ty = if is_arrow {
            self.registry
                .get_pointee(obj_ty.ty())
                .expect("Arrow access on non-pointer type")
                .ty()
        } else {
            obj_ty.ty()
        };

        if record_ty.is_record() {
            // Validate that the field exists and get its layout information
            let path = self
                .find_member_path(record_ty, *field_name)
                .expect("Field not found - should be caught by semantic analysis");

            // Apply the chain of field accesses

            // Resolve base place
            let mut current_place = self.lower_expression_as_place(obj_ref);

            if is_arrow {
                // Dereference: *ptr
                current_place = self.deref_place(current_place);
            }

            for field_idx in path {
                current_place = Place::StructField(Box::new(current_place), field_idx);
            }

            Operand::Copy(Box::new(current_place))
        } else {
            panic!("Member access on non-record type");
        }
    }

    pub(crate) fn lower_index_access(&mut self, arr_ref: NodeRef, idx_ref: NodeRef) -> Operand {
        let arr_ty = self.ast.get_resolved_type(arr_ref).unwrap();

        // Handle both array and pointer types for index access
        // In C, arr[idx] is equivalent to *(arr + idx)
        if arr_ty.is_array() || arr_ty.is_pointer() {
            let arr_place = self.lower_expression_as_place(arr_ref);
            let idx_operand = self.lower_expression(idx_ref, true);

            Operand::Copy(Box::new(Place::ArrayIndex(Box::new(arr_place), Box::new(idx_operand))))
        } else {
            panic!("Index access on non-array, non-pointer type");
        }
    }

    pub(crate) fn lower_inc_dec_expression(
        &mut self,
        operand_ref: NodeRef,
        is_inc: bool,
        is_post: bool,
        need_value: bool,
    ) -> Operand {
        let operand = self.lower_expression(operand_ref, true);
        let operand_ty = self.ast.get_resolved_type(operand_ref).unwrap();
        let mir_ty = self.lower_qual_type(operand_ty);

        if self.ast.get_value_category(operand_ref) != Some(ValueCategory::LValue) {
            panic!("Inc/Dec operand must be an lvalue");
        }

        let place = if let Operand::Copy(place) = operand.clone() {
            place
        } else {
            panic!("Inc/Dec operand is not a place");
        };

        // If it's post-inc/dec and we need the value, save the old value
        let old_value = if is_post && need_value {
            let rval = Rvalue::Use(operand.clone());
            let (_, temp_place) = self.create_temp_local_with_assignment(rval, mir_ty);
            Some(Operand::Copy(Box::new(temp_place)))
        } else {
            None
        };

        // Determine MIR operation and Rvalue
        let rval = self.create_inc_dec_rvalue(operand.clone(), operand_ty, is_inc);

        // Perform the assignment
        if is_post && !need_value {
            // Optimization: assign directly to place if old value not needed
            self.mir_builder.add_statement(MirStmt::Assign(*place.clone(), rval));
        } else {
            // If we needed old value (is_post), or if it is pre-inc (need new value),
            // we compute to a temp first to ensure correctness and return the right value.
            let (_, new_place) = self.create_temp_local_with_assignment(rval, mir_ty);
            self.emit_assignment(*place.clone(), Operand::Copy(Box::new(new_place.clone())));

            if !is_post {
                // Pre-inc: return the new value
                return Operand::Copy(Box::new(new_place));
            }
        }

        if is_post {
            if need_value {
                old_value.unwrap()
            } else {
                self.create_int_operand(0)
            }
        } else {
            // Pre-inc: we already returned inside the block above.
            // RE-FETCH from place as a fallback (should not be reached)
            Operand::Copy(place)
        }
    }

    pub(crate) fn create_inc_dec_rvalue(&mut self, operand: Operand, operand_ty: QualType, is_inc: bool) -> Rvalue {
        let one_const = self.create_int_operand(1);
        let minus_one_const = self.create_int_operand(-1);

        if operand_ty.is_pointer() {
            let op = if is_inc { BinaryOp::Add } else { BinaryOp::Sub };
            self.create_pointer_arithmetic_rvalue(operand, one_const, op)
        } else {
            let mir_ty_id = self.lower_qual_type(operand_ty);
            let mir_ty = self.mir_builder.get_type(mir_ty_id);

            if mir_ty.is_float() {
                let val = if is_inc { 1.0 } else { -1.0 };
                let const_val = self.create_constant(mir_ty_id, ConstValueKind::Float(val));
                let rhs = Operand::Constant(const_val);
                Rvalue::BinaryFloatOp(crate::mir::BinaryFloatOp::Add, operand, rhs)
            } else {
                // For Integers: Add(delta) (Note: we use Add with negative delta for decrement
                // to support proper wrapping arithmetic and fix previous bugs)
                let rhs = if is_inc { one_const } else { minus_one_const };
                Rvalue::BinaryIntOp(BinaryIntOp::Add, operand, rhs)
            }
        }
    }

    pub(crate) fn create_pointer_arithmetic_rvalue(&mut self, lhs: Operand, rhs: Operand, op: BinaryOp) -> Rvalue {
        match op {
            BinaryOp::Add => Rvalue::PtrAdd(lhs, rhs),
            BinaryOp::Sub => Rvalue::PtrSub(lhs, rhs),
            _ => panic!("Invalid pointer arithmetic op"),
        }
    }

    pub(crate) fn lower_builtin_va_arg(&mut self, ty: QualType, expr_ref: NodeRef) -> Operand {
        let ap = self.lower_expression_as_place(expr_ref);
        let mir_ty = self.lower_qual_type(ty);
        let rval = Rvalue::BuiltinVaArg(ap, mir_ty);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    pub(crate) fn lower_builtin_void(&mut self, kind: &NodeKind) -> Operand {
        let stmt = match kind {
            NodeKind::BuiltinVaStart(ap_ref, last_ref) => {
                let ap = self.lower_expression_as_place(*ap_ref);
                let last = self.lower_expression(*last_ref, true);
                MirStmt::BuiltinVaStart(ap, last)
            }
            NodeKind::BuiltinVaEnd(ap_ref) => {
                let ap = self.lower_expression_as_place(*ap_ref);
                MirStmt::BuiltinVaEnd(ap)
            }
            NodeKind::BuiltinVaCopy(dst_ref, src_ref) => {
                let dst = self.lower_expression_as_place(*dst_ref);
                let src = self.lower_expression_as_place(*src_ref);
                MirStmt::BuiltinVaCopy(dst, src)
            }
            _ => unreachable!(),
        };
        self.mir_builder.add_statement(stmt);
        self.create_int_operand(0)
    }

    pub(crate) fn lower_atomic_op(
        &mut self,
        op: AtomicOp,
        args_start: NodeRef,
        args_len: u16,
        mir_ty: TypeId,
    ) -> Operand {
        let args = self.get_atomic_args(args_start, args_len);
        let order = AtomicMemOrder::SeqCst; // Default to SeqCst for now

        match op {
            AtomicOp::LoadN => {
                let ptr = args[0].clone();
                // args[1] is memorder, ignored
                let rval = Rvalue::AtomicLoad(ptr, order);
                self.emit_rvalue_to_operand(rval, mir_ty)
            }
            AtomicOp::StoreN => {
                let ptr = args[0].clone();
                let val = args[1].clone();
                // args[2] is memorder, ignored
                self.mir_builder.add_statement(MirStmt::AtomicStore(ptr, val, order));
                self.create_dummy_operand()
            }
            AtomicOp::ExchangeN => {
                let ptr = args[0].clone();
                let val = args[1].clone();
                // args[2] is memorder, ignored
                let rval = Rvalue::AtomicExchange(ptr, val, order);
                self.emit_rvalue_to_operand(rval, mir_ty)
            }
            AtomicOp::CompareExchangeN => self.lower_atomic_cmpxchg(&args, order, mir_ty),
            AtomicOp::FetchAdd => self.lower_atomic_fetch_op(BinaryIntOp::Add, &args, order, mir_ty),
            AtomicOp::FetchSub => self.lower_atomic_fetch_op(BinaryIntOp::Sub, &args, order, mir_ty),
            AtomicOp::FetchAnd => self.lower_atomic_fetch_op(BinaryIntOp::BitAnd, &args, order, mir_ty),
            AtomicOp::FetchOr => self.lower_atomic_fetch_op(BinaryIntOp::BitOr, &args, order, mir_ty),
            AtomicOp::FetchXor => self.lower_atomic_fetch_op(BinaryIntOp::BitXor, &args, order, mir_ty),
        }
    }

    fn get_atomic_args(&mut self, args_start: NodeRef, args_len: u16) -> Vec<Operand> {
        args_start
            .range(args_len)
            .map(|arg_ref| self.lower_expression(arg_ref, true))
            .collect()
    }

    fn lower_atomic_cmpxchg(&mut self, args: &[Operand], order: AtomicMemOrder, mir_ty: TypeId) -> Operand {
        let ptr = args[0].clone();
        let expected_ptr = args[1].clone();
        let desired = args[2].clone();
        // args[3] weak, args[4] success, args[5] failure (ignored side effects were handled by lowering args)

        let expected_place = match expected_ptr {
            Operand::Copy(p) => Place::Deref(Box::new(Operand::Copy(p))),
            _ => Place::Deref(Box::new(expected_ptr)),
        };
        let expected_val_op = Operand::Copy(Box::new(expected_place.clone()));

        let weak = false;
        let cas_rval = Rvalue::AtomicCompareExchange(ptr, expected_val_op.clone(), desired.clone(), weak, order, order);

        let val_ty = self.get_operand_type(&desired);
        let (_, old_val_place) = self.create_temp_local_with_assignment(cas_rval, val_ty);
        let old_val = Operand::Copy(Box::new(old_val_place));

        let mir_type_info = self.mir_builder.get_type(val_ty);
        let cmp_rval = if mir_type_info.is_float() {
            Rvalue::BinaryFloatOp(crate::mir::BinaryFloatOp::Eq, old_val.clone(), expected_val_op)
        } else {
            Rvalue::BinaryIntOp(BinaryIntOp::Eq, old_val.clone(), expected_val_op)
        };

        let (_, success_place) = self.create_temp_local_with_assignment(cmp_rval, mir_ty);
        let success_op = Operand::Copy(Box::new(success_place));

        let update_block = self.mir_builder.create_block();
        let end_block = self.mir_builder.create_block();

        self.mir_builder
            .set_terminator(Terminator::If(success_op.clone(), end_block, update_block));

        self.mir_builder.set_current_block(update_block);
        self.mir_builder
            .add_statement(MirStmt::Assign(expected_place, Rvalue::Use(old_val)));
        self.mir_builder.set_terminator(Terminator::Goto(end_block));

        self.mir_builder.set_current_block(end_block);
        success_op
    }

    fn lower_atomic_fetch_op(
        &mut self,
        bin_op: BinaryIntOp,
        args: &[Operand],
        order: AtomicMemOrder,
        mir_ty: TypeId,
    ) -> Operand {
        let ptr = args[0].clone();
        let val = args[1].clone();
        // args[2] memorder

        let rval = Rvalue::AtomicFetchOp(bin_op, ptr, val, order);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    fn lower_complex_binary_op(&mut self, op: &BinaryOp, lhs: Operand, rhs: Operand, mir_ty: TypeId) -> Operand {
        let lhs_ty = self.get_operand_type(&lhs);
        let rhs_ty = self.get_operand_type(&rhs);

        let (lhs_real, lhs_imag) = self.get_complex_components(lhs, lhs_ty);
        let (rhs_real, rhs_imag) = self.get_complex_components(rhs, rhs_ty);

        let element_ty = match self.mir_builder.get_type(lhs_ty) {
            crate::mir::MirType::Record { field_types, .. } => field_types[0],
            _ => panic!("Expected complex record type"),
        };

        use crate::mir::BinaryFloatOp::*;

        match op {
            BinaryOp::Add | BinaryOp::Sub => {
                let mir_op = if *op == BinaryOp::Add { Add } else { Sub };
                let res_real = self.emit_float_binop(mir_op, lhs_real, rhs_real, element_ty);
                let res_imag = self.emit_float_binop(mir_op, lhs_imag, rhs_imag, element_ty);
                self.emit_complex_struct(res_real, res_imag, mir_ty)
            }
            BinaryOp::Mul => {
                let ac = self.emit_float_binop(Mul, lhs_real.clone(), rhs_real.clone(), element_ty);
                let bd = self.emit_float_binop(Mul, lhs_imag.clone(), rhs_imag.clone(), element_ty);
                let real = self.emit_float_binop(Sub, ac, bd, element_ty);

                let ad = self.emit_float_binop(Mul, lhs_real, rhs_imag.clone(), element_ty);
                let bc = self.emit_float_binop(Mul, lhs_imag, rhs_real, element_ty);
                let imag = self.emit_float_binop(Add, ad, bc, element_ty);

                self.emit_complex_struct(real, imag, mir_ty)
            }
            BinaryOp::Div => {
                let cc = self.emit_float_binop(Mul, rhs_real.clone(), rhs_real.clone(), element_ty);
                let dd = self.emit_float_binop(Mul, rhs_imag.clone(), rhs_imag.clone(), element_ty);
                let denom = self.emit_float_binop(Add, cc, dd, element_ty);

                let ac = self.emit_float_binop(Mul, lhs_real.clone(), rhs_real.clone(), element_ty);
                let bd = self.emit_float_binop(Mul, lhs_imag.clone(), rhs_imag.clone(), element_ty);
                let num_real = self.emit_float_binop(Add, ac, bd, element_ty);
                let real = self.emit_float_binop(Div, num_real, denom.clone(), element_ty);

                let bc = self.emit_float_binop(Mul, lhs_imag, rhs_real, element_ty);
                let ad = self.emit_float_binop(Mul, lhs_real, rhs_imag, element_ty);
                let num_imag = self.emit_float_binop(Sub, bc, ad, element_ty);
                let imag = self.emit_float_binop(Div, num_imag, denom, element_ty);

                self.emit_complex_struct(real, imag, mir_ty)
            }
            BinaryOp::Equal | BinaryOp::NotEqual => {
                let bool_ty = self.lower_type(self.registry.type_bool);
                if *op == BinaryOp::Equal {
                    let real_eq = self.emit_float_binop(Eq, lhs_real, rhs_real, bool_ty);
                    let imag_eq = self.emit_float_binop(Eq, lhs_imag, rhs_imag, bool_ty);
                    self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitAnd, real_eq, imag_eq), mir_ty)
                } else {
                    let real_ne = self.emit_float_binop(Ne, lhs_real, rhs_real, bool_ty);
                    let imag_ne = self.emit_float_binop(Ne, lhs_imag, rhs_imag, bool_ty);
                    self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitOr, real_ne, imag_ne), mir_ty)
                }
            }
            _ => panic!("Unsupported complex binary operator: {:?}", op),
        }
    }

    fn lower_complex_unary_op(&mut self, op: &UnaryOp, operand_ref: NodeRef, mir_ty: TypeId) -> Operand {
        let operand = self.lower_expression(operand_ref, true);
        let operand_ty = self.get_operand_type(&operand);

        let (real, imag) = self.get_complex_components(operand, operand_ty);

        let element_ty = match self.mir_builder.get_type(operand_ty) {
            crate::mir::MirType::Record { field_types, .. } => field_types[0],
            _ => panic!("Expected complex record type"),
        };

        use crate::mir::UnaryFloatOp::*;

        match op {
            UnaryOp::Minus => {
                let res_real = self.emit_float_unop(Neg, real, element_ty);
                let res_imag = self.emit_float_unop(Neg, imag, element_ty);
                self.emit_complex_struct(res_real, res_imag, mir_ty)
            }
            UnaryOp::BitNot => {
                // conjugate
                let res_imag = self.emit_float_unop(Neg, imag, element_ty);
                self.emit_complex_struct(real, res_imag, mir_ty)
            }
            UnaryOp::LogicNot => {
                let zero = self.create_constant(element_ty, ConstValueKind::Float(0.0));
                let zero_op = Operand::Constant(zero);
                let bool_ty = self.lower_type(self.registry.type_bool);

                use crate::mir::BinaryFloatOp::Eq;
                let real_eq = self.emit_float_binop(Eq, real, zero_op.clone(), bool_ty);
                let imag_eq = self.emit_float_binop(Eq, imag, zero_op, bool_ty);
                self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitAnd, real_eq, imag_eq), mir_ty)
            }
            UnaryOp::Plus => self.emit_complex_struct(real, imag, mir_ty),
            _ => panic!("Unsupported complex unary operator: {:?}", op),
        }
    }

    /// Try to lower builtin float constant functions like `__builtin_inff`, `__builtin_nanf`, etc.
    /// Returns Some(Operand) if the call is a builtin float constant, None otherwise.
    fn try_lower_builtin_float_const(&mut self, call_expr: &ast::nodes::CallExpr, mir_ty: TypeId) -> Option<Operand> {
        // Check if callee is an identifier
        let callee_kind = self.ast.get_kind(call_expr.callee);
        let name = match callee_kind {
            NodeKind::Ident(name_id, _) => name_id.as_str(),
            _ => return None,
        };

        match name {
            "__builtin_inff" | "__builtin_huge_valf" => {
                let val = f32::INFINITY as f64;
                Some(self.create_float_operand(val, mir_ty))
            }
            "__builtin_inf" | "__builtin_huge_val" => {
                let val = f64::INFINITY;
                Some(self.create_float_operand(val, mir_ty))
            }
            "__builtin_nanf" => {
                let val = f32::NAN as f64;
                Some(self.create_float_operand(val, mir_ty))
            }
            "__builtin_nan" => {
                let val = f64::NAN;
                Some(self.create_float_operand(val, mir_ty))
            }
            _ => None,
        }
    }
}
