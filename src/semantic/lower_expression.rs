use crate::ast::{BinaryOp, NodeKind, NodeRef, UnaryOp};
use crate::mir::{
    BinaryIntOp, CallTarget, ConstValue, ConstValueKind, MirStmt, Operand, Place, Rvalue, Terminator, TypeId,
};
use crate::semantic::ast_to_mir::AstToMirLowerer;
use crate::semantic::const_eval::{ConstEvalCtx, eval_const_expr};
use crate::semantic::{QualType, SymbolKind, SymbolRef, TypeKind, ValueCategory};
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
        let node_kind = self.ast.get_kind(expr_ref).clone();

        let mir_ty = self.lower_qual_type(ty);

        // Attempt constant folding for arithmetic/logical operations that are not simple literals
        if matches!(
            node_kind,
            NodeKind::BinaryOp(..) | NodeKind::UnaryOp(..) | NodeKind::TernaryOp(..)
        ) {
            let ctx = ConstEvalCtx {
                ast: self.ast,
                symbol_table: self.symbol_table,
            };
            if let Some(val) = eval_const_expr(&ctx, expr_ref) {
                let ty_id = self.lower_qual_type(ty);
                return Operand::Constant(self.create_constant(ty_id, ConstValueKind::Int(val)));
            }
        }

        match &node_kind {
            NodeKind::LiteralInt(_)
            | NodeKind::LiteralFloat(_)
            | NodeKind::LiteralChar(_)
            | NodeKind::LiteralString(_) => self.lower_literal(&node_kind, ty).expect("Failed to lower literal"),
            NodeKind::Ident(_, symbol_ref) => self.lower_ident(*symbol_ref),
            NodeKind::UnaryOp(op, operand_ref) => self.lower_unary_op_expr(op, *operand_ref, mir_ty),
            NodeKind::PostIncrement(operand_ref) => self.lower_post_incdec(*operand_ref, true, need_value),
            NodeKind::PostDecrement(operand_ref) => self.lower_post_incdec(*operand_ref, false, need_value),
            NodeKind::BinaryOp(op, left_ref, right_ref) => self.lower_binary_op_expr(op, *left_ref, *right_ref, mir_ty),
            NodeKind::Assignment(op, left_ref, right_ref) => {
                self.lower_assignment_expr(expr_ref, op, *left_ref, *right_ref, mir_ty)
            }
            NodeKind::FunctionCall(call_expr) => {
                let temp_place = if need_value {
                    let (_, temp_place) = self.create_temp_local(mir_ty);
                    Some(temp_place)
                } else {
                    None
                };

                self.lower_function_call(call_expr, temp_place.clone());

                if need_value {
                    Operand::Copy(Box::new(temp_place.unwrap()))
                } else {
                    // dummy
                    self.create_dummy_operand()
                }
            }
            NodeKind::MemberAccess(obj_ref, field_name, is_arrow) => {
                self.lower_member_access(*obj_ref, field_name, *is_arrow)
            }
            NodeKind::IndexAccess(arr_ref, idx_ref) => self.lower_index_access(*arr_ref, *idx_ref),
            NodeKind::TernaryOp(cond, then, else_expr) => self.lower_ternary_op(*cond, *then, *else_expr, mir_ty),
            NodeKind::SizeOfExpr(expr) => self.lower_sizeof_expr(*expr),
            NodeKind::SizeOfType(ty) => self.lower_sizeof_type(ty),
            NodeKind::AlignOf(ty) => self.lower_alignof_type(ty),
            NodeKind::GenericSelection(gs) => self.lower_generic_selection(gs, need_value),
            NodeKind::GnuStatementExpression(_stmt, _) => {
                panic!("GnuStatementExpression not implemented");
            }
            NodeKind::Cast(_ty, operand_ref) => self.lower_cast(*operand_ref, mir_ty),
            NodeKind::CompoundLiteral(ty, init_ref) => self.lower_compound_literal(*ty, *init_ref),
            NodeKind::BuiltinVaArg(ty, expr) => self.lower_builtin_va_arg(*ty, *expr),
            NodeKind::BuiltinVaStart(ap, last) => self.lower_builtin_va_start(*ap, *last),
            NodeKind::BuiltinVaEnd(ap) => self.lower_builtin_va_end(*ap),
            NodeKind::BuiltinVaCopy(dst, src) => self.lower_builtin_va_copy(*dst, *src),
            NodeKind::InitializerList(_) | NodeKind::InitializerItem(_) => {
                // Should be lowered in context of assignment usually.
                panic!("InitializerList or InitializerItem not implemented");
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn lower_ternary_op(
        &mut self,
        cond: NodeRef,
        then_expr: NodeRef,
        else_expr: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        let cond_op = self.lower_expression(cond, true);

        let then_block = self.mir_builder.create_block();
        let else_block = self.mir_builder.create_block();
        let exit_block = self.mir_builder.create_block();

        self.mir_builder
            .set_terminator(Terminator::If(cond_op, then_block, else_block));

        // Result local
        let result_local = self.mir_builder.create_local(None, mir_ty, false);

        // Then
        self.mir_builder.set_current_block(then_block);
        let then_val = self.lower_expression(then_expr, true);
        let then_val_conv = self.apply_conversions(then_val, then_expr, mir_ty);
        self.emit_assignment(Place::Local(result_local), then_val_conv);
        self.mir_builder.set_terminator(Terminator::Goto(exit_block));

        // Else
        self.mir_builder.set_current_block(else_block);
        let else_val = self.lower_expression(else_expr, true);
        let else_val_conv = self.apply_conversions(else_val, else_expr, mir_ty);
        self.emit_assignment(Place::Local(result_local), else_val_conv);
        self.mir_builder.set_terminator(Terminator::Goto(exit_block));

        self.mir_builder.set_current_block(exit_block);

        Operand::Copy(Box::new(Place::Local(result_local)))
    }

    pub(crate) fn lower_sizeof_expr(&mut self, expr: NodeRef) -> Operand {
        let operand_ty = self
            .ast
            .get_resolved_type(expr)
            .expect("SizeOf operand type missing")
            .ty();
        self.lower_type_query(operand_ty, true)
    }

    pub(crate) fn lower_sizeof_type(&mut self, ty: &QualType) -> Operand {
        self.lower_type_query(ty.ty(), true)
    }

    pub(crate) fn lower_alignof_type(&mut self, ty: &QualType) -> Operand {
        self.lower_type_query(ty.ty(), false)
    }

    pub(crate) fn lower_type_query(&mut self, ty: semantic::TypeRef, is_size: bool) -> Operand {
        let layout = self.registry.get_layout(ty);
        let val = if is_size { layout.size } else { layout.alignment };
        self.create_int_operand(val as i64)
    }

    pub(crate) fn lower_generic_selection(
        &mut self,
        gs: &ast::nodes::GenericSelectionData,
        need_value: bool,
    ) -> Operand {
        let ctrl_ty = self
            .ast
            .get_resolved_type(gs.control)
            .expect("Controlling expr type missing")
            .ty();
        let unqualified_ctrl = self.registry.strip_all(QualType::unqualified(ctrl_ty));

        let mut selected_expr = None;
        let mut default_expr = None;

        for assoc_node_ref in gs.assoc_start.range(gs.assoc_len) {
            if let NodeKind::GenericAssociation(ga) = self.ast.get_kind(assoc_node_ref) {
                if let Some(ty) = ga.ty {
                    if self.registry.is_compatible(unqualified_ctrl, ty) {
                        selected_expr = Some(ga.result_expr);
                        break;
                    }
                } else {
                    default_expr = Some(ga.result_expr);
                }
            }
        }

        let expr_to_lower = selected_expr
            .or(default_expr)
            .expect("Generic selection failed (should be caught by Analyzer)");
        self.lower_expression(expr_to_lower, need_value)
    }

    pub(crate) fn lower_cast(&mut self, operand_ref: NodeRef, mir_ty: TypeId) -> Operand {
        let operand = self.lower_expression(operand_ref, true);
        Operand::Cast(mir_ty, Box::new(operand))
    }

    pub(crate) fn lower_literal(&mut self, node_kind: &NodeKind, ty: QualType) -> Option<Operand> {
        let mir_ty = self.lower_qual_type(ty);
        match node_kind {
            NodeKind::LiteralInt(val) => Some(Operand::Constant(
                self.create_constant(mir_ty, ConstValueKind::Int(*val)),
            )),
            NodeKind::LiteralFloat(val) => Some(self.create_float_operand(*val)),
            NodeKind::LiteralChar(val) => Some(Operand::Constant(
                self.create_constant(mir_ty, ConstValueKind::Int(*val as i64)),
            )),
            NodeKind::LiteralString(val) => Some(self.lower_literal_string(val, ty)),
            _ => None,
        }
    }

    pub(crate) fn lower_unary_op_expr(&mut self, op: &UnaryOp, operand_ref: NodeRef, mir_ty: TypeId) -> Operand {
        match op {
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => self.lower_pre_incdec(op, operand_ref),
            UnaryOp::AddrOf => self.lower_unary_addrof(operand_ref),
            UnaryOp::Deref => self.lower_unary_deref(operand_ref),
            UnaryOp::Plus => self.lower_expression(operand_ref, true),
            _ => {
                let operand = self.lower_expression(operand_ref, true);
                let operand_ty = self.get_operand_type(&operand);
                let mir_type_info = self.mir_builder.get_type(operand_ty);

                let rval = self.emit_unary_rvalue(op, operand, mir_type_info.is_float());
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

        let place = Place::Deref(Box::new(operand_converted));
        Operand::Copy(Box::new(place))
    }

    pub(crate) fn lower_ident(&mut self, resolved_ref: SymbolRef) -> Operand {
        let entry = self.symbol_table.get_symbol(resolved_ref);

        match &entry.kind {
            SymbolKind::Variable { is_global, .. } => {
                if *is_global {
                    // Global variables should have been lowered already if we are visiting in order.
                    let global_id = match self.global_map.get(&resolved_ref) {
                        Some(id) => id,
                        None => {
                            panic!(
                                "Global variable '{}' not found in MIR map. Visited? {:?}",
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
            SymbolKind::EnumConstant { value } => {
                self.create_int_operand(*value)
            }
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

        let lhs = self.lower_expression(left_ref, true);
        let rhs = self.lower_expression(right_ref, true);

        // Handle pointer arithmetic

        if let Some(rval) = self.lower_pointer_arithmetic(op, lhs.clone(), rhs.clone(), left_ref, right_ref) {
            return self.emit_rvalue_to_operand(rval, mir_ty);
        }

        // Apply implicit conversions from semantic info first to match AST
        let lhs_converted = self.apply_conversions(lhs, left_ref, mir_ty);
        let rhs_converted = self.apply_conversions(rhs, right_ref, mir_ty);

        // Ensure both operands have the same type for MIR operations.
        let lhs_mir_ty = self.get_operand_type(&lhs_converted);
        let rhs_mir_ty = self.get_operand_type(&rhs_converted);

        let (lhs_converted, rhs_converted) =
            self.unify_binary_operands(lhs_converted, rhs_converted, lhs_mir_ty, rhs_mir_ty);

        let lhs_final = self.ensure_explicit_cast(lhs_converted, left_ref);
        let rhs_final = self.ensure_explicit_cast(rhs_converted, right_ref);

        // Check types for correct MIR op
        let lhs_mir = self.mir_builder.get_type(lhs_mir_ty);

        if matches!(op, BinaryOp::Comma) {
            return rhs_final;
        }

        let rval = self.emit_binary_rvalue(op, lhs_final, rhs_final, lhs_mir.is_float());
        self.emit_rvalue_to_operand(rval, mir_ty)
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
        self.mir_builder.add_statement(MirStmt::Assign(
            res_place.clone(),
            Rvalue::Use(short_circuit_val),
        ));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        // 2. Evaluate RHS
        self.mir_builder.set_current_block(eval_rhs_block);
        let rhs_val = self.lower_condition(right_ref);

        let rhs_true_block = self.mir_builder.create_block();
        let rhs_false_block = self.mir_builder.create_block();

        self.mir_builder
            .set_terminator(Terminator::If(rhs_val, rhs_true_block, rhs_false_block));

        self.mir_builder.set_current_block(rhs_true_block);
        self.mir_builder.add_statement(MirStmt::Assign(
            res_place.clone(),
            Rvalue::Use(one_op),
        ));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        self.mir_builder.set_current_block(rhs_false_block);
        self.mir_builder.add_statement(MirStmt::Assign(
            res_place.clone(),
            Rvalue::Use(zero_op),
        ));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        // Merge
        self.mir_builder.set_current_block(merge_block);
        self.current_block = Some(merge_block);

        Operand::Copy(Box::new(res_place))
    }

    pub(crate) fn lower_pointer_arithmetic(
        &mut self,
        op: &BinaryOp,
        lhs: Operand,
        rhs: Operand,
        left_ref: NodeRef,
        right_ref: NodeRef,
    ) -> Option<Rvalue> {
        let lhs_type = self.ast.get_resolved_type(left_ref).unwrap();
        let rhs_type = self.ast.get_resolved_type(right_ref).unwrap();

        match op {
            BinaryOp::Add => {
                if lhs_type.is_pointer() {
                    let rhs_mir_ty = self.lower_qual_type(rhs_type);
                    let rhs_converted = self.apply_conversions(rhs, right_ref, rhs_mir_ty);
                    Some(Rvalue::PtrAdd(lhs, rhs_converted))
                } else if rhs_type.is_pointer() {
                    let lhs_mir_ty = self.lower_qual_type(lhs_type);
                    let lhs_converted = self.apply_conversions(lhs, left_ref, lhs_mir_ty);
                    Some(Rvalue::PtrAdd(rhs, lhs_converted))
                } else {
                    None
                }
            }
            BinaryOp::Sub => {
                if lhs_type.is_pointer() {
                    if rhs_type.is_pointer() {
                        Some(Rvalue::PtrDiff(lhs, rhs))
                    } else if rhs_type.is_integer() {
                        let rhs_mir_ty = self.lower_qual_type(rhs_type);
                        let rhs_converted = self.apply_conversions(rhs, right_ref, rhs_mir_ty);
                        Some(Rvalue::PtrSub(lhs, rhs_converted))
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
        let lhs_op = self.lower_expression(left_ref, true);

        // Ensure the LHS is a place. If not, this is a semantic error.
        if self.ast.get_value_category(left_ref) != Some(ValueCategory::LValue) {
            panic!("LHS of assignment must be an lvalue");
        }

        let place = if let Operand::Copy(place) = lhs_op {
            *place
        } else {
            panic!("LHS of assignment lowered to non-place operand despite being LValue");
        };

        let rhs_op = self.lower_expression(right_ref, true);

        let final_rhs = if let Some(compound_op) = op.without_assignment() {
            // This is a compound assignment, e.g., a += b
            // Use the already-evaluated place to read the current value.
            let lhs_copy = Operand::Copy(Box::new(place.clone()));

            if let Some(rval) =
                self.lower_pointer_arithmetic(&compound_op, lhs_copy.clone(), rhs_op.clone(), left_ref, right_ref)
            {
                self.emit_rvalue_to_operand(rval, mir_ty)
            } else {
                let lhs_converted_for_op = self.apply_conversions(lhs_copy, left_ref, mir_ty);
                let rhs_converted_for_op = self.apply_conversions(rhs_op, right_ref, mir_ty);

                let lhs_ty_for_op = self.get_operand_type(&lhs_converted_for_op);
                let mir_type_info = self.mir_builder.get_type(lhs_ty_for_op);

                let rval = self.emit_binary_rvalue(
                    &compound_op,
                    lhs_converted_for_op,
                    rhs_converted_for_op,
                    mir_type_info.is_float(),
                );
                let result_of_op = self.emit_rvalue_to_operand(rval, lhs_ty_for_op);
                self.apply_conversions(result_of_op, node_ref, mir_ty)
            }
        } else {
            // Simple assignment, just use the RHS
            self.apply_conversions(rhs_op, right_ref, mir_ty)
        };

        self.emit_assignment(place, final_rhs.clone());
        final_rhs // C assignment expressions evaluate to the assigned value
    }

    pub(crate) fn lower_function_call(&mut self, call_expr: &ast::nodes::CallExpr, dest_place: Option<Place>) {
        let callee = self.lower_expression(call_expr.callee, true);

        let mut arg_operands = Vec::new();

        // Get the function type to determine parameter types for conversions
        let func_node_kind = self.ast.get_kind(call_expr.callee);
        let func_type = if let NodeKind::Ident(_, symbol_ref) = func_node_kind {
            let resolved_symbol = *symbol_ref;
            let func_entry = self.symbol_table.get_symbol(resolved_symbol);
            Some(self.registry.get(func_entry.type_info.ty()))
        } else {
            None
        };

        let param_types = if let Some(func_type) = func_type {
            if let TypeKind::Function { parameters, .. } = &func_type.kind {
                Some(
                    parameters
                        .iter()
                        .map(|param| self.lower_qual_type(param.param_type))
                        .collect::<Vec<_>>(),
                )
            } else {
                None
            }
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

    pub(crate) fn find_member_path(&self, record_ty: semantic::TypeRef, field_name: ast::NameId) -> Option<Vec<usize>> {
        let ty = self.registry.get(record_ty);
        if let TypeKind::Record { members, .. } = &ty.kind {
            // 1. Check direct members
            if let Some(idx) = members.iter().position(|m| m.name == Some(field_name)) {
                return Some(vec![idx]);
            }

            // 2. Check anonymous members
            for (idx, member) in members.iter().enumerate() {
                if member.name.is_none() {
                    let member_ty = member.member_type.ty();
                    // Only recurse if it's a record
                    if matches!(self.registry.get(member_ty).kind, TypeKind::Record { .. })
                        && let Some(mut sub_path) = self.find_member_path(member_ty, field_name)
                    {
                        let mut full_path = vec![idx];
                        full_path.append(&mut sub_path);
                        return Some(full_path);
                    }
                }
            }
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
                let deref_op = Operand::Copy(Box::new(current_place));
                current_place = Place::Deref(Box::new(deref_op));
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

    pub(crate) fn lower_inc_dec_common(
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

        if let Operand::Copy(place) = operand.clone() {
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
        } else {
            panic!("Inc/Dec operand is not a place");
        }
    }

    pub(crate) fn create_inc_dec_rvalue(&mut self, operand: Operand, operand_ty: QualType, is_inc: bool) -> Rvalue {
        let one_const = self.create_int_operand(1);
        let minus_one_const = self.create_int_operand(-1);

        if operand_ty.is_pointer() {
            if is_inc {
                Rvalue::PtrAdd(operand, one_const)
            } else {
                Rvalue::PtrSub(operand, one_const)
            }
        } else {
            // For Integers: Add(delta) (Note: we use Add with negative delta for decrement
            // to support proper wrapping arithmetic and fix previous bugs)
            let rhs = if is_inc { one_const } else { minus_one_const };
            Rvalue::BinaryIntOp(BinaryIntOp::Add, operand, rhs)
        }
    }

    pub(crate) fn lower_pre_incdec(&mut self, op: &UnaryOp, lhs_ref: NodeRef) -> Operand {
        let is_inc = matches!(op, UnaryOp::PreIncrement);
        self.lower_inc_dec_common(lhs_ref, is_inc, false, true)
    }

    pub(crate) fn lower_post_incdec(&mut self, operand_ref: NodeRef, is_inc: bool, need_value: bool) -> Operand {
        self.lower_inc_dec_common(operand_ref, is_inc, true, need_value)
    }

    pub(crate) fn lower_builtin_va_arg(&mut self, ty: QualType, expr_ref: NodeRef) -> Operand {
        let ap = self.lower_expression_as_place(expr_ref);
        let mir_ty = self.lower_qual_type(ty);
        let rval = Rvalue::BuiltinVaArg(ap, mir_ty);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    pub(crate) fn lower_builtin_va_start(&mut self, ap_ref: NodeRef, last_ref: NodeRef) -> Operand {
        let ap = self.lower_expression_as_place(ap_ref);
        let last = self.lower_expression(last_ref, true);
        self.mir_builder.add_statement(MirStmt::BuiltinVaStart(ap, last));
        self.create_int_operand(0)
    }

    pub(crate) fn lower_builtin_va_end(&mut self, ap_ref: NodeRef) -> Operand {
        let ap = self.lower_expression_as_place(ap_ref);
        self.mir_builder.add_statement(MirStmt::BuiltinVaEnd(ap));
        self.create_int_operand(0)
    }

    pub(crate) fn lower_builtin_va_copy(&mut self, dst_ref: NodeRef, src_ref: NodeRef) -> Operand {
        let dst = self.lower_expression_as_place(dst_ref);
        let src = self.lower_expression_as_place(src_ref);

        self.mir_builder.add_statement(MirStmt::BuiltinVaCopy(dst, src));
        self.create_int_operand(0)
    }
}
