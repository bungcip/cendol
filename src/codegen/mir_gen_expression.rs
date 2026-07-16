use crate::ast::literal::LitVal;
use crate::ast::nodes::AtomicOp;
use crate::ast::{BinaryOp, CallExpr, NameId, NodeKind, NodeRef, StorageClass, UnaryOp};
use crate::codegen::mir_gen::MirGen;
use crate::codegen::mir_gen_ops;
use crate::mir::{
    AtomicMemOrder, BinaryFloatOp, BinaryIntOp, BitFieldInfo, CallTarget, ConstValue, ConstValueKind, MirBlockId,
    MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId, UnaryFloatOp, UnaryIntOp,
};

use crate::ast;
use crate::semantic::{
    ArraySizeType, BuiltinFunctionKind, Conversion, QualType, SymbolKind, SymbolRef, TypeKind, TypeQualifiers, TypeRef,
    ValueCategory,
};

impl<'a> MirGen<'a> {
    pub(crate) fn visit_expression_as_place(&mut self, expr: NodeRef) -> Place {
        let node_kind = self.ast.get_kind(expr);
        match node_kind {
            NodeKind::Ident(_, sym) => {
                let op = self.visit_ident(*sym);
                if let Operand::Copy(p) = op {
                    *p
                } else {
                    self.ensure_place_fallback(op, expr)
                }
            }
            NodeKind::MemberAccess(obj, field_name, is_arrow) => {
                self.visit_member_access_as_place(*obj, *field_name, *is_arrow)
            }
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access_as_place(*arr, *idx),
            NodeKind::UnaryOp(UnaryOp::Deref, operand) => {
                let op = self.visit_expression(*operand, true);
                let op_ty = self.ast.qual_type_of(*operand);
                let mir_ty = self.lower_qual_type(op_ty);
                let conv = self.apply_conversions(op, *operand, mir_ty);
                self.deref_operand(conv)
            }
            NodeKind::UnaryOp(UnaryOp::Real, operand) => {
                let base_place = self.visit_expression_as_place(*operand);
                let operand_ty = self.ast.qual_type_of(*operand);
                if operand_ty.is_complex() {
                    Place::StructField(Box::new(base_place), 0, None)
                } else {
                    base_place
                }
            }
            NodeKind::UnaryOp(UnaryOp::Imag, operand) => {
                let base_place = self.visit_expression_as_place(*operand);
                let operand_ty = self.ast.qual_type_of(*operand);
                if operand_ty.is_complex() {
                    Place::StructField(Box::new(base_place), 1, None)
                } else {
                    let op = self.visit_expression(expr, true);
                    self.ensure_place_fallback(op, expr)
                }
            }
            _ => {
                let op = self.visit_expression(expr, true);
                self.ensure_place_fallback(op, expr)
            }
        }
    }

    fn ensure_place_fallback(&mut self, op: Operand, expr: NodeRef) -> Place {
        let ty = self.ast.qual_type_of(expr);
        let mir_ty = self.lower_qual_type(ty);
        self.ensure_place(op, mir_ty)
    }

    pub(crate) fn visit_expression(&mut self, expr: NodeRef, need_value: bool) -> Operand {
        let qt = self.ast.qual_type_of(expr);
        let node_kind = *self.ast.get_kind(expr);
        let mir_ty = self.lower_qual_type(qt);

        if let Some(const_op) = self.try_constant_fold(expr, &node_kind, qt) {
            return if need_value {
                self.apply_conversions(const_op, expr, mir_ty)
            } else {
                const_op
            };
        }

        let operand = match &node_kind {
            NodeKind::Literal(_) => self.visit_literal(&node_kind, qt).expect("Failed to lower literal"),
            NodeKind::Ident(_, sym) => self.visit_ident(*sym),
            NodeKind::UnaryOp(op, operand) => self.visit_unary_op(*op, *operand, mir_ty),
            NodeKind::PostIncrement(operand) => self.visit_inc_dec_expr(*operand, true, true, need_value),
            NodeKind::PostDecrement(operand) => self.visit_inc_dec_expr(*operand, false, true, need_value),
            NodeKind::BinaryOp(op, left, right) => self.visit_binary_op(*op, *left, *right, mir_ty),
            NodeKind::Assignment(op, left, right) => self.visit_assignment_expr(*op, *left, *right, mir_ty),
            NodeKind::FunctionCall(call_expr) => {
                self.visit_function_call_expression(call_expr, expr, mir_ty, need_value)
            }
            NodeKind::LabelAddr(name, _) => self.visit_label_addr(*name, mir_ty),
            _ if node_kind.is_type_query() => self.visit_type_query_expression(&node_kind, expr, mir_ty, need_value),
            NodeKind::StatementExpr(stmt, result_expr) => self.visit_gnu_stmt_expr(*stmt, *result_expr, need_value),
            NodeKind::Cast(_ty, operand) => self.visit_cast(*operand, mir_ty),
            NodeKind::CompoundLiteral(ty, init) => self.visit_compound_literal(*ty, *init),
            _ if node_kind.is_builtin() => self.visit_builtin_expression(&node_kind, expr, mir_ty, need_value),
            NodeKind::MemberAccess(obj, field_name, is_arrow) => self.visit_member_access(*obj, *field_name, *is_arrow),
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(*arr, *idx),
            NodeKind::TernaryOp(cond, then, else_expr) => self.visit_ternary_op(*cond, *then, *else_expr, mir_ty),
            _ => unreachable!("Unhandled node kind in visit_expression: {:?}", node_kind),
        };

        if !need_value {
            return operand;
        }

        self.apply_conversions(operand, expr, mir_ty)
    }

    fn visit_function_call_expression(
        &mut self,
        call_expr: &CallExpr,
        expr: NodeRef,
        mir_ty: TypeId,
        need_value: bool,
    ) -> Operand {
        // Check for builtin functions that need special MIR lowering
        if let Some(builtin_op) = self.try_visit_builtin_call(call_expr, mir_ty, need_value) {
            return builtin_op;
        }

        // Check for builtin float constant functions
        if let Some(builtin_op) = self.try_visit_builtin_float_const(call_expr, mir_ty) {
            return if need_value {
                self.apply_conversions(builtin_op, expr, mir_ty)
            } else {
                builtin_op
            };
        }

        let is_void = self.mb.get_type(mir_ty).is_void();
        let temp_place = if need_value && !is_void {
            let (_, temp_place) = self.create_temp_local(mir_ty);
            Some(temp_place)
        } else {
            None
        };

        self.visit_function_call(call_expr, temp_place.clone());

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

    fn visit_type_query_expression(
        &mut self,
        node_kind: &NodeKind,
        expr: NodeRef,
        mir_ty: TypeId,
        need_value: bool,
    ) -> Operand {
        match node_kind {
            NodeKind::SizeOfExpr(inner_expr) => {
                let ty = self
                    .ast
                    .get_resolved_type(*inner_expr)
                    .expect("SizeOf operand type missing")
                    .ty();
                self.visit_type_query(ty, true)
            }
            NodeKind::SizeOfType(qt) => self.visit_type_query(qt.ty(), true),
            NodeKind::AlignOfType(qt) => self.visit_type_query(qt.ty(), false),
            NodeKind::AlignOfExpr(inner_expr) => {
                // If the expression is a direct reference to a variable, it might have a custom alignment.
                if let NodeKind::Ident(_, sym) = self.ast.get_kind(*inner_expr) {
                    let symbol = self.symbol_table.get_symbol(*sym);
                    if let SymbolKind::Variable(v) = &symbol.kind
                        && let Some(align) = v.alignment
                    {
                        let op = self.create_size_t_operand(align as u64);
                        return if need_value {
                            self.apply_conversions(op, expr, mir_ty)
                        } else {
                            op
                        };
                    }
                }

                let ty = self
                    .ast
                    .get_resolved_type(*inner_expr)
                    .expect("AlignOf operand type missing")
                    .ty();
                self.visit_type_query(ty, false)
            }
            _ => unreachable!(),
        }
    }

    fn visit_builtin_expression(
        &mut self,
        node_kind: &NodeKind,
        expr: NodeRef,
        mir_ty: TypeId,
        need_value: bool,
    ) -> Operand {
        match node_kind {
            NodeKind::BuiltinOffsetof(..) | NodeKind::BuiltinTypesCompatibleP(..) => {
                let val = self.const_ctx().eval_int(expr).expect("Builtin should be constant");
                let kind = if self.mb.get_type(mir_ty).is_float() {
                    ConstValueKind::Float(val as f64)
                } else {
                    ConstValueKind::Int(val)
                };
                Operand::Constant(self.create_constant(mir_ty, kind))
            }
            NodeKind::BuiltinChooseExpr(..) => self.visit_builtin_choose_expr(need_value, expr),
            NodeKind::GenericSelection(..) => self.visit_generic_selection(need_value, expr),
            NodeKind::BuiltinVaArg(ty, expr) => self.visit_builtin_va_arg(*ty, *expr),
            NodeKind::BuiltinComplex(real, imag) => {
                let real_op = self.visit_expression(*real, true);
                let imag_op = self.visit_expression(*imag, true);

                let _common_real_ty = match self.mb.get_type(mir_ty) {
                    MirType::Record { field_types, .. } => field_types[0],
                    _ => panic!("Expected complex record type"),
                };

                // Internal operands need their own conversions applied (since they are visited via visit_expression)
                // but the result structure itself doesn't have a record in semantic_info usually.
                self.emit_complex_struct(real_op, imag_op, mir_ty)
            }
            NodeKind::BuiltinBitCast(ty, expr) => {
                let operand = self.visit_expression(*expr, true);
                let target_mir_ty = self.lower_qual_type(*ty);
                Operand::Cast(target_mir_ty, Box::new(operand))
            }
            NodeKind::BuiltinConvertVector(expr, ty) => {
                let operand = self.visit_expression(*expr, true);
                let target_mir_ty = self.lower_qual_type(*ty);
                // For now, treat convertvector as a cast.
                // In the future, this might need a more specialized MIR op.
                Operand::Cast(target_mir_ty, Box::new(operand))
            }
            _ => unreachable!("Unhandled node kind in visit_builtin_expression: {:?}", node_kind),
        }
    }

    fn try_constant_fold(&mut self, expr: NodeRef, kind: &NodeKind, qt: QualType) -> Option<Operand> {
        // Attempt constant folding for arithmetic/logical operations that are not simple literals
        if !matches!(
            kind,
            NodeKind::BinaryOp(..)
                | NodeKind::UnaryOp(..)
                | NodeKind::TernaryOp(..)
                | NodeKind::Cast(..)
                | NodeKind::BuiltinComplex(..)
        ) {
            return None;
        }

        if let NodeKind::BuiltinComplex(real, imag) = kind
            && let (Some(rv), Some(iv)) = (self.const_ctx().eval_float(*real), self.const_ctx().eval_float(*imag))
        {
            let ty_id = self.lower_qual_type(qt);
            let MirType::Record { field_types, .. } = self.mb.get_type(ty_id) else {
                return None;
            };
            let elem_ty = field_types[0];
            let r_const = self.create_constant(elem_ty, ConstValueKind::Float(rv));
            let i_const = self.create_constant(elem_ty, ConstValueKind::Float(iv));
            return Some(Operand::Constant(self.create_constant(
                ty_id,
                ConstValueKind::StructLiteral(vec![(0, r_const), (1, i_const)]),
            )));
        }

        // Try floating-point constant folding first for float types
        if qt.is_floating() && !qt.is_complex() {
            if let Some(val) = self.const_ctx().eval_float(expr) {
                let ty_id = self.lower_qual_type(qt);
                return Some(Operand::Constant(
                    self.create_constant(ty_id, ConstValueKind::Float(val)),
                ));
            }
            return None;
        }

        // Integer constant folding
        if let Some(val) = self.const_ctx().eval_int(expr) {
            let ty_id = self.lower_qual_type(qt);
            let mir_type = self.mb.get_type(ty_id);
            let truncated_val = mir_type.truncate_int(val);
            return Some(Operand::Constant(
                self.create_constant(ty_id, ConstValueKind::Int(truncated_val)),
            ));
        }
        None
    }

    fn visit_gnu_stmt_expr(&mut self, stmt: NodeRef, result_expr: NodeRef, need_value: bool) -> Operand {
        let kind = self.ast.get_kind(stmt);
        if let NodeKind::CompoundStmt(cs) = kind {
            let old_scope = self.current_scope_id;
            self.current_scope_id = cs.scope_id;

            self.func_state_mut().scope_cleanup.push(Vec::new());

            for stmt in cs.stmt_start.range(cs.stmt_len) {
                let is_last_stmt_expr = if let NodeKind::ExpressionStmt(Some(e)) = self.ast.get_kind(stmt) {
                    *e == result_expr
                } else {
                    false
                };

                if is_last_stmt_expr {
                    continue;
                }

                let node_kind = self.ast.get_kind(stmt);
                if self.current_block_has_terminator() {
                    if let NodeKind::Label(..) = node_kind {
                        // OK
                    } else {
                        continue;
                    }
                }
                self.visit_node(stmt);
            }

            let mut op = if let NodeKind::Dummy = self.ast.get_kind(result_expr) {
                self.create_dummy_operand()
            } else {
                self.visit_expression(result_expr, need_value)
            };

            if need_value && self.has_any_cleanups() && !matches!(op, Operand::Constant(_)) {
                let mir_ty = self.get_operand_type(&op);
                op = self.emit_rvalue_to_operand(Rvalue::Use(op), mir_ty);
            }

            let cleanup = self.func_state_mut().scope_cleanup.pop().unwrap();
            if !self.current_block_has_terminator() {
                for action in cleanup.into_iter().rev() {
                    self.emit_cleanup(action);
                }
            }

            self.current_scope_id = old_scope;
            op
        } else {
            panic!("GnuStatementExpression stmt is not CompoundStatement");
        }
    }

    pub(crate) fn cast_operand_to_bool(&mut self, operand: Operand) -> Operand {
        let ty_id = self.get_operand_type(&operand);
        let bool_ty_id = self.lower_type(self.registry.type_bool);
        if ty_id == bool_ty_id {
            return operand;
        }

        if let Some(const_id) = self.operand_to_const_id(&operand) {
            let const_val = self.mb.get_constants().get(const_id.index()).unwrap().clone();

            let is_true = match const_val.kind {
                ConstValueKind::Int(val) => val != 0,
                ConstValueKind::Float(val) => val != 0.0,
                ConstValueKind::FunctionAddress(_) | ConstValueKind::GlobalAddress(_, _) => true,
                ConstValueKind::Bool(val) => val,
                ConstValueKind::Null => false,
                _ => return Operand::Cast(bool_ty_id, Box::new(operand)),
            };

            return Operand::Constant(
                self.create_constant(bool_ty_id, ConstValueKind::Int(if is_true { 1 } else { 0 })),
            );
        }

        Operand::Cast(bool_ty_id, Box::new(operand))
    }

    fn visit_ternary_op(&mut self, cond: NodeRef, then_expr: NodeRef, else_expr: NodeRef, mir_ty: TypeId) -> Operand {
        let is_void = matches!(self.mb.get_type(mir_ty), MirType::Void);

        let mut cond_op = self.visit_expression(cond, true);
        cond_op = self.cast_operand_to_bool(cond_op);

        let then_block = self.create_block();
        let else_block = self.create_block();
        let exit_block = self.create_block();

        self.set_terminator(Terminator::If(cond_op, then_block, else_block));

        // Result local
        let result_local = if !is_void {
            Some(self.create_local(None, mir_ty, false))
        } else {
            None
        };

        for (target_block, expr) in [(then_block, then_expr), (else_block, else_expr)] {
            self.set_current_block(target_block);
            let val = self.visit_expression(expr, !is_void);
            if let Some(local) = result_local {
                let val_conv = self.apply_conversions(val, expr, mir_ty);
                self.emit_assignment(Place::Local(local), val_conv);
            }
            self.set_terminator(Terminator::Goto(exit_block));
        }

        self.set_current_block(exit_block);

        if let Some(local) = result_local {
            Operand::Copy(Box::new(Place::Local(local)))
        } else {
            self.create_dummy_operand()
        }
    }

    pub(crate) fn visit_type_query(&mut self, ty: TypeRef, is_size: bool) -> Operand {
        if self.registry.is_variably_modified(ty) {
            if is_size {
                // sizeof(VLA) — compute dynamically
                return self.visit_sizeof_vla(ty);
            } else {
                // alignof(VLA) — alignment is determined statically by element type
                let type_info = self.registry.get(ty);
                if let TypeKind::Array { element_type, .. } = &type_info.kind {
                    let elem = *element_type;
                    let _ = self.registry.ensure_layout(elem);
                    let layout = self.registry.get_layout(elem);
                    return self.create_size_t_operand(layout.alignment as u64);
                }
            }
            return self.create_dummy_operand();
        }
        let _ = self.registry.ensure_layout(ty);
        let layout = self.registry.get_layout(ty);
        let val = if is_size { layout.size } else { layout.alignment as u64 };
        self.create_size_t_operand(val)
    }

    /// Compute sizeof(VLA) at runtime.
    fn visit_sizeof_vla(&mut self, ty: TypeRef) -> Operand {
        let type_info = self.registry.get(ty);
        if let TypeKind::Array {
            element_type,
            size: ArraySizeType::Variable(size_expr),
        } = &type_info.kind
        {
            let size_expr = *size_expr;
            let element_type = *element_type;

            // Get element size dynamically (the element type might itself be a VLA)
            let element_size_operand = self.visit_type_query(element_type, true);

            let size_t_mir_ty = self.get_size_t_type();

            // Evaluate the count expression at runtime
            let count_operand = self.visit_expression(size_expr, true);

            // Cast count to size_t if needed
            let count_ty = self.get_operand_type(&count_operand);
            let count_as_size_t = if count_ty != size_t_mir_ty {
                Operand::Cast(size_t_mir_ty, Box::new(count_operand))
            } else {
                count_operand
            };

            // total_size = count * element_size
            let rvalue = Rvalue::BinaryIntOp(BinaryIntOp::Mul, count_as_size_t, element_size_operand);
            self.emit_rvalue_to_operand(rvalue, size_t_mir_ty)
        } else {
            // Shouldn't happen, but fallback
            self.create_dummy_operand()
        }
    }

    fn visit_generic_selection(&mut self, need_value: bool, node: NodeRef) -> Operand {
        let expr_to_lower = self.ast.get_generic_selection(node);
        self.visit_expression(expr_to_lower, need_value)
    }

    fn visit_builtin_choose_expr(&mut self, need_value: bool, node: NodeRef) -> Operand {
        let expr_to_lower = self.ast.get_choose_expression(node);
        self.visit_expression(expr_to_lower, need_value)
    }

    fn visit_cast(&mut self, operand: NodeRef, mir_ty: TypeId) -> Operand {
        let is_void = self.mb.get_type(mir_ty).is_void();
        if is_void {
            self.visit_expression(operand, false);
            return self.create_dummy_operand();
        }
        let operand_op = self.visit_expression(operand, true);
        self.emit_cast(operand_op, mir_ty)
    }

    fn visit_literal(&mut self, node_kind: &NodeKind, ty: QualType) -> Option<Operand> {
        let mir_ty = self.lower_qual_type(ty);
        let NodeKind::Literal(literal_id) = node_kind else {
            return None;
        };

        literal_id.with_val(|val| {
            let const_kind = match val {
                LitVal::Int { value, .. } => ConstValueKind::Int(*value),
                LitVal::Char(val, _) => ConstValueKind::Int(*val as i64),
                LitVal::Nullptr => ConstValueKind::Null,
                LitVal::True => ConstValueKind::Bool(true),
                LitVal::False => ConstValueKind::Bool(false),
                lit @ LitVal::Float { suffix, .. } if suffix.is_imaginary() => {
                    let MirType::Record { field_types, .. } = self.mb.get_type(mir_ty) else {
                        unreachable!("Complex float must lower to a record type");
                    };
                    let elem_ty = field_types[0];
                    let zero = self.create_constant(elem_ty, ConstValueKind::Float(0.0));
                    let imag = self.create_constant(elem_ty, ConstValueKind::Float(lit.as_f64()));
                    ConstValueKind::StructLiteral(vec![(0, zero), (1, imag)])
                }
                lit @ LitVal::Float { .. } => ConstValueKind::Float(lit.as_f64()),
                LitVal::String { value, prefix } => return Some(self.visit_literal_string(value, *prefix, ty)),
            };

            Some(Operand::Constant(self.create_constant(mir_ty, const_kind)))
        })
    }

    fn visit_unary_op(&mut self, op: UnaryOp, expr: NodeRef, mir_ty: TypeId) -> Operand {
        let ty = self.ast.get_resolved_type(expr).unwrap();
        if ty.is_complex() && !matches!(op, UnaryOp::AddrOf | UnaryOp::Deref) {
            return self.visit_complex_unary_op(op, expr, mir_ty);
        }

        match op {
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                self.visit_inc_dec_expr(expr, op == UnaryOp::PreIncrement, false, true)
            }
            UnaryOp::AddrOf => self.visit_addrof(expr, mir_ty),
            UnaryOp::Deref => self.visit_unary_deref(expr),
            UnaryOp::Real => self.visit_expression(expr, true),
            UnaryOp::Imag => {
                let _ = self.visit_expression(expr, false);
                let kind = if self.mb.get_type(mir_ty).is_float() {
                    ConstValueKind::Float(0.0)
                } else {
                    ConstValueKind::Int(0)
                };
                Operand::Constant(self.create_constant(mir_ty, kind))
            }
            _ => {
                let operand = self.visit_expression(expr, true);
                let operand_ty = self.get_operand_type(&operand);
                let is_float = self.mb.get_type(operand_ty).is_float();
                if matches!(op, UnaryOp::LogicNot) && is_float {
                    let zero = Operand::Constant(self.create_constant(operand_ty, ConstValueKind::Float(0.0)));
                    let rval = Rvalue::BinaryFloatOp(BinaryFloatOp::Eq, operand, zero);
                    self.emit_rvalue_to_operand(rval, mir_ty)
                } else {
                    let rval = mir_gen_ops::emit_unary_rvalue(op, operand, is_float);
                    self.emit_rvalue_to_operand(rval, mir_ty)
                }
            }
        }
    }

    fn visit_addrof(&mut self, expr: NodeRef, mir_ty: TypeId) -> Operand {
        let operand = self.visit_expression(expr, true);

        match &operand {
            Operand::Copy(place) => {
                // Special case for VLA: &vla should evaluate to the value of the pointer local.
                if let Place::Local(local_id) = &**place
                    && self.func_state_mut().vla_map.values().any(|(ptr, _)| ptr == local_id)
                    && self.ast.qual_type_of(expr).is_array()
                {
                    return operand;
                }

                // Simplify &(*p) -> p
                if let Place::Deref(deref_op) = &**place {
                    return *deref_op.clone();
                }
            }
            Operand::Constant(_) => {
                // Function address constant usually has FunctionType, but &func results in Pointer(FunctionType).
                return if self.get_operand_type(&operand) != mir_ty {
                    self.emit_cast(operand, mir_ty)
                } else {
                    operand
                };
            }
            _ => {}
        }

        let place = match operand {
            Operand::Copy(place) => *place,
            _ => self.visit_expression_as_place(expr),
        };

        // Simplify &(*p) -> p (in case it came from visit_expression_as_place)
        if let Place::Deref(deref_op) = place {
            return *deref_op;
        }

        Operand::AddressOf(Box::new(place))
    }

    fn visit_unary_deref(&mut self, expr: NodeRef) -> Operand {
        let operand = self.visit_expression(expr, true);
        let place = self.deref_operand(operand);
        Operand::Copy(Box::new(place))
    }

    fn visit_ident(&mut self, sym: SymbolRef) -> Operand {
        let entry = self.symbol_table.get_symbol(sym);

        match &entry.kind {
            SymbolKind::Variable(v) => {
                let is_static_local = v.storage == Some(StorageClass::Static);
                if v.is_global || is_static_local {
                    let global_id = self.get_or_lower_global(sym);
                    Operand::Copy(Box::new(Place::Global(global_id)))
                } else if let Some(&(ptr_local_id, _)) = self.func_state_mut().vla_map.get(&sym) {
                    // For VLA, the identifier refers to the dynamically allocated memory.
                    let is_array = entry.type_info.is_array();
                    if is_array {
                        // Array refers to the base pointer directly.
                        Operand::Copy(Box::new(Place::Local(ptr_local_id)))
                    } else {
                        // Scalar fallback: Deref the pointer to get the value.
                        let ptr_op = Operand::Copy(Box::new(Place::Local(ptr_local_id)));
                        Operand::Copy(Box::new(Place::Deref(Box::new(ptr_op))))
                    }
                } else {
                    if let Some(&local_id) = self.func_state_mut().local_map.get(&sym) {
                        Operand::Copy(Box::new(Place::Local(local_id)))
                    } else {
                        // Local not found in current function state; fall back to global symbol.
                        // This avoids panics when lowering identifiers that may refer to
                        // file-scoped or otherwise externally-declared variables.
                        let global_id = self.get_or_lower_global(sym);
                        Operand::Copy(Box::new(Place::Global(global_id)))
                    }
                }
            }
            SymbolKind::Function(_) => {
                let func_id = self.get_or_declare_function(sym);
                let func_type = self.get_function_type(func_id);
                let func_ptr_type = self.mb.add_type(MirType::Pointer { pointee: func_type });
                Operand::Constant(self.create_constant(func_ptr_type, ConstValueKind::FunctionAddress(func_id)))
            }
            SymbolKind::EnumConstant { value } => self.create_int_operand(*value),
            _ => panic!("Unexpected symbol kind: {:?}", entry.kind),
        }
    }

    fn unify_binary_operands(
        &mut self,
        mut lhs: Operand,
        mut rhs: Operand,
        lhs_mir_ty: TypeId,
        rhs_mir_ty: TypeId,
    ) -> (Operand, Operand) {
        if lhs_mir_ty != rhs_mir_ty {
            let lhs_mir = self.mb.get_type(lhs_mir_ty);
            let rhs_mir = self.mb.get_type(rhs_mir_ty);

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

    fn visit_binary_op(&mut self, op: BinaryOp, left: NodeRef, right: NodeRef, mir_ty: TypeId) -> Operand {
        debug_assert!(
            !op.is_assignment(),
            "visit_binary_op called with assignment operator: {:?}",
            op
        );
        if matches!(op, BinaryOp::LogicAnd | BinaryOp::LogicOr) {
            return self.visit_logical_op(op, left, right, mir_ty);
        }

        if matches!(op, BinaryOp::Comma) {
            self.visit_expression(left, false);
            return self.visit_expression(right, true);
        }

        let lhs = self.visit_expression(left, true);
        let rhs = self.visit_expression(right, true);

        let (rval, _op_ty) = self.visit_binary_arithmetic_logic(op, lhs, rhs, left, right, mir_ty);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    fn visit_binary_arithmetic_logic(
        &mut self,
        op: BinaryOp,
        lhs: Operand,
        rhs: Operand,
        left_expr: NodeRef,
        right_expr: NodeRef,
        context_ty: TypeId,
    ) -> (Rvalue, TypeId) {
        // Handle pointer arithmetic
        if let Some(rval) = self.visit_pointer_arithmetic(op, lhs.clone(), rhs.clone(), left_expr, right_expr) {
            let res_ty = match &rval {
                Rvalue::PtrAdd(base, _) | Rvalue::PtrSub(base, _) => self.get_operand_type(base),
                Rvalue::PtrDiff(..) => self.lower_type(self.registry.type_long),
                _ => unreachable!(),
            };
            return (rval, res_ty);
        }

        let lhs_mir_ty = self.get_operand_type(&lhs);
        let rhs_mir_ty = self.get_operand_type(&rhs);

        let lhs_mir_type = self.mb.get_type(lhs_mir_ty);
        let rhs_mir_type = self.mb.get_type(rhs_mir_ty);

        let lhs_is_complex = lhs_mir_type.is_complex();
        let rhs_is_complex = rhs_mir_type.is_complex();

        if lhs_is_complex || rhs_is_complex {
            let op = self.visit_complex_binary_op(op, lhs, rhs, context_ty);
            return (Rvalue::Use(op), context_ty);
        }

        // Ensure both operands have the same type for MIR operations.
        let (lhs_unified, rhs_unified) = self.unify_binary_operands(lhs, rhs, lhs_mir_ty, rhs_mir_ty);

        let lhs_final = lhs_unified;
        let rhs_final = rhs_unified;

        let common_ty = self.get_operand_type(&lhs_final);

        let common_mir_type = self.mb.get_type(common_ty);
        let rval = mir_gen_ops::emit_binary_rvalue(op, lhs_final, rhs_final, common_mir_type.is_float());

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

    fn visit_bool_normalization(&mut self, value_op: Operand, result_place: Place, merge_block: MirBlockId) {
        let true_block = self.create_block();
        let false_block = self.create_block();

        self.set_terminator(Terminator::If(value_op, true_block, false_block));

        self.set_current_block(true_block);
        let one_op = self.create_int_operand(1);
        self.add_stmt(MirStmt::Assign(result_place.clone(), Rvalue::Use(one_op)));
        self.set_terminator(Terminator::Goto(merge_block));

        self.set_current_block(false_block);
        let zero_op = self.create_int_operand(0);
        self.add_stmt(MirStmt::Assign(result_place, Rvalue::Use(zero_op)));
        self.set_terminator(Terminator::Goto(merge_block));
    }

    fn visit_logical_op(&mut self, op: BinaryOp, left: NodeRef, right: NodeRef, mir_ty: TypeId) -> Operand {
        // Short-circuiting logic for && and ||
        let (_res_local, res_place) = self.create_temp_local(mir_ty);

        let eval_rhs_block = self.create_block();
        let merge_block = self.create_block();
        let short_circuit_block = self.create_block();

        // 1. Evaluate LHS
        let lhs_op = self.lower_condition(left);

        // Pre-create constants to avoid double borrow
        let zero_op = self.create_int_operand(0);
        let one_op = self.create_int_operand(1);

        let (short_circuit_val, true_target, false_target) = match op {
            BinaryOp::LogicAnd => (zero_op, eval_rhs_block, short_circuit_block),
            BinaryOp::LogicOr => (one_op, short_circuit_block, eval_rhs_block),
            _ => unreachable!(),
        };

        // if lhs { goto true_target } else { goto false_target }
        self.set_terminator(Terminator::If(lhs_op, true_target, false_target));

        // Short circuit case
        self.set_current_block(short_circuit_block);
        self.add_stmt(MirStmt::Assign(res_place.clone(), Rvalue::Use(short_circuit_val)));
        self.set_terminator(Terminator::Goto(merge_block));

        // 2. Evaluate RHS
        self.set_current_block(eval_rhs_block);
        let rhs_val = self.lower_condition(right);

        self.visit_bool_normalization(rhs_val, res_place.clone(), merge_block);

        // Merge
        self.set_current_block(merge_block);
        self.set_current_block(merge_block);

        Operand::Copy(Box::new(res_place))
    }

    fn unwrap_cast_if_int(&mut self, op: Operand) -> Operand {
        match op {
            Operand::Cast(ty, inner) => {
                let inner_ty = self.get_operand_type(&inner);
                if self.mb.get_type(inner_ty).is_int() {
                    return *inner;
                }

                let unwrapped = self.unwrap_cast_if_int(*inner);
                let unwrapped_ty = self.get_operand_type(&unwrapped);
                if self.mb.get_type(unwrapped_ty).is_int() {
                    unwrapped
                } else {
                    Operand::Cast(ty, Box::new(unwrapped))
                }
            }
            Operand::Constant(const_id) => {
                if let ConstValueKind::Int(val) = self.mb.get_constant(const_id).kind {
                    self.create_int_operand(val)
                } else {
                    Operand::Constant(const_id)
                }
            }
            _ => op,
        }
    }

    fn visit_pointer_arithmetic(
        &mut self,
        op: BinaryOp,
        lhs: Operand,
        rhs: Operand,
        left_expr: NodeRef,
        right_expr: NodeRef,
    ) -> Option<Rvalue> {
        // Lower types and apply conversions locally to check for pointer arithmetic
        // We use the operand's own type as the target for conversion to avoid forcing
        // implicit casts to the result type (which causes issues for Ptr + Int -> Ptr)
        let lhs_ty = self.ast.qual_type_of(left_expr);
        let rhs_ty = self.ast.qual_type_of(right_expr);

        let lhs_mir_target = self.lower_qual_type(lhs_ty);
        let rhs_mir_target = self.lower_qual_type(rhs_ty);

        let lhs_converted = self.apply_conversions(lhs, left_expr, lhs_mir_target);
        let rhs_converted = self.apply_conversions(rhs, right_expr, rhs_mir_target);

        let lhs_mir_ty = self.get_operand_type(&lhs_converted);
        let rhs_mir_ty = self.get_operand_type(&rhs_converted);

        let lhs_type_info = self.mb.get_type(lhs_mir_ty);
        let rhs_type_info = self.mb.get_type(rhs_mir_ty);

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

                    if self.mb.get_type(lhs_u_ty).is_pointer() && self.mb.get_type(rhs_u_ty).is_int() {
                        Some(self.create_pointer_arithmetic_rvalue(lhs_unwrapped, rhs_unwrapped, BinaryOp::Add))
                    } else if self.mb.get_type(rhs_u_ty).is_pointer() && self.mb.get_type(lhs_u_ty).is_int() {
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

                        if self.mb.get_type(rhs_u_ty_id).is_int() {
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

    fn visit_assignment_expr(&mut self, op: BinaryOp, left: NodeRef, right: NodeRef, mir_ty: TypeId) -> Operand {
        debug_assert!(
            op.is_assignment(),
            "visit_assignment_expr called with non-assignment operator: {:?}",
            op
        );

        // Ensure the LHS is a place. If not, this is a semantic error.
        if self.ast.get_value_category(left) != Some(ValueCategory::LValue) {
            panic!("LHS of assignment must be an lvalue");
        }

        // Use visit_expression_as_place to properly resolve the destination place
        let place = self.visit_expression_as_place(left);

        let rhs_op = self.visit_expression(right, true);

        let lhs_ty = self.ast.get_resolved_type(left).unwrap();

        if let Some(compound_op) = op.without_assignment() {
            self.visit_compound_assignment(compound_op, place, rhs_op, left, right, mir_ty)
        } else {
            // Simple assignment, just use the RHS
            if lhs_ty.is_atomic() {
                let ptr = Operand::AddressOf(Box::new(place.clone()));
                self.add_stmt(MirStmt::AtomicStore(ptr, rhs_op.clone(), AtomicMemOrder::SeqCst));
            } else {
                self.emit_assignment(place.clone(), rhs_op.clone());
            }

            // C11 6.5.16p3: An assignment expression has the value of the left operand after the assignment,
            // but is not an lvalue. For bit-fields, this means the value is truncated to the bit-field width.
            if let Place::StructField(.., Some(bit_info)) = &place {
                return self.apply_bitfield_truncation(rhs_op, bit_info, mir_ty);
            }

            rhs_op
        }
    }

    fn apply_bitfield_truncation(&mut self, op: Operand, bit_info: &BitFieldInfo, mir_ty: TypeId) -> Operand {
        if let Some(const_id) = self.operand_to_const_id(&op) {
            let constants = self.mb.get_constants();
            let const_val = constants.get(const_id.index()).unwrap().clone();
            if let ConstValueKind::Int(val) = const_val.kind {
                let truncated = bit_info.truncate(val);
                let new_const = self.mb.create_constant(mir_ty, ConstValueKind::Int(truncated));
                return Operand::Constant(new_const);
            }
        }

        // Non-constant: emit bitwise AND for unsigned, or shifts for signed
        if bit_info.is_signed && bit_info.width < 64 {
            // (val << (64-width)) >> (64-width)
            let shift = (64 - bit_info.width) as i64;
            let shift_op = {
                let c = self.mb.create_constant(mir_ty, ConstValueKind::Int(shift));
                Operand::Constant(c)
            };
            let lshift =
                self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::LShift, op, shift_op.clone()), mir_ty);
            self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::RShift, lshift, shift_op), mir_ty)
        } else {
            let mask = if bit_info.width == 64 {
                -1i64
            } else {
                ((1u64 << bit_info.width) - 1) as i64
            };
            let mask_op = {
                let c = self.mb.create_constant(mir_ty, ConstValueKind::Int(mask));
                Operand::Constant(c)
            };
            self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitAnd, op, mask_op), mir_ty)
        }
    }

    fn visit_compound_assignment(
        &mut self,
        compound_op: BinaryOp,
        place: Place,
        rhs_op: Operand,
        left: NodeRef,
        right: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        let lhs_ty = self.ast.get_resolved_type(left).unwrap();

        if lhs_ty.is_atomic() {
            let ptr = Operand::AddressOf(Box::new(place.clone()));
            let mir_op = match compound_op {
                BinaryOp::Add => Some(BinaryIntOp::Add),
                BinaryOp::Sub => Some(BinaryIntOp::Sub),
                BinaryOp::BitAnd => Some(BinaryIntOp::BitAnd),
                BinaryOp::BitOr => Some(BinaryIntOp::BitOr),
                BinaryOp::BitXor => Some(BinaryIntOp::BitXor),
                _ => None,
            };

            if let Some(op) = mir_op {
                let rval = Rvalue::AtomicFetchOp(op, ptr, rhs_op.clone(), AtomicMemOrder::SeqCst);
                let old_val = self.emit_rvalue_to_operand(rval, mir_ty);
                // AtomicFetchOp returns old value. Compound assignment evaluates to NEW value.
                // Re-apply operation to old value to get new value for the expression result.
                let (new_val_rval, _) =
                    self.visit_binary_arithmetic_logic(compound_op, old_val, rhs_op, left, right, mir_ty);
                return self.emit_rvalue_to_operand(new_val_rval, mir_ty);
            }
        }

        // This is a compound assignment, e.g., a += b
        // Use the already-evaluated place to read the current value.
        let lhs_copy = Operand::Copy(Box::new(place.clone()));

        let (rval, op_ty) = self.visit_binary_arithmetic_logic(compound_op, lhs_copy, rhs_op, left, right, mir_ty);
        let result_op = self.emit_rvalue_to_operand(rval, op_ty);

        let truncated_op = self.emit_cast(result_op, mir_ty);

        self.emit_assignment(place.clone(), truncated_op.clone());

        // C11 6.5.16p3: Bit-field truncation for compound assignment result
        if let Place::StructField(.., Some(bit_info)) = &place {
            self.apply_bitfield_truncation(truncated_op, bit_info, mir_ty)
        } else {
            truncated_op
        }
    }

    pub(super) fn emit_cast(&mut self, operand: Operand, target_ty: TypeId) -> Operand {
        if self.get_operand_type(&operand) == target_ty {
            return operand;
        }

        // Fold constant casts if types are compatible
        if let Some(const_id) = self.operand_to_const_id(&operand) {
            let const_val = self.mb.get_constant(const_id).clone();
            let mir_type = self.mb.get_type(target_ty);

            let is_compatible = match (&const_val.kind, mir_type) {
                (ConstValueKind::Int(_), t) => t.is_int() || t.is_pointer(),
                (ConstValueKind::Float(_), t) => t.is_float() || matches!(t, MirType::Bool),
                (ConstValueKind::GlobalAddress(_, _), t) => t.is_pointer() || t.is_int(),
                (ConstValueKind::FunctionAddress(_), t) => t.is_pointer() || t.is_int(),
                _ => false,
            };

            if is_compatible {
                let truncated_kind = match const_val.kind {
                    ConstValueKind::Int(val) => {
                        // C11 6.3.1.2-3: When converting to _Bool, the result is 0 if the value is 0, otherwise 1
                        if matches!(mir_type, MirType::Bool) {
                            ConstValueKind::Int(if val != 0 { 1 } else { 0 })
                        } else {
                            ConstValueKind::Int(mir_type.truncate_int(val))
                        }
                    }
                    ConstValueKind::FunctionAddress(_) | ConstValueKind::GlobalAddress(_, _)
                        if matches!(mir_type, MirType::Bool) =>
                    {
                        ConstValueKind::Int(1)
                    }
                    ConstValueKind::Float(val) => {
                        if matches!(mir_type, MirType::Bool) {
                            ConstValueKind::Int(if val != 0.0 { 1 } else { 0 })
                        } else if matches!(mir_type, MirType::F32) {
                            ConstValueKind::Float((val as f32) as f64)
                        } else {
                            ConstValueKind::Float(val)
                        }
                    }
                    kind => kind,
                };
                return Operand::Constant(self.create_constant(target_ty, truncated_kind));
            }
        }

        Operand::Cast(target_ty, Box::new(operand))
    }

    fn visit_function_call(&mut self, call_expr: &ast::nodes::CallExpr, dest_place: Option<Place>) {
        let callee = self.visit_expression(call_expr.callee, true);

        let arg_operands = self.visit_function_call_args(call_expr);

        let call_target = if let Operand::Constant(const_id) = callee {
            if let ConstValue {
                kind: ConstValueKind::FunctionAddress(func_id),
                ..
            } = self.mb.get_constants().get(const_id.index()).unwrap()
            {
                CallTarget::Direct(*func_id)
            } else {
                // Handle non-function-address constants (e.g. casted integers) as indirect calls
                CallTarget::Indirect(Operand::Constant(const_id))
            }
        } else {
            CallTarget::Indirect(callee)
        };

        let stmt = MirStmt::Call {
            target: call_target,
            args: arg_operands,
            dest: dest_place,
        };
        self.add_stmt(stmt);
    }

    fn visit_function_call_args(&mut self, call_expr: &ast::nodes::CallExpr) -> Vec<Operand> {
        let mut arg_operands = Vec::new();

        // Get the function type to determine parameter types for conversions
        let func_node_kind = self.ast.get_kind(call_expr.callee);
        // Bolt ⚡: Avoid cloning TypeKind. Extract parameter types directly.
        let param_types = if let NodeKind::Ident(_, sym) = func_node_kind {
            let symbol = *sym;
            let func_entry = self.symbol_table.get_symbol(symbol);
            let mut qt_params = None;
            {
                let type_info = self.registry.get(func_entry.type_info.ty());
                if let TypeKind::Function { parameters, .. } = &type_info.kind {
                    qt_params = Some(parameters.iter().map(|p| p.param_type).collect::<Vec<_>>());
                }
            }

            qt_params.map(|params| {
                params
                    .into_iter()
                    .map(|qt| self.lower_qual_type(qt))
                    .collect::<Vec<_>>()
            })
        } else {
            None
        };

        for (i, arg) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
            // Note: visit_expression(CallArg) will just lower the inner expression.
            // But we use arg(the CallArg node) for implicit conversion lookup.
            let arg_operand = self.visit_expression(arg, true);

            // Apply conversions for function arguments if needed
            // The resolved type of CallArg is same as inner expr.
            let arg_ty = self.ast.qual_type_of(arg);
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

            let converted_arg = self.apply_conversions(arg_operand, arg, target_mir_ty);

            arg_operands.push(converted_arg);
        }
        arg_operands
    }

    fn find_member_path(&self, record_ty: TypeRef, field_name: NameId) -> Option<Vec<usize>> {
        let mut base_index = 0;
        let ty = self.registry.get(record_ty);
        if let Some((_, idx)) = ty.find_member_recursive(self.registry, field_name, &mut base_index) {
            return Some(vec![idx]);
        }
        None
    }

    fn visit_member_access(&mut self, obj: NodeRef, field_name: NameId, is_arrow: bool) -> Operand {
        let current_place = self.visit_member_access_as_place(obj, field_name, is_arrow);
        Operand::Copy(Box::new(current_place))
    }

    fn visit_member_access_as_place(&mut self, obj: NodeRef, field_name: NameId, is_arrow: bool) -> Place {
        let mut obj_qt = self.ast.qual_type_of(obj);

        // Handle implicit conversions (like array-to-pointer decay) for arrow access
        let record_ty = if is_arrow {
            if let Some(conversions) = self.ast.semantic_info.conversions.get(&obj.index()) {
                for conv in conversions {
                    if let Conversion::PointerDecay { to } = conv {
                        obj_qt = QualType::unqualified(*to);
                    }
                }
            }
            self.registry
                .get_pointee(obj_qt.ty())
                .expect("ICE: Arrow access on non-pointer type")
                .ty()
        } else {
            obj_qt.ty()
        };

        if record_ty.is_record() == false {
            panic!("ICE: Member access on non-record type");
        }

        // Validate that the field exists and get its layout information
        let path = self
            .find_member_path(record_ty, field_name)
            .expect("ICE: Field not found - should be caught by semantic analysis");

        // Apply the chain of field accesses

        // Resolve base place
        let mut current_place = if is_arrow {
            let obj_op = self.visit_expression(obj, true);
            self.deref_operand(obj_op)
        } else {
            self.visit_expression_as_place(obj)
        };

        for field_idx in path {
            let struct_ty = self.get_place_type(&current_place);
            let mir_type = self.mb.get_type(struct_ty);
            let bit_info = if let MirType::Record { layout, .. } = mir_type {
                let field = &layout.fields[field_idx];
                field.bit_width.and_then(|w| {
                    field.bit_offset.map(|o| BitFieldInfo {
                        width: w,
                        offset: o,
                        storage_size: field.storage_size as u16,
                        is_signed: field.is_signed,
                    })
                })
            } else {
                None
            };
            current_place = Place::StructField(Box::new(current_place), field_idx, bit_info);
        }

        current_place
    }

    fn visit_index_access(&mut self, arr: NodeRef, idx: NodeRef) -> Operand {
        Operand::Copy(Box::new(self.visit_index_access_as_place(arr, idx)))
    }

    fn visit_index_access_as_place(&mut self, arr: NodeRef, idx: NodeRef) -> Place {
        let arr_ty = self.ast.qual_type_of(arr);
        let idx_ty = self.ast.qual_type_of(idx);

        // Handle both arr[idx] and idx[arr] (subscripting is commutative in C)
        // One must be a pointer/array, the other must be an integer
        let (sequence, index) = if arr_ty.is_array() || arr_ty.is_pointer() {
            (arr, idx)
        } else if idx_ty.is_array() || idx_ty.is_pointer() {
            (idx, arr)
        } else {
            panic!("ICE: Index access: neither operand is an array or pointer type");
        };

        // In C, arr[idx] is equivalent to *(arr + idx)
        // However, for global initialization, we prefer to stay as ArrayIndex if possible
        // to avoid emitting instructions (PtrAdd) that would require temporary locals.
        let arr_operand = if self.func_state.is_none() && arr_ty.is_array() {
            let p = self.visit_expression_as_place(sequence);
            Operand::Copy(Box::new(p))
        } else {
            self.visit_expression(sequence, true)
        };
        let idx_operand = self.visit_expression(index, true);

        // Check if the base operand is already a pointer in MIR (e.g., VLA locals stored as pointers)
        let arr_mir_ty = self.get_operand_type(&arr_operand);
        let arr_mir_type = self.mb.get_type(arr_mir_ty);
        if arr_mir_type.is_pointer() {
            // Pointer-based indexing: *(ptr + idx)
            let ptr_add = Rvalue::PtrAdd(arr_operand, idx_operand);
            let result_op = self.emit_rvalue_to_operand(ptr_add, arr_mir_ty);
            // Deref the resulting pointer
            self.deref_operand(result_op)
        } else {
            // Array-based indexing: use Place::ArrayIndex
            let arr_ty = self.ast.qual_type_of(sequence);
            let mir_ty = self.lower_qual_type(arr_ty);
            let arr_place = self.ensure_place(arr_operand, mir_ty);
            Place::ArrayIndex(Box::new(arr_place), Box::new(idx_operand))
        }
    }

    fn visit_inc_dec_expr(&mut self, expr: NodeRef, is_inc: bool, is_post: bool, need_value: bool) -> Operand {
        let operand = self.visit_expression(expr, true);
        let operand_ty = self.ast.get_resolved_type(expr).unwrap();
        let mir_ty = self.lower_qual_type(operand_ty);

        if self.ast.get_value_category(expr) != Some(ValueCategory::LValue) {
            panic!("Inc/Dec operand must be an lvalue");
        }

        let place = if let Operand::Copy(place) = operand {
            place
        } else {
            panic!("Inc/Dec operand is not a place");
        };

        if operand_ty.is_atomic() {
            return self.visit_atomic_inc_dec(expr, *place, mir_ty, is_inc, is_post);
        }

        // If it's post-inc/dec and we need the value, save the old value
        let old_value = if is_post && need_value {
            let rval = Rvalue::Use(Operand::Copy(place.clone()));
            let (_, temp_place) = self.create_temp_local_with_assignment(rval, mir_ty);
            Some(Operand::Copy(Box::new(temp_place)))
        } else {
            None
        };

        // Determine MIR operation and Rvalue
        let rval = self.create_inc_dec_rvalue(Operand::Copy(place.clone()), operand_ty, is_inc);

        // Perform the assignment
        if is_post && !need_value {
            // Optimization: assign directly to place if old value not needed
            self.add_stmt(MirStmt::Assign(*place.clone(), rval));
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
                self.create_dummy_operand()
            }
        } else {
            // Pre-inc: already returned
            Operand::Copy(place)
        }
    }

    fn visit_atomic_inc_dec(
        &mut self,
        expr: NodeRef,
        place: Place,
        mir_ty: TypeId,
        is_inc: bool,
        is_post: bool,
    ) -> Operand {
        let ptr = Operand::AddressOf(Box::new(place));
        let op = if is_inc { BinaryIntOp::Add } else { BinaryIntOp::Sub };
        let step = self.create_int_operand(1);
        let rval = Rvalue::AtomicFetchOp(op, ptr, step.clone(), AtomicMemOrder::SeqCst);
        let old_val = self.emit_rvalue_to_operand(rval, mir_ty);

        if is_post {
            old_val
        } else {
            let bin_op = if is_inc { BinaryOp::Add } else { BinaryOp::Sub };
            let (new_val_rval, _) = self.visit_binary_arithmetic_logic(bin_op, old_val, step, expr, expr, mir_ty);
            self.emit_rvalue_to_operand(new_val_rval, mir_ty)
        }
    }

    fn create_inc_dec_rvalue(&mut self, operand: Operand, operand_ty: QualType, is_inc: bool) -> Rvalue {
        let one_const = self.create_int_operand(1);
        let minus_one_const = self.create_int_operand(-1);

        if operand_ty.is_pointer() {
            let op = if is_inc { BinaryOp::Add } else { BinaryOp::Sub };
            self.create_pointer_arithmetic_rvalue(operand, one_const, op)
        } else if operand_ty.is_complex() {
            let mir_ty = self.lower_qual_type(operand_ty);
            let (real, imag) = self.get_complex_components(operand, mir_ty);
            let element_ty = match self.mb.get_type(mir_ty) {
                MirType::Record { field_types, .. } => field_types[0],
                _ => unreachable!("Complex type must be a record"),
            };

            let op = if is_inc { BinaryFloatOp::Add } else { BinaryFloatOp::Sub };
            let one = self.create_constant(element_ty, ConstValueKind::Float(1.0));
            let res_real = self.emit_float_binop(op, real, Operand::Constant(one), element_ty);

            Rvalue::StructLiteral(vec![(0, res_real), (1, imag)])
        } else {
            let mir_ty_id = self.lower_qual_type(operand_ty);
            let mir_ty = self.mb.get_type(mir_ty_id);

            if mir_ty.is_float() {
                let val = if is_inc { 1.0 } else { -1.0 };
                let const_val = self.create_constant(mir_ty_id, ConstValueKind::Float(val));
                let rhs = Operand::Constant(const_val);
                Rvalue::BinaryFloatOp(BinaryFloatOp::Add, operand, rhs)
            } else {
                // For Integers: Add(delta) (Note: we use Add with negative delta for decrement
                // to support proper wrapping arithmetic and fix previous bugs)
                let rhs = if is_inc { one_const } else { minus_one_const };
                Rvalue::BinaryIntOp(BinaryIntOp::Add, operand, rhs)
            }
        }
    }

    fn create_pointer_arithmetic_rvalue(&mut self, lhs: Operand, rhs: Operand, op: BinaryOp) -> Rvalue {
        match op {
            BinaryOp::Add => Rvalue::PtrAdd(lhs, rhs),
            BinaryOp::Sub => Rvalue::PtrSub(lhs, rhs),
            _ => panic!("Invalid pointer arithmetic op"),
        }
    }

    fn ensure_valist_place(&mut self, op: Operand) -> Place {
        let ty_id = self.get_operand_type(&op);
        let ty = self.mb.get_type(ty_id);

        if ty.is_aggregate() {
            self.ensure_place(op, ty_id)
        } else {
            self.deref_operand(op)
        }
    }

    fn visit_builtin_va_arg(&mut self, qt: QualType, expr: NodeRef) -> Operand {
        let ap_op = self.visit_expression(expr, true);
        let ap = self.ensure_valist_place(ap_op);
        let mir_ty = self.lower_qual_type(qt);
        let rval = Rvalue::BuiltinVaArg(ap, mir_ty);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    fn visit_atomic_op(&mut self, op: AtomicOp, args_start: NodeRef, args_len: u16, mir_ty: TypeId) -> Operand {
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
                self.add_stmt(MirStmt::AtomicStore(ptr, val, order));
                self.create_dummy_operand()
            }
            AtomicOp::ThreadFence => {
                self.add_stmt(MirStmt::AtomicThreadFence(order));
                self.create_dummy_operand()
            }
            AtomicOp::ExchangeN => {
                let ptr = args[0].clone();
                let val = args[1].clone();
                // args[2] is memorder, ignored
                let rval = Rvalue::AtomicExchange(ptr, val, order);
                self.emit_rvalue_to_operand(rval, mir_ty)
            }
            AtomicOp::CompareExchangeN => self.visit_atomic_cmpxchg(&args, order, mir_ty),
            AtomicOp::FetchAdd => self.visit_atomic_fetch_op(BinaryIntOp::Add, &args, order, mir_ty),
            AtomicOp::FetchSub => self.visit_atomic_fetch_op(BinaryIntOp::Sub, &args, order, mir_ty),
            AtomicOp::FetchAnd => self.visit_atomic_fetch_op(BinaryIntOp::BitAnd, &args, order, mir_ty),
            AtomicOp::FetchOr => self.visit_atomic_fetch_op(BinaryIntOp::BitOr, &args, order, mir_ty),
            AtomicOp::FetchXor => self.visit_atomic_fetch_op(BinaryIntOp::BitXor, &args, order, mir_ty),
            AtomicOp::AddFetch | AtomicOp::SubFetch | AtomicOp::AndFetch | AtomicOp::OrFetch | AtomicOp::XorFetch => {
                let bin_op = match op {
                    AtomicOp::AddFetch => BinaryIntOp::Add,
                    AtomicOp::SubFetch => BinaryIntOp::Sub,
                    AtomicOp::AndFetch => BinaryIntOp::BitAnd,
                    AtomicOp::OrFetch => BinaryIntOp::BitOr,
                    AtomicOp::XorFetch => BinaryIntOp::BitXor,
                    _ => unreachable!(),
                };
                let ptr = args[0].clone();
                let val = args[1].clone();
                let rval = Rvalue::AtomicFetchOp(bin_op, ptr, val.clone(), order);
                let old_val = self.emit_rvalue_to_operand(rval, mir_ty);
                let new_val_rval = Rvalue::BinaryIntOp(bin_op, old_val, val);
                self.emit_rvalue_to_operand(new_val_rval, mir_ty)
            }
        }
    }

    fn get_atomic_args(&mut self, args_start: NodeRef, args_len: u16) -> Vec<Operand> {
        args_start
            .range(args_len)
            .map(|arg| self.visit_expression(arg, true))
            .collect()
    }

    fn visit_atomic_cmpxchg(&mut self, args: &[Operand], order: AtomicMemOrder, mir_ty: TypeId) -> Operand {
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

        let mir_type_info = self.mb.get_type(val_ty);
        let cmp_rval = if mir_type_info.is_float() {
            Rvalue::BinaryFloatOp(BinaryFloatOp::Eq, old_val.clone(), expected_val_op)
        } else {
            Rvalue::BinaryIntOp(BinaryIntOp::Eq, old_val.clone(), expected_val_op)
        };

        let (_, success_place) = self.create_temp_local_with_assignment(cmp_rval, mir_ty);
        let success_op = Operand::Copy(Box::new(success_place));

        let update_block = self.create_block();
        let end_block = self.create_block();

        self.set_terminator(Terminator::If(success_op.clone(), end_block, update_block));

        self.set_current_block(update_block);
        self.add_stmt(MirStmt::Assign(expected_place, Rvalue::Use(old_val)));
        self.set_terminator(Terminator::Goto(end_block));

        self.set_current_block(end_block);
        success_op
    }

    fn visit_atomic_fetch_op(
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

    fn visit_complex_binary_op(&mut self, op: BinaryOp, lhs: Operand, rhs: Operand, mir_ty: TypeId) -> Operand {
        let lhs_ty = self.get_operand_type(&lhs);
        let rhs_ty = self.get_operand_type(&rhs);

        let (lhs_real, lhs_imag) = self.get_complex_components(lhs, lhs_ty);
        let (rhs_real, rhs_imag) = self.get_complex_components(rhs, rhs_ty);

        let element_ty = if let MirType::Record { field_types, .. } = self.mb.get_type(lhs_ty) {
            field_types[0]
        } else if let MirType::Record { field_types, .. } = self.mb.get_type(rhs_ty) {
            field_types[0]
        } else {
            panic!("Expected at least one complex record type in visit_complex_binary_op");
        };

        match op {
            BinaryOp::Add | BinaryOp::Sub => {
                let mir_op = if op == BinaryOp::Add {
                    BinaryFloatOp::Add
                } else {
                    BinaryFloatOp::Sub
                };
                let res_real = self.emit_float_binop(mir_op, lhs_real, rhs_real, element_ty);
                let res_imag = self.emit_float_binop(mir_op, lhs_imag, rhs_imag, element_ty);
                self.emit_complex_struct(res_real, res_imag, mir_ty)
            }
            BinaryOp::Mul => {
                let ac = self.emit_float_binop(BinaryFloatOp::Mul, lhs_real.clone(), rhs_real.clone(), element_ty);
                let bd = self.emit_float_binop(BinaryFloatOp::Mul, lhs_imag.clone(), rhs_imag.clone(), element_ty);
                let real = self.emit_float_binop(BinaryFloatOp::Sub, ac, bd, element_ty);

                let ad = self.emit_float_binop(BinaryFloatOp::Mul, lhs_real, rhs_imag, element_ty);
                let bc = self.emit_float_binop(BinaryFloatOp::Mul, lhs_imag, rhs_real, element_ty);
                let imag = self.emit_float_binop(BinaryFloatOp::Add, ad, bc, element_ty);

                self.emit_complex_struct(real, imag, mir_ty)
            }
            BinaryOp::Div => {
                let cc = self.emit_float_binop(BinaryFloatOp::Mul, rhs_real.clone(), rhs_real.clone(), element_ty);
                let dd = self.emit_float_binop(BinaryFloatOp::Mul, rhs_imag.clone(), rhs_imag.clone(), element_ty);
                let denom = self.emit_float_binop(BinaryFloatOp::Add, cc, dd, element_ty);

                let ac = self.emit_float_binop(BinaryFloatOp::Mul, lhs_real.clone(), rhs_real.clone(), element_ty);
                let bd = self.emit_float_binop(BinaryFloatOp::Mul, lhs_imag.clone(), rhs_imag.clone(), element_ty);
                let num_real = self.emit_float_binop(BinaryFloatOp::Add, ac, bd, element_ty);
                let real = self.emit_float_binop(BinaryFloatOp::Div, num_real, denom.clone(), element_ty);

                let bc = self.emit_float_binop(BinaryFloatOp::Mul, lhs_imag, rhs_real, element_ty);
                let ad = self.emit_float_binop(BinaryFloatOp::Mul, lhs_real, rhs_imag, element_ty);
                let num_imag = self.emit_float_binop(BinaryFloatOp::Sub, bc, ad, element_ty);
                let imag = self.emit_float_binop(BinaryFloatOp::Div, num_imag, denom, element_ty);

                self.emit_complex_struct(real, imag, mir_ty)
            }
            BinaryOp::Equal | BinaryOp::NotEqual => {
                let bool_ty = self.lower_type(self.registry.type_bool);
                if op == BinaryOp::Equal {
                    let real_eq = self.emit_float_binop(BinaryFloatOp::Eq, lhs_real, rhs_real, bool_ty);
                    let imag_eq = self.emit_float_binop(BinaryFloatOp::Eq, lhs_imag, rhs_imag, bool_ty);
                    self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitAnd, real_eq, imag_eq), mir_ty)
                } else {
                    let real_ne = self.emit_float_binop(BinaryFloatOp::Ne, lhs_real, rhs_real, bool_ty);
                    let imag_ne = self.emit_float_binop(BinaryFloatOp::Ne, lhs_imag, rhs_imag, bool_ty);
                    self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitOr, real_ne, imag_ne), mir_ty)
                }
            }
            _ => panic!("Unsupported complex binary operator: {:?}", op),
        }
    }

    fn visit_complex_unary_op(&mut self, op: UnaryOp, expr: NodeRef, mir_ty: TypeId) -> Operand {
        let operand = self.visit_expression(expr, true);
        let operand_ty = self.get_operand_type(&operand);

        let (real, imag) = self.get_complex_components(operand, operand_ty);

        let element_ty = match self.mb.get_type(operand_ty) {
            MirType::Record { field_types, .. } => field_types[0],
            _ => panic!("Expected complex record type"),
        };

        match op {
            UnaryOp::Minus => {
                let res_real = self.emit_float_unop(UnaryFloatOp::Neg, real, element_ty);
                let res_imag = self.emit_float_unop(UnaryFloatOp::Neg, imag, element_ty);
                self.emit_complex_struct(res_real, res_imag, mir_ty)
            }
            UnaryOp::BitNot => {
                // conjugate
                let res_imag = self.emit_float_unop(UnaryFloatOp::Neg, imag, element_ty);
                self.emit_complex_struct(real, res_imag, mir_ty)
            }
            UnaryOp::LogicNot => {
                let zero = self.create_constant(element_ty, ConstValueKind::Float(0.0));
                let zero_op = Operand::Constant(zero);
                let bool_ty = self.lower_type(self.registry.type_bool);

                let real_eq = self.emit_float_binop(BinaryFloatOp::Eq, real, zero_op.clone(), bool_ty);
                let imag_eq = self.emit_float_binop(BinaryFloatOp::Eq, imag, zero_op, bool_ty);
                self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitAnd, real_eq, imag_eq), mir_ty)
            }
            UnaryOp::Plus => self.emit_complex_struct(real, imag, mir_ty),
            UnaryOp::Real => real,
            UnaryOp::Imag => imag,
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                let is_inc = matches!(op, UnaryOp::PreIncrement);
                self.visit_inc_dec_expr(expr, is_inc, false, true)
            }
            _ => panic!("Unsupported complex unary operator: {:?}", op),
        }
    }

    fn try_visit_builtin_call(&mut self, call_expr: &CallExpr, mir_ty: TypeId, need_value: bool) -> Option<Operand> {
        let kind = self.get_builtin_function_kind(call_expr.callee)?;

        match kind {
            BuiltinFunctionKind::Signbit | BuiltinFunctionKind::SignbitF | BuiltinFunctionKind::SignbitL => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryFloatOp(UnaryFloatOp::IsNegative, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::FrameAddress => {
                let arg = call_expr.arg_start;
                let level = self.const_ctx().eval_int(arg).unwrap_or(0) as u32;
                let rval = Rvalue::BuiltinFrameAddress(level);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Expect => {
                let arg = call_expr.arg_start;
                Some(self.visit_expression(arg, true))
            }
            BuiltinFunctionKind::Clz | BuiltinFunctionKind::ClzL | BuiltinFunctionKind::ClzLL => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryIntOp(UnaryIntOp::Clz, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Ctz | BuiltinFunctionKind::CtzL | BuiltinFunctionKind::CtzLL => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryIntOp(UnaryIntOp::Ctz, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Popcount | BuiltinFunctionKind::PopcountL | BuiltinFunctionKind::PopcountLL => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryIntOp(UnaryIntOp::Popcount, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Ffs | BuiltinFunctionKind::FfsL | BuiltinFunctionKind::FfsLL => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryIntOp(UnaryIntOp::Ffs, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Bswap16 => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryIntOp(UnaryIntOp::Bswap16, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Bswap32 => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryIntOp(UnaryIntOp::Bswap32, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Bswap64 => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryIntOp(UnaryIntOp::Bswap64, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Unreachable | BuiltinFunctionKind::Trap => {
                self.set_terminator(Terminator::Trap);
                Some(self.create_dummy_operand())
            }
            BuiltinFunctionKind::ConstantP => {
                let arg = call_expr.arg_start;
                let is_const = self.const_ctx().eval_int(arg).is_some() || self.const_ctx().eval_float(arg).is_some();
                let val = if is_const { 1 } else { 0 };
                let const_op = self.create_constant(mir_ty, ConstValueKind::Int(val));
                Some(Operand::Constant(const_op))
            }
            BuiltinFunctionKind::Prefetch => {
                let arg_start = call_expr.arg_start;
                let addr = self.visit_expression(arg_start, true);

                let rw = if call_expr.arg_len > 1 {
                    self.const_ctx().eval_int(arg_start.add_offset(1)).unwrap_or(0) as u32
                } else {
                    0
                };

                let locality = if call_expr.arg_len > 2 {
                    self.const_ctx().eval_int(arg_start.add_offset(2)).unwrap_or(3) as u32
                } else {
                    3
                };

                self.add_stmt(MirStmt::BuiltinPrefetch { addr, rw, locality });
                Some(self.create_dummy_operand())
            }
            BuiltinFunctionKind::Pause => Some(self.create_dummy_operand()),
            BuiltinFunctionKind::VaStart => {
                let arg_start = call_expr.arg_start;
                let ap_op = self.visit_expression(arg_start, true);
                let ap = self.ensure_valist_place(ap_op);
                let last = self.visit_expression(arg_start.add_offset(1), true);
                self.add_stmt(MirStmt::BuiltinVaStart(ap, last));
                Some(self.create_int_operand(0))
            }
            BuiltinFunctionKind::VaEnd => {
                let arg_start = call_expr.arg_start;
                let ap_op = self.visit_expression(arg_start, true);
                let ap = self.ensure_valist_place(ap_op);
                self.add_stmt(MirStmt::BuiltinVaEnd(ap));
                Some(self.create_int_operand(0))
            }
            BuiltinFunctionKind::VaCopy => {
                let arg_start = call_expr.arg_start;
                let dst_op = self.visit_expression(arg_start, true);
                let dst = self.ensure_valist_place(dst_op);
                let src_op = self.visit_expression(arg_start.add_offset(1), true);
                let src = self.ensure_valist_place(src_op);
                self.add_stmt(MirStmt::BuiltinVaCopy(dst, src));
                Some(self.create_int_operand(0))
            }
            BuiltinFunctionKind::Fabs | BuiltinFunctionKind::FabsF | BuiltinFunctionKind::FabsL => {
                let arg = call_expr.arg_start;
                let operand = self.visit_expression(arg, true);
                let rval = Rvalue::UnaryFloatOp(UnaryFloatOp::Abs, operand);
                Some(self.emit_rvalue_to_operand(rval, mir_ty))
            }
            BuiltinFunctionKind::Alloca => {
                let arg = call_expr.arg_start;
                let size_op = self.visit_expression(arg, true);
                let void_ptr_mir = self.lower_type(self.registry.type_void_ptr);
                let (temp_local, temp_place) = self.create_temp_local(void_ptr_mir);

                self.emit_malloc_call(temp_local, size_op);
                Some(Operand::Copy(Box::new(temp_place)))
            }
            BuiltinFunctionKind::Memcpy | BuiltinFunctionKind::Memmove => {
                let arg_start = call_expr.arg_start;
                let dest = arg_start;
                let src = arg_start.add_offset(1);
                let n = arg_start.add_offset(2);

                let void_ptr = self.registry.type_void_ptr;
                let const_void = QualType::new(self.registry.type_void, TypeQualifiers::CONST);
                let const_void_ptr = self.registry.pointer_to(const_void);

                let d_ty = self.lower_type(void_ptr);
                let s_ty = self.lower_type(const_void_ptr);
                let n_ty = self.get_size_t_type();

                let name = if kind == BuiltinFunctionKind::Memcpy {
                    "memcpy"
                } else {
                    "memmove"
                };
                Some(self.emit_builtin_memory_op(name, &[(dest, d_ty), (src, s_ty), (n, n_ty)], d_ty, need_value))
            }
            BuiltinFunctionKind::Memset => {
                let arg_start = call_expr.arg_start;
                let s = arg_start;
                let c = arg_start.add_offset(1);
                let n = arg_start.add_offset(2);

                let void_ptr = self.lower_type(self.registry.type_void_ptr);
                let int_ty = self.get_int_type();
                let size_t = self.get_size_t_type();

                Some(self.emit_builtin_memory_op(
                    "memset",
                    &[(s, void_ptr), (c, int_ty), (n, size_t)],
                    void_ptr,
                    need_value,
                ))
            }
            BuiltinFunctionKind::Memcmp => {
                let arg_start = call_expr.arg_start;
                let s1 = arg_start;
                let s2 = arg_start.add_offset(1);
                let n = arg_start.add_offset(2);

                let const_void = QualType::new(self.registry.type_void, TypeQualifiers::CONST);
                let const_void_ptr = self.registry.pointer_to(const_void);

                let cv_ptr_ty = self.lower_type(const_void_ptr);
                let n_ty = self.get_size_t_type();
                let ret_ty = self.get_int_type();

                Some(self.emit_builtin_memory_op(
                    "memcmp",
                    &[(s1, cv_ptr_ty), (s2, cv_ptr_ty), (n, n_ty)],
                    ret_ty,
                    need_value,
                ))
            }
            k if k.to_atomic_op().is_some() => {
                let op = k.to_atomic_op().unwrap();
                Some(self.visit_atomic_op(op, call_expr.arg_start, call_expr.arg_len, mir_ty))
            }
            _ => None,
        }
    }

    /// Try to lower builtin float constant functions like `__builtin_inff`, `__builtin_nanf`, etc.
    /// Returns Some(Operand) if the call is a builtin float constant, None otherwise.
    fn try_visit_builtin_float_const(&mut self, call_expr: &CallExpr, mir_ty: TypeId) -> Option<Operand> {
        let kind = self.get_builtin_function_kind(call_expr.callee)?;

        match kind {
            BuiltinFunctionKind::Inff | BuiltinFunctionKind::HugeValf => {
                let val = f32::INFINITY as f64;
                Some(self.create_float_operand(val, mir_ty))
            }
            BuiltinFunctionKind::Inf | BuiltinFunctionKind::HugeVal => {
                let val = f64::INFINITY;
                Some(self.create_float_operand(val, mir_ty))
            }
            BuiltinFunctionKind::Nanf => {
                let val = f32::NAN as f64;
                Some(self.create_float_operand(val, mir_ty))
            }
            BuiltinFunctionKind::Nan => {
                let val = f64::NAN;
                Some(self.create_float_operand(val, mir_ty))
            }
            _ => None,
        }
    }

    fn emit_builtin_memory_op(
        &mut self,
        name: &str,
        args: &[(NodeRef, TypeId)],
        return_ty: TypeId,
        need_value: bool,
    ) -> Operand {
        let mut arg_ops = Vec::new();
        let mut arg_types = Vec::new();
        for (node, target_ty) in args {
            let op = self.visit_expression(*node, true);
            let conv = self.apply_conversions(op, *node, *target_ty);
            arg_ops.push(conv);
            arg_types.push(*target_ty);
        }

        let target = self.find_or_declare_extern_function(NameId::new(name), arg_types, return_ty, false);

        let dest_place = if need_value {
            let (_, p) = self.create_temp_local(return_ty);
            Some(p)
        } else {
            None
        };

        self.add_stmt(MirStmt::Call {
            target: CallTarget::Direct(target),
            args: arg_ops,
            dest: dest_place.clone(),
        });

        if let Some(p) = dest_place {
            Operand::Copy(Box::new(p))
        } else {
            self.create_dummy_operand()
        }
    }

    fn get_builtin_function_kind(&self, node: NodeRef) -> Option<BuiltinFunctionKind> {
        match self.ast.get_kind(node) {
            NodeKind::Ident(_, sym_ref) => {
                let sym = self.symbol_table.get_symbol(*sym_ref);
                if let SymbolKind::Function(f) = &sym.kind {
                    f.builtin_kind
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn visit_label_addr(&mut self, name: NameId, expected_ty: TypeId) -> Operand {
        let label_info = self
            .func_state()
            .label_map
            .get(&name)
            .cloned()
            .expect("Label was not pre-scanned");
        let rvalue = Rvalue::LabelAddr(label_info.block_id);
        let (_, place) = self.create_temp_local(expected_ty);
        self.add_stmt(crate::mir::MirStmt::Assign(place.clone(), rvalue));
        Operand::Copy(Box::new(place))
    }
}
