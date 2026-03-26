use crate::ast::literal::{FloatSuffix, Literal};
use crate::ast::nodes::AtomicOp;
use crate::ast::{BinaryOp, NameId, NodeKind, NodeRef, UnaryOp};
use crate::codegen::mir_gen::MirGen;
use crate::codegen::mir_gen_ops;
use crate::mir::{
    AtomicMemOrder, BinaryFloatOp, BinaryIntOp, BitFieldInfo, CallTarget, ConstValue, ConstValueKind, MirStmt, MirType,
    Operand, Place, Rvalue, Terminator, TypeId,
};

use crate::semantic::{ArraySizeType, Conversion, QualType, SymbolKind, SymbolRef, TypeKind, ValueCategory};
use crate::{ast, semantic};

impl<'a> MirGen<'a> {
    fn visit_expression_as_place(&mut self, expr: NodeRef) -> Place {
        let node_kind = self.ast.get_kind(expr);
        match node_kind {
            NodeKind::UnaryOp(UnaryOp::Real, operand) => {
                let base_place = self.visit_expression_as_place(*operand);
                let operand_ty = self.ast.get_resolved_type(*operand).unwrap();
                if operand_ty.is_complex() {
                    Place::StructField(Box::new(base_place), 0, None)
                } else {
                    base_place
                }
            }
            NodeKind::UnaryOp(UnaryOp::Imag, operand) => {
                let base_place = self.visit_expression_as_place(*operand);
                let operand_ty = self.ast.get_resolved_type(*operand).unwrap();
                if operand_ty.is_complex() {
                    Place::StructField(Box::new(base_place), 1, None)
                } else {
                    let op = self.visit_expression(expr, true);
                    let ty = self.ast.get_resolved_type(expr).unwrap();
                    let mir_ty = self.lower_qual_type(ty);
                    self.ensure_place(op, mir_ty)
                }
            }
            _ => {
                let op = self.visit_expression(expr, true);
                let ty = self.ast.get_resolved_type(expr).unwrap();
                let mir_ty = self.lower_qual_type(ty);
                self.ensure_place(op, mir_ty)
            }
        }
    }

    pub(crate) fn visit_expression(&mut self, expr: NodeRef, need_value: bool) -> Operand {
        let qt = self.ast.get_resolved_type(expr).unwrap_or_else(|| {
            let node_kind = self.ast.get_kind(expr);
            let node_span = self.ast.get_span(expr);
            let (line, col, file) = self
                .source_manager
                .get_presumed_location(node_span.start())
                .map(|(l, c, f)| (l, c, f.unwrap_or("<unknown>")))
                .unwrap_or((0, 0, "<unknown>"));
            panic!(
                "Type not resolved for node {:?} at {}:{}:{} (span: {:?})",
                node_kind, file, line, col, node_span
            );
        });
        let node_kind = *self.ast.get_kind(expr);

        let mir_ty = self.lower_qual_type(qt);

        if let Some(const_op) = self.try_constant_fold(expr, &node_kind, qt) {
            return const_op;
        }

        match &node_kind {
            NodeKind::Literal(_) => self.visit_literal(&node_kind, qt).expect("Failed to lower literal"),
            NodeKind::Ident(_, sym) => self.visit_ident(*sym),
            NodeKind::UnaryOp(op, operand) => self.visit_unary_op(op, *operand, mir_ty),
            NodeKind::PostIncrement(operand) => self.visit_inc_dec_expr(*operand, true, true, need_value),
            NodeKind::PostDecrement(operand) => self.visit_inc_dec_expr(*operand, false, true, need_value),
            NodeKind::BinaryOp(op, left, right) => self.visit_binary_op(op, *left, *right, mir_ty),
            NodeKind::Assignment(op, left, right) => self.visit_assignment_expr(expr, op, *left, *right, mir_ty),
            NodeKind::FunctionCall(call_expr) => {
                // Check for builtin float constant functions
                if let Some(builtin_op) = self.try_visit_builtin_float_const(call_expr, mir_ty) {
                    return builtin_op;
                }

                let is_void = self.mir_builder.get_type(mir_ty).is_void();
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
            NodeKind::MemberAccess(obj, field_name, is_arrow) => self.visit_member_access(*obj, field_name, *is_arrow),
            NodeKind::IndexAccess(arr, idx) => self.visit_index_access(*arr, *idx),
            NodeKind::TernaryOp(cond, then, else_expr) => self.visit_ternary_op(*cond, *then, *else_expr, mir_ty),
            NodeKind::SizeOfExpr(expr) => {
                let ty = self
                    .ast
                    .get_resolved_type(*expr)
                    .expect("SizeOf operand type missing")
                    .ty();
                self.visit_type_query(ty, true)
            }
            NodeKind::SizeOfType(qt) => self.visit_type_query(qt.ty(), true),
            NodeKind::AlignOfType(qt) => self.visit_type_query(qt.ty(), false),
            NodeKind::AlignOfExpr(expr) => {
                // If the expression is a direct reference to a variable, it might have a custom alignment.
                if let NodeKind::Ident(_, sym) = self.ast.get_kind(*expr) {
                    let symbol = self.symbol_table.get_symbol(*sym);
                    if let SymbolKind::Variable { alignment, .. } = &symbol.kind
                        && let Some(align) = alignment
                    {
                        return self.create_size_t_operand(*align as u64);
                    }
                }

                let ty = self
                    .ast
                    .get_resolved_type(*expr)
                    .expect("AlignOf operand type missing")
                    .ty();
                self.visit_type_query(ty, false)
            }
            NodeKind::BuiltinOffsetof(..) => {
                let val = self.const_ctx().eval_int(expr).expect("offsetof should be constant");
                self.create_size_t_operand(val as u64)
            }
            NodeKind::BuiltinTypesCompatibleP(..) => {
                let val = self
                    .const_ctx()
                    .eval_int(expr)
                    .expect("__builtin_types_compatible_p should be constant");
                self.create_int_operand(val)
            }
            NodeKind::BuiltinConstantP(..) => {
                let val = self
                    .const_ctx()
                    .eval_int(expr)
                    .expect("__builtin_constant_p should evaluate to constant");
                self.create_int_operand(val)
            }
            NodeKind::BuiltinUnreachable | NodeKind::BuiltinTrap => {
                self.mir_builder.set_terminator(crate::mir::Terminator::Trap);
                self.create_dummy_operand()
            }
            NodeKind::BuiltinChooseExpr(..) => self.visit_builtin_choose_expr(need_value, expr),
            NodeKind::GenericSelection(gs) => self.visit_generic_selection(gs, need_value, expr),
            NodeKind::StatementExpr(stmt, result_expr) => self.visit_gnu_stmt_expr(*stmt, *result_expr, need_value),
            NodeKind::Cast(_ty, operand) => self.visit_cast(*operand, mir_ty),
            NodeKind::CompoundLiteral(ty, init) => self.visit_compound_literal(*ty, *init),
            NodeKind::BuiltinVaArg(ty, expr) => self.visit_builtin_va_arg(*ty, *expr),
            NodeKind::BuiltinExpect(exp, c) => {
                let _ = self.visit_expression(*c, true); // lower 'c' for side effects or just to process it
                self.visit_expression(*exp, need_value)
            }
            NodeKind::BuiltinMemcpy(dest, src, n) | NodeKind::BuiltinMemmove(dest, src, n) => {
                let d_op = self.visit_expression(*dest, true);
                let s_op = self.visit_expression(*src, true);
                let n_op = self.visit_expression(*n, true);

                let void_ptr = self.registry.type_void_ptr;
                let const_void = QualType::new(self.registry.type_void, crate::semantic::TypeQualifiers::CONST);
                let const_void_ptr = self.registry.pointer_to(const_void);

                let d_ty = self.lower_type(void_ptr);
                let s_ty = self.lower_type(const_void_ptr);
                let n_ty = self.get_size_t_type();

                let d_conv = self.apply_conversions(d_op, *dest, d_ty);
                let s_conv = self.apply_conversions(s_op, *src, s_ty);
                let n_conv = self.apply_conversions(n_op, *n, n_ty);

                let name = match node_kind {
                    NodeKind::BuiltinMemcpy(..) => "memcpy",
                    NodeKind::BuiltinMemmove(..) => "memmove",
                    _ => unreachable!(),
                };

                let target = self.find_or_declare_extern_function(
                    crate::ast::NameId::new(name),
                    vec![d_ty, s_ty, n_ty],
                    d_ty,
                    false,
                );

                let dest_place = if need_value {
                    let (_, p) = self.create_temp_local(d_ty);
                    Some(p)
                } else {
                    None
                };

                self.mir_builder.add_statement(crate::mir::MirStmt::Call {
                    target: crate::mir::CallTarget::Direct(target),
                    args: vec![d_conv, s_conv, n_conv],
                    dest: dest_place.clone(),
                });

                if let Some(p) = dest_place {
                    Operand::Copy(Box::new(p))
                } else {
                    self.create_dummy_operand()
                }
            }
            NodeKind::BuiltinMemset(s, c, n) => {
                let s_op = self.visit_expression(*s, true);
                let c_op = self.visit_expression(*c, true);
                let n_op = self.visit_expression(*n, true);

                let void_ptr = self.lower_type(self.registry.type_void_ptr);
                let int_ty = self.get_int_type();
                let size_t = self.get_size_t_type();

                let s_conv = self.apply_conversions(s_op, *s, void_ptr);
                let c_conv = self.apply_conversions(c_op, *c, int_ty);
                let n_conv = self.apply_conversions(n_op, *n, size_t);

                let target = self.find_or_declare_extern_function(
                    crate::ast::NameId::new("memset"),
                    vec![void_ptr, int_ty, size_t],
                    void_ptr,
                    false,
                );

                let dest_place = if need_value {
                    let (_, p) = self.create_temp_local(void_ptr);
                    Some(p)
                } else {
                    None
                };

                self.mir_builder.add_statement(crate::mir::MirStmt::Call {
                    target: crate::mir::CallTarget::Direct(target),
                    args: vec![s_conv, c_conv, n_conv],
                    dest: dest_place.clone(),
                });

                if let Some(p) = dest_place {
                    Operand::Copy(Box::new(p))
                } else {
                    self.create_dummy_operand()
                }
            }
            NodeKind::BuiltinPopcount(exp)
            | NodeKind::BuiltinClz(exp)
            | NodeKind::BuiltinCtz(exp)
            | NodeKind::BuiltinFfs(exp)
            | NodeKind::BuiltinBswap16(exp)
            | NodeKind::BuiltinBswap32(exp)
            | NodeKind::BuiltinBswap64(exp)
            | NodeKind::BuiltinFabs(exp)
            | NodeKind::BuiltinFabsf(exp)
            | NodeKind::BuiltinFabsl(exp) => {
                let op = match node_kind {
                    NodeKind::BuiltinPopcount(_) => Some(crate::mir::UnaryIntOp::Popcount),
                    NodeKind::BuiltinClz(_) => Some(crate::mir::UnaryIntOp::Clz),
                    NodeKind::BuiltinCtz(_) => Some(crate::mir::UnaryIntOp::Ctz),
                    NodeKind::BuiltinFfs(_) => Some(crate::mir::UnaryIntOp::Ffs),
                    NodeKind::BuiltinBswap16(_) => Some(crate::mir::UnaryIntOp::Bswap16),
                    NodeKind::BuiltinBswap32(_) => Some(crate::mir::UnaryIntOp::Bswap32),
                    NodeKind::BuiltinBswap64(_) => Some(crate::mir::UnaryIntOp::Bswap64),
                    _ => None,
                };
                let operand = self.visit_expression(*exp, true);

                let operand_ty = self.ast.get_resolved_type(*exp).unwrap();
                let operand_mir_ty = self.lower_qual_type(operand_ty);
                let operand_converted = self.apply_conversions(operand, *exp, operand_mir_ty);

                let is_fabs = matches!(
                    node_kind,
                    NodeKind::BuiltinFabs(_) | NodeKind::BuiltinFabsf(_) | NodeKind::BuiltinFabsl(_)
                );

                if is_fabs {
                    let rval = crate::mir::Rvalue::UnaryFloatOp(crate::mir::UnaryFloatOp::Abs, operand_converted);
                    self.emit_rvalue_to_operand(rval, mir_ty)
                } else {
                    let rval = crate::mir::Rvalue::UnaryIntOp(op.unwrap(), operand_converted);
                    self.emit_rvalue_to_operand(rval, mir_ty)
                }
            }
            NodeKind::BuiltinPrefetch(addr, rw, locality) => {
                let _ = self.visit_expression(*addr, true);
                if let Some(rw) = rw {
                    let _ = self.visit_expression(*rw, true);
                }
                if let Some(locality) = locality {
                    let _ = self.visit_expression(*locality, true);
                }
                self.create_dummy_operand()
            }
            NodeKind::BuiltinAlloca(size) => {
                let size_op = self.visit_expression(*size, true);
                let size_t = self.get_size_t_type();
                let size_conv = self.apply_conversions(size_op, *size, size_t);

                let void_ptr_mir = self.lower_type(self.registry.type_void_ptr);
                let (temp_local, temp_place) = self.create_temp_local(void_ptr_mir);

                self.emit_malloc_call(temp_local, size_conv);
                Operand::Copy(Box::new(temp_place))
            }
            NodeKind::AtomicOp(op, args_start, args_len) => self.visit_atomic_op(*op, *args_start, *args_len, mir_ty),
            NodeKind::BuiltinVaStart(..) | NodeKind::BuiltinVaEnd(..) | NodeKind::BuiltinVaCopy(..) => {
                self.visit_builtin_void(&node_kind)
            }
            NodeKind::InitializerList(_) | NodeKind::InitializerItem(_) => {
                panic!("InitializerList or InitializerItem not implemented");
            }
            _ => unreachable!(),
        }
    }

    fn try_constant_fold(&mut self, expr: NodeRef, kind: &NodeKind, qt: QualType) -> Option<Operand> {
        // Attempt constant folding for arithmetic/logical operations that are not simple literals
        if !matches!(
            kind,
            NodeKind::BinaryOp(..) | NodeKind::UnaryOp(..) | NodeKind::TernaryOp(..) | NodeKind::Cast(..)
        ) {
            return None;
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
            let mir_type = self.mir_builder.get_type(ty_id);
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
                if self.mir_builder.current_block_has_terminator() {
                    if let NodeKind::Label(..) = node_kind {
                        // OK
                    } else {
                        continue;
                    }
                }
                self.visit_node(stmt);
            }

            let op = if let NodeKind::Dummy = self.ast.get_kind(result_expr) {
                self.create_dummy_operand()
            } else {
                self.visit_expression(result_expr, need_value)
            };

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
            let const_val = self.mir_builder.get_constants().get(&const_id).unwrap().clone();

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
        let is_void = matches!(self.mir_builder.get_type(mir_ty), crate::mir::MirType::Void);

        let mut cond_op = self.visit_expression(cond, true);
        cond_op = self.cast_operand_to_bool(cond_op);

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

        for (target_block, expr) in [(then_block, then_expr), (else_block, else_expr)] {
            self.mir_builder.set_current_block(target_block);
            let val = self.visit_expression(expr, !is_void);
            if let Some(local) = result_local {
                let val_conv = self.apply_conversions(val, expr, mir_ty);
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

    pub(crate) fn visit_type_query(&mut self, ty: semantic::TypeRef, is_size: bool) -> Operand {
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
                    return self.create_size_t_operand(layout.alignment);
                }
            }
            return self.create_dummy_operand();
        }
        let _ = self.registry.ensure_layout(ty);
        let layout = self.registry.get_layout(ty);
        let val = if is_size { layout.size } else { layout.alignment };
        self.create_size_t_operand(val)
    }

    /// Compute sizeof(VLA) at runtime.
    fn visit_sizeof_vla(&mut self, ty: semantic::TypeRef) -> Operand {
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
            let rvalue = Rvalue::BinaryIntOp(crate::mir::BinaryIntOp::Mul, count_as_size_t, element_size_operand);
            self.emit_rvalue_to_operand(rvalue, size_t_mir_ty)
        } else {
            // Shouldn't happen, but fallback
            self.create_dummy_operand()
        }
    }

    fn visit_generic_selection(
        &mut self,
        _gs: &ast::nodes::GenericSelection,
        need_value: bool,
        node: NodeRef,
    ) -> Operand {
        let expr_to_lower = *self
            .ast
            .semantic_info
            .as_ref()
            .unwrap()
            .generic_selections
            .get(&node.index())
            .expect("Generic selection failed (should be caught by Analyzer)");
        self.visit_expression(expr_to_lower, need_value)
    }

    fn visit_builtin_choose_expr(&mut self, need_value: bool, node: NodeRef) -> Operand {
        let expr_to_lower = *self
            .ast
            .semantic_info
            .as_ref()
            .unwrap()
            .choose_expressions
            .get(&node.index())
            .expect("__builtin_choose_expr failed (should be caught by Analyzer)");
        self.visit_expression(expr_to_lower, need_value)
    }

    fn visit_cast(&mut self, operand: NodeRef, mir_ty: TypeId) -> Operand {
        let is_void = self.mir_builder.get_type(mir_ty).is_void();
        if is_void {
            self.visit_expression(operand, false);
            return self.create_dummy_operand();
        }
        let operand = self.visit_expression(operand, true);
        if self.get_operand_type(&operand) == mir_ty {
            return operand;
        }

        // Fold constant casts if types are compatible
        if let Some(const_id) = self.operand_to_const_id(&operand) {
            let const_val = self.mir_builder.get_constants().get(&const_id).unwrap().clone();
            let mir_type = self.mir_builder.get_type(mir_ty);

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
                return Operand::Constant(self.create_constant(mir_ty, truncated_kind));
            }
        }

        Operand::Cast(mir_ty, Box::new(operand))
    }

    fn visit_literal(&mut self, node_kind: &NodeKind, ty: QualType) -> Option<Operand> {
        let mir_ty = self.lower_qual_type(ty);
        match node_kind {
            NodeKind::Literal(literal) => match literal {
                Literal::Int { val, .. } => Some(Operand::Constant(
                    self.create_constant(mir_ty, ConstValueKind::Int(*val)),
                )),
                Literal::Float { val, suffix } => {
                    if matches!(suffix, Some(FloatSuffix::I | FloatSuffix::IF | FloatSuffix::IL)) {
                        let ty_info = self.mir_builder.get_type(mir_ty);
                        if let crate::mir::MirType::Record { field_types, .. } = ty_info {
                            let elem_ty = field_types[0];
                            let zero = self.create_constant(elem_ty, ConstValueKind::Float(0.0));
                            let imag = self.create_constant(elem_ty, ConstValueKind::Float(*val));
                            Some(Operand::Constant(self.create_constant(
                                mir_ty,
                                ConstValueKind::StructLiteral(vec![(0, zero), (1, imag)]),
                            )))
                        } else {
                            unreachable!("Complex float must lower to a record type")
                        }
                    } else {
                        Some(Operand::Constant(
                            self.create_constant(mir_ty, ConstValueKind::Float(*val)),
                        ))
                    }
                }
                Literal::Char(val) => Some(Operand::Constant(
                    self.create_constant(mir_ty, ConstValueKind::Int(*val as i64)),
                )),
                Literal::String(val) => Some(self.visit_literal_string(val, ty)),
            },
            _ => None,
        }
    }

    fn visit_unary_op(&mut self, op: &UnaryOp, expr: NodeRef, mir_ty: TypeId) -> Operand {
        let ty = self.ast.get_resolved_type(expr).unwrap();
        if ty.is_complex() && !matches!(op, UnaryOp::AddrOf | UnaryOp::Deref) {
            return self.visit_complex_unary_op(op, expr, mir_ty);
        }

        match op {
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                let is_inc = matches!(op, UnaryOp::PreIncrement);
                self.visit_inc_dec_expr(expr, is_inc, false, true)
            }
            UnaryOp::AddrOf => self.visit_unary_addrof(expr),
            UnaryOp::Deref => self.visit_unary_deref(expr),
            UnaryOp::Real => {
                if self.ast.get_value_category(expr) == Some(ValueCategory::LValue) {
                    let place = self.visit_expression_as_place(expr);
                    Operand::Copy(Box::new(place))
                } else {
                    let operand = self.visit_expression(expr, true);
                    self.apply_conversions(operand, expr, mir_ty)
                }
            }
            UnaryOp::Imag => {
                let _ = self.visit_expression(expr, false);
                let kind = if self.mir_builder.get_type(mir_ty).is_float() {
                    ConstValueKind::Float(0.0)
                } else {
                    ConstValueKind::Int(0)
                };
                Operand::Constant(self.create_constant(mir_ty, kind))
            }
            _ => {
                let operand = self.visit_expression(expr, true);
                let operand_converted = self.apply_conversions(operand, expr, mir_ty);
                let operand_ty = self.get_operand_type(&operand_converted);
                let mir_type = self.mir_builder.get_type(operand_ty);

                let rval = mir_gen_ops::emit_unary_rvalue(op, operand_converted, mir_type.is_float());
                self.emit_rvalue_to_operand(rval, mir_ty)
            }
        }
    }

    fn visit_unary_addrof(&mut self, expr: NodeRef) -> Operand {
        let operand = self.visit_expression(expr, true);
        if let Operand::Copy(ref place) = operand {
            // Special case for VLA: &vla should evaluate to the value of the pointer local.
            if let Place::Local(local_id) = &**place
                && self.vla_map.values().any(|(ptr, _)| ptr == local_id)
            {
                let symbol_ty = self.ast.get_resolved_type(expr).unwrap();
                if symbol_ty.is_array() {
                    return operand.clone();
                }
            }
            Operand::AddressOf(place.clone())
        } else if let Operand::Constant(const_id) = operand
            && self.ast.get_value_category(expr) == Some(ValueCategory::LValue)
            && matches!(
                self.mir_builder.get_constants().get(&const_id),
                Some(ConstValue {
                    kind: ConstValueKind::FunctionAddress(_),
                    ..
                })
            )
        {
            // Function address constant has FunctionType, but &func results in Pointer(FunctionType).
            let func_ty = self.get_operand_type(&operand);
            let ptr_ty = self
                .mir_builder
                .add_type(crate::mir::MirType::Pointer { pointee: func_ty });
            Operand::Cast(ptr_ty, Box::new(operand))
        } else {
            panic!("Cannot take address of a non-lvalue");
        }
    }

    fn visit_unary_deref(&mut self, expr: NodeRef) -> Operand {
        let operand = self.visit_expression(expr, true);
        let operand_ty = self.ast.get_resolved_type(expr).unwrap();
        let target_mir_ty = self.lower_qual_type(operand_ty);
        let operand_converted = self.apply_conversions(operand, expr, target_mir_ty);

        let place = self.deref_operand(operand_converted);
        Operand::Copy(Box::new(place))
    }

    fn visit_ident(&mut self, sym: SymbolRef) -> Operand {
        let entry = self.symbol_table.get_symbol(sym);

        match &entry.kind {
            SymbolKind::Variable { is_global, storage, .. } => {
                let is_static_local = *storage == Some(crate::ast::StorageClass::Static);
                if *is_global || is_static_local {
                    // Lazy lowering for globals/statics (e.g. __func__) that might not be lowered yet
                    if !self.global_map.contains_key(&sym) {
                        let qt = entry.type_info;
                        let mir_ty = self.lower_qual_type(qt);
                        self.visit_variable(sym, mir_ty);
                    }

                    let global_id = match self.global_map.get(&sym) {
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
                } else if let Some(&(ptr_local_id, _)) = self.vla_map.get(&sym) {
                    // For VLA, the identifier refers to the dynamically allocated memory.
                    // If it is an array type (VLA), the identifier refers to the base of the array.
                    // If it is a scalar (highly-aligned fallback), we must Deref to get the value.
                    let symbol = self.symbol_table.get_symbol(sym);
                    let is_array = symbol.type_info.is_array();

                    if is_array {
                        // Return the pointer local directly. ArrayIndex and decay will handle it.
                        Operand::Copy(Box::new(Place::Local(ptr_local_id)))
                    } else {
                        // Return Deref(p) so it behaves like a normal scalar variable.
                        let ptr_op = Operand::Copy(Box::new(Place::Local(ptr_local_id)));
                        Operand::Copy(Box::new(Place::Deref(Box::new(ptr_op))))
                    }
                } else {
                    let local_id = self.local_map.get(&sym).unwrap();
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

    fn unify_binary_operands(
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

    fn visit_binary_op(&mut self, op: &BinaryOp, left: NodeRef, right: NodeRef, mir_ty: TypeId) -> Operand {
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
            let rhs = self.visit_expression(right, true);
            // Apply conversions for RHS to match result type (comma result type is RHS type)
            return self.apply_conversions(rhs, right, mir_ty);
        }

        let lhs = self.visit_expression(left, true);
        let rhs = self.visit_expression(right, true);

        let (rval, _op_ty) = self.visit_binary_arithmetic_logic(op, lhs, rhs, left, right, mir_ty);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    fn visit_binary_arithmetic_logic(
        &mut self,
        op: &BinaryOp,
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

        // Apply implicit conversions from semantic info first to match AST
        let lhs_converted = self.apply_conversions(lhs, left_expr, context_ty);
        let rhs_converted = self.apply_conversions(rhs, right_expr, context_ty);

        let lhs_mir_ty = self.get_operand_type(&lhs_converted);
        let rhs_mir_ty = self.get_operand_type(&rhs_converted);

        let lhs_is_complex = self.mir_builder.get_type(lhs_mir_ty).is_aggregate()
            && self.ast.get_resolved_type(left_expr).is_some_and(|t| t.is_complex());
        let rhs_is_complex = self.mir_builder.get_type(rhs_mir_ty).is_aggregate()
            && self.ast.get_resolved_type(right_expr).is_some_and(|t| t.is_complex());

        if lhs_is_complex || rhs_is_complex {
            let op = self.visit_complex_binary_op(op, lhs_converted, rhs_converted, context_ty);
            return (Rvalue::Use(op), context_ty);
        }

        // Ensure both operands have the same type for MIR operations.
        let (lhs_unified, rhs_unified) =
            self.unify_binary_operands(lhs_converted, rhs_converted, lhs_mir_ty, rhs_mir_ty);

        let lhs_final = lhs_unified;
        let rhs_final = rhs_unified;

        let common_ty = self.get_operand_type(&lhs_final);

        let common_mir_type = self.mir_builder.get_type(common_ty);
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

    fn visit_bool_normalization(
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
            .add_statement(MirStmt::Assign(result_place, Rvalue::Use(zero_op)));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));
    }

    fn visit_logical_op(&mut self, op: &BinaryOp, left: NodeRef, right: NodeRef, mir_ty: TypeId) -> Operand {
        // Short-circuiting logic for && and ||
        let (_res_local, res_place) = self.create_temp_local(mir_ty);

        let eval_rhs_block = self.mir_builder.create_block();
        let merge_block = self.mir_builder.create_block();
        let short_circuit_block = self.mir_builder.create_block();

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
        self.mir_builder
            .set_terminator(Terminator::If(lhs_op, true_target, false_target));

        // Short circuit case
        self.mir_builder.set_current_block(short_circuit_block);
        self.mir_builder
            .add_statement(MirStmt::Assign(res_place.clone(), Rvalue::Use(short_circuit_val)));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        // 2. Evaluate RHS
        self.mir_builder.set_current_block(eval_rhs_block);
        let rhs_val = self.lower_condition(right);

        self.visit_bool_normalization(rhs_val, res_place.clone(), merge_block);

        // Merge
        self.mir_builder.set_current_block(merge_block);
        self.current_block = Some(merge_block);

        Operand::Copy(Box::new(res_place))
    }

    fn unwrap_cast_if_int(&mut self, op: Operand) -> Operand {
        match op {
            Operand::Cast(ty, inner) => {
                let inner_ty = self.get_operand_type(&inner);
                if self.mir_builder.get_type(inner_ty).is_int() {
                    return *inner;
                }

                let unwrapped = self.unwrap_cast_if_int(*inner.clone());
                let unwrapped_ty = self.get_operand_type(&unwrapped);
                if self.mir_builder.get_type(unwrapped_ty).is_int() {
                    return unwrapped;
                }

                Operand::Cast(ty, inner)
            }
            Operand::Constant(const_id) => {
                let val_opt = {
                    let const_val = self.mir_builder.get_constants().get(&const_id).unwrap();
                    if let ConstValueKind::Int(val) = const_val.kind {
                        Some(val)
                    } else {
                        None
                    }
                };

                if let Some(val) = val_opt {
                    return self.create_int_operand(val);
                }
                Operand::Constant(const_id)
            }
            _ => op,
        }
    }

    fn visit_pointer_arithmetic(
        &mut self,
        op: &BinaryOp,
        lhs: Operand,
        rhs: Operand,
        left_expr: NodeRef,
        right_expr: NodeRef,
    ) -> Option<Rvalue> {
        // Lower types and apply conversions locally to check for pointer arithmetic
        // We use the operand's own type as the target for conversion to avoid forcing
        // implicit casts to the result type (which causes issues for Ptr + Int -> Ptr)
        let lhs_ty = self.ast.get_resolved_type(left_expr).unwrap();
        let rhs_ty = self.ast.get_resolved_type(right_expr).unwrap();

        let lhs_mir_target = self.lower_qual_type(lhs_ty);
        let rhs_mir_target = self.lower_qual_type(rhs_ty);

        let lhs_converted = self.apply_conversions(lhs, left_expr, lhs_mir_target);
        let rhs_converted = self.apply_conversions(rhs, right_expr, rhs_mir_target);

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

    fn visit_assignment_expr(
        &mut self,
        node: NodeRef,
        op: &BinaryOp,
        left: NodeRef,
        right: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
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
            self.visit_compound_assignment(node, compound_op, place, rhs_op, left, right, mir_ty)
        } else {
            // Simple assignment, just use the RHS
            let final_rhs = self.apply_conversions(rhs_op, right, mir_ty);

            if lhs_ty.is_atomic() {
                let ptr = Operand::AddressOf(Box::new(place.clone()));
                self.mir_builder
                    .add_statement(MirStmt::AtomicStore(ptr, final_rhs.clone(), AtomicMemOrder::SeqCst));
            } else {
                self.emit_assignment(place.clone(), final_rhs.clone());
            }

            // C11 6.5.16p3: An assignment expression has the value of the left operand after the assignment,
            // but is not an lvalue. For bit-fields, this means the value is truncated to the bit-field width.
            if let Place::StructField(_, _, Some(bit_info)) = &place {
                return self.apply_bitfield_truncation(final_rhs, bit_info, mir_ty);
            }

            final_rhs
        }
    }

    fn apply_bitfield_truncation(&mut self, op: Operand, bit_info: &BitFieldInfo, mir_ty: TypeId) -> Operand {
        let mask = if bit_info.width == 64 {
            !0u64
        } else {
            (1u64 << bit_info.width) - 1
        };

        if let Operand::Constant(const_id) = op {
            let constants = self.mir_builder.get_constants();
            let const_val = constants.get(&const_id).unwrap().clone();
            if let ConstValueKind::Int(val) = const_val.kind {
                let mask_signed = mask as i64;
                let truncated = if bit_info.is_signed {
                    // Sign extend from bit_info.width
                    let shift = 64 - bit_info.width;
                    (val << shift) >> shift
                } else {
                    val & mask_signed
                };
                let new_const = self.mir_builder.create_constant(mir_ty, ConstValueKind::Int(truncated));
                return Operand::Constant(new_const);
            }
        }

        // Non-constant: emit bitwise AND for unsigned, or shifts for signed
        if bit_info.is_signed {
            // (val << (64-width)) >> (64-width)
            let shift = (64 - bit_info.width) as i64;
            let shift_op = {
                let c = self.mir_builder.create_constant(mir_ty, ConstValueKind::Int(shift));
                Operand::Constant(c)
            };
            let lshift =
                self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::LShift, op, shift_op.clone()), mir_ty);
            self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::RShift, lshift, shift_op), mir_ty)
        } else {
            let mask_op = {
                let c = self
                    .mir_builder
                    .create_constant(mir_ty, ConstValueKind::Int(mask as i64));
                Operand::Constant(c)
            };
            self.emit_rvalue_to_operand(Rvalue::BinaryIntOp(BinaryIntOp::BitAnd, op, mask_op), mir_ty)
        }
    }

    fn visit_compound_assignment(
        &mut self,
        node: NodeRef,
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
                    self.visit_binary_arithmetic_logic(&compound_op, old_val, rhs_op, left, right, mir_ty);
                return self.emit_rvalue_to_operand(new_val_rval, mir_ty);
            }
        }

        // This is a compound assignment, e.g., a += b
        // Use the already-evaluated place to read the current value.
        let lhs_copy = Operand::Copy(Box::new(place.clone()));

        let (rval, op_ty) = self.visit_binary_arithmetic_logic(&compound_op, lhs_copy, rhs_op, left, right, mir_ty);
        let result_op = self.emit_rvalue_to_operand(rval, op_ty);

        let truncated_op = self.emit_cast(result_op, mir_ty);

        self.emit_assignment(place.clone(), truncated_op.clone());

        // C11 6.5.16p3: Bit-field truncation for compound assignment result
        let final_op = if let Place::StructField(_, _, Some(bit_info)) = &place {
            self.apply_bitfield_truncation(truncated_op, bit_info, mir_ty)
        } else {
            truncated_op
        };

        self.apply_conversions(final_op, node, mir_ty)
    }

    fn emit_cast(&mut self, operand: Operand, target_ty: TypeId) -> Operand {
        if self.get_operand_type(&operand) == target_ty {
            return operand;
        }

        // Fold constant casts if types are compatible
        if let Some(const_id) = self.operand_to_const_id(&operand) {
            let const_val = self.mir_builder.get_constants().get(&const_id).unwrap().clone();
            let mir_type = self.mir_builder.get_type(target_ty);

            let is_compatible = match (&const_val.kind, mir_type) {
                (ConstValueKind::Int(_), t) => t.is_int() || t.is_pointer(),
                (ConstValueKind::Float(_), t) => t.is_float(),
                (ConstValueKind::GlobalAddress(_, _), t) => t.is_pointer() || t.is_int(),
                (ConstValueKind::FunctionAddress(_), t) => t.is_pointer() || t.is_int(),
                _ => false,
            };

            if is_compatible {
                let truncated_kind = match const_val.kind {
                    ConstValueKind::Int(val) => ConstValueKind::Int(mir_type.truncate_int(val)),
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
            } = self.mir_builder.get_constants().get(&const_id).unwrap()
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
        self.mir_builder.add_statement(stmt);
    }

    fn visit_function_call_args(&mut self, call_expr: &ast::nodes::CallExpr) -> Vec<Operand> {
        let mut arg_operands = Vec::new();

        // Get the function type to determine parameter types for conversions
        let func_node_kind = self.ast.get_kind(call_expr.callee);
        let func_type_kind = if let NodeKind::Ident(_, sym) = func_node_kind {
            let symbol = *sym;
            let func_entry = self.symbol_table.get_symbol(symbol);
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

        for (i, arg) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
            // Note: visit_expression(CallArg) will just lower the inner expression.
            // But we use arg(the CallArg node) for implicit conversion lookup.
            let arg_operand = self.visit_expression(arg, true);

            // Apply conversions for function arguments if needed
            // The resolved type of CallArg is same as inner expr.
            let arg_ty = self.ast.get_resolved_type(arg).unwrap();
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

    fn find_member_path(&self, record_ty: semantic::TypeRef, field_name: NameId) -> Option<Vec<usize>> {
        let mut base_index = 0;
        let ty = self.registry.get(record_ty);
        if let Some((_, idx)) = ty.find_member_recursive(self.registry, field_name, &mut base_index) {
            return Some(vec![idx]);
        }
        None
    }

    fn visit_member_access(&mut self, obj: NodeRef, field_name: &NameId, is_arrow: bool) -> Operand {
        let mut obj_qt = self.ast.get_resolved_type(obj).unwrap();

        // Handle implicit conversions (like array-to-pointer decay) for arrow access
        if is_arrow && let Some(semantic_info) = &self.ast.semantic_info {
            let idx = obj.index();
            if idx < semantic_info.conversions.len() {
                for conv in &semantic_info.conversions[idx] {
                    if let Conversion::PointerDecay { to } = conv {
                        obj_qt = QualType::unqualified(*to);
                    }
                }
            }
        }

        let record_ty = if is_arrow {
            self.registry
                .get_pointee(obj_qt.ty())
                .expect("Arrow access on non-pointer type")
                .ty()
        } else {
            obj_qt.ty()
        };

        if record_ty.is_record() {
            // Validate that the field exists and get its layout information
            let path = self
                .find_member_path(record_ty, *field_name)
                .expect("Field not found - should be caught by semantic analysis");

            // Apply the chain of field accesses

            // Resolve base place
            let mut current_place = if is_arrow {
                let obj_op = self.visit_expression(obj, true);
                let obj_mir_ty = self.lower_qual_type(obj_qt);
                let obj_op_converted = self.apply_conversions(obj_op, obj, obj_mir_ty);
                self.deref_operand(obj_op_converted)
            } else {
                self.visit_expression_as_place(obj)
            };

            for field_idx in path {
                let struct_ty = self.get_place_type(&current_place);
                let mir_type = self.mir_builder.get_type(struct_ty);
                let bit_info = if let MirType::Record { layout, .. } = mir_type {
                    let field = &layout.fields[field_idx];
                    field.bit_width.and_then(|w| {
                        field.bit_offset.map(|o| BitFieldInfo {
                            width: w,
                            offset: o,
                            is_signed: field.is_signed,
                        })
                    })
                } else {
                    None
                };
                current_place = Place::StructField(Box::new(current_place), field_idx, bit_info);
            }

            Operand::Copy(Box::new(current_place))
        } else {
            panic!("Member access on non-record type");
        }
    }

    fn visit_index_access(&mut self, arr: NodeRef, idx: NodeRef) -> Operand {
        let arr_ty = self.ast.get_resolved_type(arr).unwrap();
        let idx_ty = self.ast.get_resolved_type(idx).unwrap();

        // Handle both arr[idx] and idx[arr] (subscripting is commutative in C)
        // One must be a pointer/array, the other must be an integer
        let (sequence, index) = if arr_ty.is_array() || arr_ty.is_pointer() {
            (arr, idx)
        } else if idx_ty.is_array() || idx_ty.is_pointer() {
            (idx, arr)
        } else {
            panic!("Index access: neither operand is an array or pointer type");
        };

        // In C, arr[idx] is equivalent to *(arr + idx)
        let arr_operand = self.visit_expression(sequence, true);
        let idx_operand = self.visit_expression(index, true);

        // Check if the base operand is already a pointer in MIR (e.g., VLA locals stored as pointers)
        let arr_mir_ty = self.get_operand_type(&arr_operand);
        let arr_mir_type = self.mir_builder.get_type(arr_mir_ty);
        if arr_mir_type.is_pointer() {
            // Pointer-based indexing: *(ptr + idx)
            let ptr_add = Rvalue::PtrAdd(arr_operand, idx_operand);
            let result_op = self.emit_rvalue_to_operand(ptr_add, arr_mir_ty);
            // Deref the resulting pointer
            let deref_place = self.deref_operand(result_op);
            Operand::Copy(Box::new(deref_place))
        } else {
            // Array-based indexing: use Place::ArrayIndex
            let arr_ty = self.ast.get_resolved_type(sequence).unwrap();
            let mir_ty = self.lower_qual_type(arr_ty);
            let arr_place = self.ensure_place(arr_operand, mir_ty);
            Operand::Copy(Box::new(Place::ArrayIndex(Box::new(arr_place), Box::new(idx_operand))))
        }
    }

    fn visit_inc_dec_expr(&mut self, expr: NodeRef, is_inc: bool, is_post: bool, need_value: bool) -> Operand {
        let operand = self.visit_expression(expr, true);
        let operand_ty = self.ast.get_resolved_type(expr).unwrap();
        let mir_ty = self.lower_qual_type(operand_ty);

        if self.ast.get_value_category(expr) != Some(ValueCategory::LValue) {
            panic!("Inc/Dec operand must be an lvalue");
        }

        let place = if let Operand::Copy(place) = operand.clone() {
            place
        } else {
            panic!("Inc/Dec operand is not a place");
        };

        if operand_ty.is_atomic() {
            let ptr = Operand::AddressOf(place);
            let op = if is_inc { BinaryIntOp::Add } else { BinaryIntOp::Sub };
            let step = self.create_int_operand(1);
            let rval = Rvalue::AtomicFetchOp(op, ptr, step.clone(), AtomicMemOrder::SeqCst);
            let old_val = self.emit_rvalue_to_operand(rval, mir_ty);

            if is_post {
                return old_val;
            } else {
                let bin_op = if is_inc { BinaryOp::Add } else { BinaryOp::Sub };
                let (new_val_rval, _) = self.visit_binary_arithmetic_logic(&bin_op, old_val, step, expr, expr, mir_ty);
                return self.emit_rvalue_to_operand(new_val_rval, mir_ty);
            }
        }

        // If it's post-inc/dec and we need the value, save the old value
        let old_value = if is_post && need_value {
            let rval = Rvalue::Use(operand.clone());
            let (_, temp_place) = self.create_temp_local_with_assignment(rval, mir_ty);
            Some(Operand::Copy(Box::new(temp_place)))
        } else {
            None
        };

        // Determine MIR operation and Rvalue
        let rval = self.create_inc_dec_rvalue(operand, operand_ty, is_inc);

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

    fn create_inc_dec_rvalue(&mut self, operand: Operand, operand_ty: QualType, is_inc: bool) -> Rvalue {
        let one_const = self.create_int_operand(1);
        let minus_one_const = self.create_int_operand(-1);

        if operand_ty.is_pointer() {
            let op = if is_inc { BinaryOp::Add } else { BinaryOp::Sub };
            self.create_pointer_arithmetic_rvalue(operand, one_const, op)
        } else if operand_ty.is_complex() {
            let mir_ty = self.lower_qual_type(operand_ty);
            let (real, imag) = self.get_complex_components(operand, mir_ty);
            let element_ty = match self.mir_builder.get_type(mir_ty) {
                MirType::Record { field_types, .. } => field_types[0],
                _ => unreachable!("Complex type must be a record"),
            };

            let op = if is_inc { BinaryFloatOp::Add } else { BinaryFloatOp::Sub };
            let one = self.create_constant(element_ty, ConstValueKind::Float(1.0));
            let res_real = self.emit_float_binop(op, real, Operand::Constant(one), element_ty);

            Rvalue::StructLiteral(vec![(0, res_real), (1, imag)])
        } else {
            let mir_ty_id = self.lower_qual_type(operand_ty);
            let mir_ty = self.mir_builder.get_type(mir_ty_id);

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
        let ty = self.mir_builder.get_type(ty_id);

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

    fn visit_builtin_void(&mut self, kind: &NodeKind) -> Operand {
        let stmt = match kind {
            NodeKind::BuiltinVaStart(ap, last) => {
                let ap_op = self.visit_expression(*ap, true);
                let ap = self.ensure_valist_place(ap_op);
                let last = self.visit_expression(*last, true);
                MirStmt::BuiltinVaStart(ap, last)
            }
            NodeKind::BuiltinVaEnd(ap) => {
                let ap_op = self.visit_expression(*ap, true);
                let ap = self.ensure_valist_place(ap_op);
                MirStmt::BuiltinVaEnd(ap)
            }
            NodeKind::BuiltinVaCopy(dst, src) => {
                let dst_op = self.visit_expression(*dst, true);
                let dst = self.ensure_valist_place(dst_op);
                let src_op = self.visit_expression(*src, true);
                let src = self.ensure_valist_place(src_op);
                MirStmt::BuiltinVaCopy(dst, src)
            }
            _ => unreachable!(),
        };
        self.mir_builder.add_statement(stmt);
        self.create_int_operand(0)
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
            AtomicOp::CompareExchangeN => self.visit_atomic_cmpxchg(&args, order, mir_ty),
            AtomicOp::FetchAdd => self.visit_atomic_fetch_op(BinaryIntOp::Add, &args, order, mir_ty),
            AtomicOp::FetchSub => self.visit_atomic_fetch_op(BinaryIntOp::Sub, &args, order, mir_ty),
            AtomicOp::FetchAnd => self.visit_atomic_fetch_op(BinaryIntOp::BitAnd, &args, order, mir_ty),
            AtomicOp::FetchOr => self.visit_atomic_fetch_op(BinaryIntOp::BitOr, &args, order, mir_ty),
            AtomicOp::FetchXor => self.visit_atomic_fetch_op(BinaryIntOp::BitXor, &args, order, mir_ty),
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

    fn visit_complex_binary_op(&mut self, op: &BinaryOp, lhs: Operand, rhs: Operand, mir_ty: TypeId) -> Operand {
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

                let ad = self.emit_float_binop(Mul, lhs_real, rhs_imag, element_ty);
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

    fn visit_complex_unary_op(&mut self, op: &UnaryOp, expr: NodeRef, mir_ty: TypeId) -> Operand {
        let operand = self.visit_expression(expr, true);
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
            UnaryOp::Real => real,
            UnaryOp::Imag => imag,
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                let is_inc = matches!(op, UnaryOp::PreIncrement);
                self.visit_inc_dec_expr(expr, is_inc, false, true)
            }
            _ => panic!("Unsupported complex unary operator: {:?}", op),
        }
    }

    /// Try to lower builtin float constant functions like `__builtin_inff`, `__builtin_nanf`, etc.
    /// Returns Some(Operand) if the call is a builtin float constant, None otherwise.
    fn try_visit_builtin_float_const(&mut self, call_expr: &ast::nodes::CallExpr, mir_ty: TypeId) -> Option<Operand> {
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
