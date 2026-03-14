//! Constant expression evaluation
//!
//! This module provides the functionality to evaluate constant expressions
//! at compile time, as required by the C11 standard for contexts like
//! static assertions and array sizes.

use crate::ast::literal::Literal;
use crate::ast::{Ast, BinaryOp, NodeKind, NodeRef, UnaryOp};
use crate::semantic::literal_utils::parse_string_literal;
use crate::semantic::types::TypeClass;
use crate::semantic::{BuiltinType, QualType, SemanticInfo, SymbolKind, SymbolTable, TypeRef, TypeRegistry};

/// Context for constant expression evaluation
pub(crate) struct ConstEvalCtx<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: &'a SymbolTable,
    pub(crate) registry: &'a TypeRegistry,
    pub(crate) semantic_info: Option<&'a SemanticInfo>,
}

impl<'a> ConstEvalCtx<'a> {
    fn get_resolved_type(&self, node: NodeRef) -> Option<QualType> {
        if let Some(info) = self.semantic_info {
            info.types.get(node.index()).and_then(|t| *t)
        } else {
            self.ast.get_resolved_type(node)
        }
    }

    fn truncate_to_type(&self, val: i64, qt: QualType) -> i64 {
        let ty_obj = self.registry.get(qt.ty());
        ty_obj.truncate_int(val)
    }

    fn get_result_type(&self, op: BinaryOp, left: NodeRef, right: NodeRef) -> Option<QualType> {
        let left_ty = self
            .get_resolved_type(left)
            .or_else(|| self.infer_type_from_node(left))?;
        let right_ty = self
            .get_resolved_type(right)
            .or_else(|| self.infer_type_from_node(right))?;

        match op {
            BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Mul
            | BinaryOp::Div
            | BinaryOp::Mod
            | BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor => {
                crate::semantic::conversions::usual_arithmetic_conversions(self.registry, left_ty, right_ty)
            }
            BinaryOp::LShift | BinaryOp::RShift => {
                Some(crate::semantic::conversions::integer_promotion(
                    self.registry, left_ty, None,
                ))
            }
            BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual
            | BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::LogicAnd
            | BinaryOp::LogicOr => Some(QualType::unqualified(self.registry.type_int)),
            _ => None,
        }
    }

    fn get_unary_result_type(&self, op: UnaryOp, expr: NodeRef) -> Option<QualType> {
        let qt = self
            .get_resolved_type(expr)
            .or_else(|| self.infer_type_from_node(expr))?;
        match op {
            UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => {
                Some(crate::semantic::conversions::integer_promotion(self.registry, qt, None))
            }
            UnaryOp::LogicNot => Some(QualType::unqualified(self.registry.type_int)),
            _ => None,
        }
    }

    /// Infer the type of an expression node from its AST kind and symbol table,
    /// without relying on semantic_info. Used during lowering when semantic_info
    /// isn't available yet (e.g., for evaluating sizeof in array sizes).
    fn infer_type_from_node(&self, node: NodeRef) -> Option<QualType> {
        match self.ast.get_kind(node) {
            NodeKind::Ident(_, sym_ref) => {
                let symbol = self.symbol_table.get_symbol(*sym_ref);
                Some(symbol.type_info)
            }
            NodeKind::IndexAccess(base, _) => {
                // array[index] -> element type
                let base_qt = self
                    .get_resolved_type(*base)
                    .or_else(|| self.infer_type_from_node(*base))?;
                let elem_ty = self.registry.get_array_element(base_qt.ty())?;
                Some(QualType::unqualified(elem_ty))
            }
            NodeKind::MemberAccess(base, member_name, _) => {
                let base_qt = self
                    .get_resolved_type(*base)
                    .or_else(|| self.infer_type_from_node(*base))?;
                let mut ty = base_qt.ty();
                // Dereference pointer for arrow operator
                if ty.is_pointer() {
                    ty = self.registry.get_pointee(ty)?.ty();
                }
                let type_info = self.registry.get(ty);
                let member = type_info.find_member(self.registry, *member_name)?;
                Some(member.member_type)
            }
            NodeKind::UnaryOp(UnaryOp::Deref, expr) => {
                let qt = self
                    .get_resolved_type(*expr)
                    .or_else(|| self.infer_type_from_node(*expr))?;
                let pointee = self.registry.get_pointee(qt.ty())?;
                Some(pointee)
            }
            NodeKind::Cast(target_ty, _) => Some(*target_ty),
            NodeKind::Literal(Literal::Int { val, suffix, base }) => {
                let val_u64 = *val as u64;
                let is_decimal = *base == 10;
                let ty = match suffix {
                    None => {
                        // C11 6.4.4.1: Determine type by smallest that fits.
                        // For decimal: int, long, long long.
                        // For oct/hex: also include the unsigned variants.
                        if is_decimal {
                            if val_u64 <= i32::MAX as u64 {
                                self.registry.type_int
                            } else if val_u64 <= i64::MAX as u64 {
                                // On 64-bit, long and long long are same size
                                self.registry.type_long_long
                            } else {
                                self.registry.type_long_long_unsigned
                            }
                        } else {
                            if val_u64 <= i32::MAX as u64 {
                                self.registry.type_int
                            } else if val_u64 <= u32::MAX as u64 {
                                self.registry.type_int_unsigned
                            } else if val_u64 <= i64::MAX as u64 {
                                self.registry.type_long_long
                            } else {
                                self.registry.type_long_long_unsigned
                            }
                        }
                    }
                    Some(crate::ast::literal::IntegerSuffix::U) => self.registry.type_int_unsigned,
                    Some(crate::ast::literal::IntegerSuffix::L) => self.registry.type_long,
                    Some(crate::ast::literal::IntegerSuffix::UL) => self.registry.type_long_unsigned,
                    Some(crate::ast::literal::IntegerSuffix::LL) => self.registry.type_long_long,
                    Some(crate::ast::literal::IntegerSuffix::ULL) => self.registry.type_long_long_unsigned,
                };
                Some(QualType::unqualified(ty))
            }
            NodeKind::Literal(Literal::Char(_)) => Some(QualType::unqualified(self.registry.type_int)),
            NodeKind::Literal(Literal::Float { .. }) => Some(QualType::unqualified(self.registry.type_double)),
            NodeKind::Literal(Literal::String(val)) => {
                let parsed_str = parse_string_literal(*val);
                let len = parsed_str.values.len() + 1;
                let builtin_base = match parsed_str.builtin_type {
                    BuiltinType::Char => self.registry.type_char,
                    BuiltinType::Int => self.registry.type_int,
                    BuiltinType::UShort => self.registry.type_short_unsigned,
                    BuiltinType::UInt => self.registry.type_int_unsigned,
                    _ => self.registry.type_char,
                };
                Some(QualType::unqualified(
                    TypeRef::new(builtin_base.base(), TypeClass::Array, 0, len as u32).unwrap(),
                ))
            }
            _ => None,
        }
    }
}

/// Evaluate a constant expression node to an i64 value
pub(crate) fn eval_const_expr(ctx: &ConstEvalCtx, expr_node: NodeRef) -> Option<i64> {
    let node_kind = ctx.ast.get_kind(expr_node);
    match node_kind {
        NodeKind::Literal(Literal::Int { val, .. }) => Some(*val),
        NodeKind::Literal(Literal::Char(val)) => Some(*val as i64),
        NodeKind::Ident(_, sym_ref) => {
            let symbol = ctx.symbol_table.get_symbol(*sym_ref);
            if let SymbolKind::EnumConstant { value } = &symbol.kind {
                Some(*value)
            } else {
                None
            }
        }
        NodeKind::BinaryOp(op, left, right) => {
            let is_cmp_or_logic = matches!(
                *op,
                BinaryOp::Equal
                    | BinaryOp::NotEqual
                    | BinaryOp::Less
                    | BinaryOp::LessEqual
                    | BinaryOp::Greater
                    | BinaryOp::GreaterEqual
                    | BinaryOp::LogicAnd
                    | BinaryOp::LogicOr
            );

            if is_cmp_or_logic {
                let is_float_op = ctx.get_resolved_type(*left).is_some_and(|ty| ty.ty().is_floating())
                    || ctx.get_resolved_type(*right).is_some_and(|ty| ty.ty().is_floating());
                if is_float_op
                    && let (Some(left_f), Some(right_f)) =
                        (eval_const_expr_float(ctx, *left), eval_const_expr_float(ctx, *right))
                {
                    return match op {
                        BinaryOp::Equal => Some((left_f == right_f) as i64),
                        BinaryOp::NotEqual => Some((left_f != right_f) as i64),
                        BinaryOp::Less => Some((left_f < right_f) as i64),
                        BinaryOp::LessEqual => Some((left_f <= right_f) as i64),
                        BinaryOp::Greater => Some((left_f > right_f) as i64),
                        BinaryOp::GreaterEqual => Some((left_f >= right_f) as i64),
                        BinaryOp::LogicAnd => Some(((left_f != 0.0) && (right_f != 0.0)) as i64),
                        BinaryOp::LogicOr => Some(((left_f != 0.0) || (right_f != 0.0)) as i64),
                        _ => None,
                    };
                }
            }

            // If the operator is logic and/or, try fallback to float evaluation if it doesn't evaluate as an integer
            let left_val = match eval_const_expr(ctx, *left) {
                Some(v) => v,
                None => {
                    if matches!(op, BinaryOp::LogicAnd | BinaryOp::LogicOr) {
                        let is_float_op = ctx.get_resolved_type(*left).is_some_and(|qt| qt.ty().is_floating())
                            || ctx.get_resolved_type(*right).is_some_and(|qt| qt.ty().is_floating());
                        if is_float_op {
                            if *op == BinaryOp::LogicAnd {
                                if let Some(left_f) = eval_const_expr_float(ctx, *left) {
                                    if left_f == 0.0 {
                                        return Some(0);
                                    }
                                    if let Some(right_f) = eval_const_expr_float(ctx, *right) {
                                        return Some((right_f != 0.0) as i64);
                                    }
                                }
                            } else if let Some(left_f) = eval_const_expr_float(ctx, *left) {
                                if left_f != 0.0 {
                                    return Some(1);
                                }
                                if let Some(right_f) = eval_const_expr_float(ctx, *right) {
                                    return Some((right_f != 0.0) as i64);
                                }
                            }
                        }
                    }
                    return None;
                }
            };

            // Short-circuiting logic
            match op {
                BinaryOp::LogicAnd => {
                    if left_val == 0 {
                        return Some(0);
                    }
                    let right_val = eval_const_expr(ctx, *right)?;
                    return Some((right_val != 0) as i64);
                }
                BinaryOp::LogicOr => {
                    if left_val != 0 {
                        return Some(1);
                    }
                    let right_val = eval_const_expr(ctx, *right)?;
                    return Some((right_val != 0) as i64);
                }
                _ => {}
            }

            let right_val = eval_const_expr(ctx, *right)?;

            // Determine if operation should be unsigned
            let (is_unsigned, is_unsigned_cmp) = {
                let left_ty = ctx.get_resolved_type(*left);
                let right_ty = ctx.get_resolved_type(*right);

                match (left_ty, right_ty) {
                    (Some(lt), Some(rt)) => {
                        let lb = ctx.registry.get(lt.ty());
                        let rb = ctx.registry.get(rt.ty());
                        let is_unsigned = (!lb.is_signed() && lb.is_int()) || (!rb.is_signed() && rb.is_int());
                        let is_unsigned_cmp = is_unsigned || lb.is_pointer() || rb.is_pointer();
                        (is_unsigned, is_unsigned_cmp)
                    }
                    (Some(ty), None) | (None, Some(ty)) => {
                        let ty_obj = ctx.registry.get(ty.ty());
                        let is_unsigned = !ty_obj.is_signed() && ty_obj.is_int();
                        (is_unsigned, is_unsigned || ty_obj.is_pointer())
                    }
                    (None, None) => (false, false),
                }
            };

            let result = match op {
                BinaryOp::Add => Some(left_val.wrapping_add(right_val)),
                BinaryOp::Sub => Some(left_val.wrapping_sub(right_val)),
                BinaryOp::Mul => Some(left_val.wrapping_mul(right_val)),
                BinaryOp::Div => {
                    if right_val == 0 {
                        None
                    } else if is_unsigned {
                        Some((left_val as u64).wrapping_div(right_val as u64) as i64)
                    } else {
                        Some(left_val.wrapping_div(right_val))
                    }
                }
                BinaryOp::Mod => {
                    if right_val == 0 {
                        None
                    } else if is_unsigned {
                        Some((left_val as u64).wrapping_rem(right_val as u64) as i64)
                    } else {
                        Some(left_val.wrapping_rem(right_val))
                    }
                }
                BinaryOp::Equal => Some((left_val == right_val) as i64),
                BinaryOp::NotEqual => Some((left_val != right_val) as i64),
                BinaryOp::Less => {
                    if is_unsigned_cmp {
                        Some(((left_val as u64) < (right_val as u64)) as i64)
                    } else {
                        Some((left_val < right_val) as i64)
                    }
                }
                BinaryOp::LessEqual => {
                    if is_unsigned_cmp {
                        Some(((left_val as u64) <= (right_val as u64)) as i64)
                    } else {
                        Some((left_val <= right_val) as i64)
                    }
                }
                BinaryOp::Greater => {
                    if is_unsigned_cmp {
                        Some(((left_val as u64) > (right_val as u64)) as i64)
                    } else {
                        Some((left_val > right_val) as i64)
                    }
                }
                BinaryOp::GreaterEqual => {
                    if is_unsigned_cmp {
                        Some(((left_val as u64) >= (right_val as u64)) as i64)
                    } else {
                        Some((left_val >= right_val) as i64)
                    }
                }
                // LogicAnd/LogicOr handled above
                BinaryOp::BitOr => Some(left_val | right_val),
                BinaryOp::BitAnd => Some(left_val & right_val),
                BinaryOp::BitXor => Some(left_val ^ right_val),
                BinaryOp::LShift => {
                    // Safe shift, handle overflow or large shift count by wrapping or masking
                    Some(left_val.wrapping_shl(right_val as u32))
                }
                BinaryOp::RShift => {
                    if is_unsigned {
                        Some((left_val as u64).wrapping_shr(right_val as u32) as i64)
                    } else {
                        Some(left_val.wrapping_shr(right_val as u32))
                    }
                }
                _ => None,
            };

            if let Some(v) = result {
                if let Some(res_ty) = ctx.get_result_type(*op, *left, *right) {
                    return Some(ctx.truncate_to_type(v, res_ty));
                }
                return Some(v);
            }
            None
        }
        NodeKind::UnaryOp(op, expr) => {
            let result = if let Some(operand_val) = eval_const_expr(ctx, *expr) {
                match op {
                    UnaryOp::LogicNot => Some((operand_val == 0) as i64),
                    UnaryOp::Plus => Some(operand_val),
                    UnaryOp::Minus => Some(operand_val.wrapping_neg()),
                    UnaryOp::BitNot => Some(!operand_val),
                    _ => None,
                }
            } else if let Some(f_val) = eval_const_expr_float(ctx, *expr) {
                match op {
                    UnaryOp::LogicNot => Some((f_val == 0.0) as i64),
                    UnaryOp::Plus => Some(f_val as i64),
                    UnaryOp::Minus => Some(-(f_val as i64)),
                    _ => None,
                }
            } else {
                None
            };

            if let Some(v) = result {
                if let Some(res_ty) = ctx.get_unary_result_type(*op, *expr) {
                    return Some(ctx.truncate_to_type(v, res_ty));
                }
                return Some(v);
            }
            None
        }
        NodeKind::SizeOfExpr(expr) => {
            let qt = ctx
                .get_resolved_type(*expr)
                .or_else(|| ctx.infer_type_from_node(*expr))?;
            let layout = ctx.registry.try_get_layout(qt.ty())?;
            Some(layout.size as i64)
        }
        NodeKind::AlignOf(qt) => {
            let layout = ctx.registry.try_get_layout(qt.ty())?;
            Some(layout.alignment as i64)
        }
        NodeKind::SizeOfType(qt) => {
            let layout = ctx.registry.try_get_layout(qt.ty())?;
            Some(layout.size as i64)
        }
        NodeKind::GenericSelection(_) => {
            let info = ctx.semantic_info.or(ctx.ast.semantic_info.as_ref());
            if let Some(info) = info
                && let Some(selected_expr) = info.generic_selections.get(&expr_node.index())
            {
                return eval_const_expr(ctx, *selected_expr);
            }
            None
        }
        NodeKind::BuiltinConstantP(expr) => {
            if eval_const_expr(ctx, *expr).is_some() {
                Some(1)
            } else {
                Some(0)
            }
        }
        NodeKind::BuiltinChooseExpr(cond, true_expr, false_expr) => {
            let info = ctx.semantic_info.or(ctx.ast.semantic_info.as_ref());
            if let Some(info) = info
                && let Some(selected_expr) = info.choose_expressions.get(&expr_node.index())
            {
                return eval_const_expr(ctx, *selected_expr);
            }

            let cond_val = eval_const_expr(ctx, *cond)?;
            if cond_val != 0 {
                eval_const_expr(ctx, *true_expr)
            } else {
                eval_const_expr(ctx, *false_expr)
            }
        }
        NodeKind::TernaryOp(cond, then_expr, else_expr) => {
            let cond_val = eval_const_expr(ctx, *cond)?;
            if cond_val != 0 {
                eval_const_expr(ctx, *then_expr)
            } else {
                eval_const_expr(ctx, *else_expr)
            }
        }
        NodeKind::Cast(target_ty, expr) => {
            let kind = ctx.ast.get_kind(*expr);

            if target_ty.ty().builtin() == Some(BuiltinType::Bool) {
                if let Some(val) = eval_const_expr(ctx, *expr) {
                    return Some((val != 0) as i64);
                } else if let Some(f_val) = eval_const_expr_float(ctx, *expr) {
                    // C11 6.3.1.2: Any scalar value converts to 1 if it compares unequal to 0, otherwise 0.
                    // NaN compares unequal to 0.0, so (bool)NaN is 1.
                    return Some((f_val != 0.0) as i64);
                } else {
                    return None;
                }
            }

            let val = if let Some(val) = eval_const_expr(ctx, *expr) {
                val
            } else if let NodeKind::Literal(Literal::Float { val: f_val, .. }) = kind {
                if !f_val.is_finite() {
                    return None;
                }
                let truncated = f_val.trunc();
                if !(-9223372036854775808.0..9223372036854775808.0).contains(&truncated) {
                    return None;
                }
                truncated as i64
            } else {
                return None;
            };

            if !target_ty.is_integer() && !target_ty.is_pointer() {
                return None;
            }

            let target_type_obj = ctx.registry.get(target_ty.ty());
            Some(target_type_obj.truncate_int(val))
        }
        NodeKind::BuiltinOffsetof(ty, expr) => {
            if let Some(info) = ctx.semantic_info
                && let Some(&offset) = info.offsetof_results.get(&expr_node.index())
            {
                return Some(offset);
            }
            eval_offsetof(ctx, *ty, *expr)
        }
        NodeKind::BuiltinTypesCompatibleP(t1, t2) => {
            let t1_unqual = t1.strip_all();
            let t2_unqual = t2.strip_all();
            Some(ctx.registry.is_compatible(t1_unqual, t2_unqual) as i64)
        }
        NodeKind::BuiltinPopcount(exp) => {
            let val = eval_const_expr(ctx, *exp)?;
            Some(val.count_ones() as i64)
        }
        NodeKind::BuiltinClz(exp) => {
            let val = eval_const_expr(ctx, *exp)?;
            if val == 0 {
                None // Undefined behavior for 0, return None
            } else {
                Some(val.leading_zeros() as i64)
            }
        }
        NodeKind::BuiltinCtz(exp) => {
            let val = eval_const_expr(ctx, *exp)?;
            if val == 0 {
                None // Undefined behavior for 0, return None
            } else {
                Some(val.trailing_zeros() as i64)
            }
        }
        NodeKind::BuiltinFfs(exp) => {
            let val = eval_const_expr(ctx, *exp)?;
            if val == 0 {
                Some(0)
            } else {
                Some((val.trailing_zeros() + 1) as i64)
            }
        }
        _ => None,
    }
}

/// Evaluate a constant expression node to an f64 value
///
/// This function handles floating-point operations specifically and falls back to integer evaluation
/// for other types, converting the result to f64.
pub(crate) fn eval_const_expr_float(ctx: &ConstEvalCtx, expr_node: NodeRef) -> Option<f64> {
    let node_kind = ctx.ast.get_kind(expr_node);
    match node_kind {
        NodeKind::Literal(Literal::Float { val, .. }) => Some(*val),
        NodeKind::Literal(Literal::Int { val, .. }) => Some(*val as f64),
        NodeKind::Literal(Literal::Char(val)) => Some(*val as f64),
        NodeKind::BinaryOp(op, left, right) => {
            let left_val = eval_const_expr_float(ctx, *left)?;
            let right_val = eval_const_expr_float(ctx, *right)?;
            match op {
                BinaryOp::Add => Some(left_val + right_val),
                BinaryOp::Sub => Some(left_val - right_val),
                BinaryOp::Mul => Some(left_val * right_val),
                BinaryOp::Div => Some(left_val / right_val),
                BinaryOp::Less => Some((left_val < right_val) as i64 as f64),
                BinaryOp::LessEqual => Some((left_val <= right_val) as i64 as f64),
                BinaryOp::Greater => Some((left_val > right_val) as i64 as f64),
                BinaryOp::GreaterEqual => Some((left_val >= right_val) as i64 as f64),
                BinaryOp::Equal => Some((left_val == right_val) as i64 as f64),
                BinaryOp::NotEqual => Some((left_val != right_val) as i64 as f64),
                _ => None,
            }
        }
        NodeKind::UnaryOp(op, expr) => {
            let operand_val = eval_const_expr_float(ctx, *expr)?;
            match op {
                UnaryOp::Plus => Some(operand_val),
                UnaryOp::Minus => Some(-operand_val),
                UnaryOp::LogicNot => Some((operand_val == 0.0) as i64 as f64),
                _ => None,
            }
        }
        NodeKind::Cast(target_ty, expr) => {
            if let Some(val) = eval_const_expr_float(ctx, *expr) {
                if target_ty.is_integer() {
                    Some(val.trunc())
                } else {
                    Some(val)
                }
            } else {
                None
            }
        }
        _ => eval_const_expr(ctx, expr_node).map(|v| v as f64),
    }
}

fn eval_offsetof(ctx: &ConstEvalCtx, qt: QualType, expr: NodeRef) -> Option<i64> {
    let mut current_qt = qt;
    let mut offset = 0i64;

    fn walk(ctx: &ConstEvalCtx, node: NodeRef, current_qt: &mut QualType, offset: &mut i64) -> bool {
        match *ctx.ast.get_kind(node) {
            NodeKind::Dummy => true,
            NodeKind::MemberAccess(base, member_name, is_arrow) => {
                debug_assert!(!is_arrow, "offsetof does not support arrow operator");

                if !walk(ctx, base, current_qt, offset) {
                    return false;
                }

                let record_ty = current_qt.ty();

                if !record_ty.is_record() {
                    return false;
                }

                let mut base_index = 0;
                let ty_info = ctx.registry.get(record_ty);
                if let Some((member, field, _)) =
                    ty_info.find_member_with_offset(ctx.registry, member_name, 0, &mut base_index)
                {
                    *offset += field.offset as i64;
                    *current_qt = member.member_type;
                    true
                } else {
                    false
                }
            }
            NodeKind::IndexAccess(base, index) => {
                if !walk(ctx, base, current_qt, offset) {
                    return false;
                }

                let Some(elem_ty) = ctx.registry.get_array_element(current_qt.ty()) else {
                    return false;
                };
                let Some(index_val) = eval_const_expr(ctx, index) else {
                    return false;
                };

                let layout = ctx.registry.get_layout(elem_ty);
                *offset += index_val * (layout.size as i64);
                *current_qt = QualType::unqualified(elem_ty);
                true
            }
            _ => false,
        }
    }

    if walk(ctx, expr, &mut current_qt, &mut offset) {
        Some(offset)
    } else {
        None
    }
}
