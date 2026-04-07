//! Constant expression evaluation
//!
//! This module provides the functionality to evaluate constant expressions
//! at compile time, as required by the C11 standard for contexts like
//! static assertions and array sizes.

use crate::ast::literal::{FloatSuffix, IntegerSuffix, Literal};
use crate::ast::{Ast, BinaryOp, NodeKind, NodeRef, StringId, UnaryOp};
use crate::semantic::conversions::{integer_promotion, usual_arithmetic_conversions};
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

    /// Resolve type of a node, with inference fallback if semantic info is missing.
    fn resolve_type(&self, node: NodeRef) -> Option<QualType> {
        self.get_resolved_type(node).or_else(|| self.infer_type_from_node(node))
    }

    fn truncate_to_type(&self, val: i64, qt: QualType) -> i64 {
        let ty_obj = self.registry.get(qt.ty());
        ty_obj.truncate_int(val)
    }

    fn get_result_type(&self, op: BinaryOp, left: NodeRef, right: NodeRef) -> Option<QualType> {
        let left_ty = self.resolve_type(left)?;
        let right_ty = self.resolve_type(right)?;

        match op {
            BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Mul
            | BinaryOp::Div
            | BinaryOp::Mod
            | BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor => usual_arithmetic_conversions(self.registry, left_ty, right_ty),
            BinaryOp::LShift | BinaryOp::RShift => Some(integer_promotion(self.registry, left_ty, None)),
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
        let qt = self.resolve_type(expr)?;
        match op {
            UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => Some(integer_promotion(self.registry, qt, None)),
            UnaryOp::LogicNot => Some(QualType::unqualified(self.registry.type_int)),
            _ => None,
        }
    }

    /// Infer the type of an expression node from its AST kind and symbol table,
    /// without relying on semantic_info. Used during lowering when semantic_info
    /// isn't available yet (e.g., for evaluating sizeof in array sizes).
    fn infer_type_from_node(&self, node: NodeRef) -> Option<QualType> {
        match self.ast.get_kind(node) {
            NodeKind::Ident(_, sym) => {
                let symbol = self.symbol_table.get_symbol(*sym);
                Some(symbol.type_info)
            }
            NodeKind::IndexAccess(base, _) => {
                // array[index] -> element type
                let base_qt = self.resolve_type(*base)?;
                let elem_ty = self.registry.get_array_element(base_qt.ty())?;
                Some(QualType::unqualified(elem_ty))
            }
            NodeKind::MemberAccess(base, member_name, _) => {
                let base_qt = self.resolve_type(*base)?;
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
                let qt = self.resolve_type(*expr)?;
                if let Some(pointee) = self.registry.get_pointee(qt.ty()) {
                    Some(pointee)
                } else {
                    self.registry.get_array_element(qt.ty()).map(QualType::unqualified)
                }
            }
            NodeKind::Cast(target_ty, _) => Some(*target_ty),
            NodeKind::Literal(literal) => Some(self.get_literal_type(literal)),
            _ => None,
        }
    }

    fn get_literal_type(&self, literal: &Literal) -> QualType {
        let ty = match literal {
            Literal::Int { val, suffix, base } => {
                let val_u64 = *val as u64;
                let is_decimal = *base == 10;
                let mut ty = self.registry.type_long_long_unsigned;
                for cand in IntegerSuffix::get_candidates(*suffix, self.registry, is_decimal) {
                    if self.registry.is_value_fitting(val_u64, cand) {
                        ty = cand;
                        break;
                    }
                }
                ty
            }
            Literal::Char(_, prefix) => prefix.get_type(self.registry),
            Literal::Float { suffix, .. } => FloatSuffix::get_type(*suffix, self.registry),
            Literal::String(val) => {
                let parsed_str = parse_string_literal(*val);
                let len = parsed_str.values.len() + 1;
                let builtin_base = match parsed_str.builtin_type {
                    BuiltinType::Char => self.registry.type_char,
                    BuiltinType::Int => self.registry.type_int,
                    BuiltinType::UShort => self.registry.type_short_unsigned,
                    BuiltinType::UInt => self.registry.type_int_unsigned,
                    _ => self.registry.type_char,
                };
                TypeRef::new(builtin_base.base(), TypeClass::Array, 0, len as u32).unwrap()
            }
            Literal::Nullptr => self.registry.type_nullptr_t,
            Literal::True | Literal::False => self.registry.type_bool,
        };
        QualType::unqualified(ty)
    }

    fn eval_complex_part(&self, node: NodeRef, is_real: bool) -> Option<f64> {
        match self.ast.get_kind(node) {
            NodeKind::Literal(Literal::Float { val, suffix }) => match suffix {
                Some(FloatSuffix::I) | Some(FloatSuffix::IF) | Some(FloatSuffix::IL) => {
                    if is_real {
                        Some(0.0)
                    } else {
                        Some(*val)
                    }
                }
                _ => {
                    if is_real {
                        Some(*val)
                    } else {
                        Some(0.0)
                    }
                }
            },
            NodeKind::CompoundLiteral(_, init_list) => {
                if let NodeKind::InitializerList(list) = self.ast.get_kind(*init_list) {
                    let index = if is_real { 0 } else { 1 };
                    if (index as u16) < list.init_len {
                        let item = NodeRef::new(list.init_start.get() + index as u32).expect("NodeRef overflow");
                        if let NodeKind::InitializerItem(item) = self.ast.get_kind(item) {
                            return self.eval_float(item.initializer);
                        }
                    }
                    Some(0.0)
                } else {
                    None
                }
            }
            NodeKind::Cast(_, expr) => self.eval_complex_part(*expr, is_real),
            _ => {
                if is_real {
                    self.eval_float(node)
                } else {
                    let qt = self.resolve_type(node)?;
                    if qt.is_complex() { None } else { Some(0.0) }
                }
            }
        }
    }

    pub(crate) fn eval_int(&self, expr_node: NodeRef) -> Option<i64> {
        let node_kind = self.ast.get_kind(expr_node);
        match node_kind {
            NodeKind::Literal(Literal::Int { val, .. }) => Some(*val),
            NodeKind::Literal(Literal::Char(val, _)) => Some(*val as i64),
            NodeKind::Literal(Literal::True) => Some(1),
            NodeKind::Literal(Literal::False) => Some(0),
            NodeKind::Ident(_, sym) => {
                let symbol = self.symbol_table.get_symbol(*sym);
                if let SymbolKind::EnumConstant { value } = &symbol.kind {
                    Some(*value)
                } else {
                    None
                }
            }
            NodeKind::BinaryOp(op, left, right) => self.eval_binary(*op, *left, *right),
            NodeKind::UnaryOp(op, expr) => self.eval_unary(*op, *expr),
            NodeKind::SizeOfExpr(expr) => self.eval_sizeof(Some(*expr), None),
            NodeKind::SizeOfType(qt) => self.eval_sizeof(None, Some(*qt)),
            NodeKind::AlignOfExpr(expr) => self.eval_alignof(Some(*expr), None),
            NodeKind::AlignOfType(qt) => self.eval_alignof(None, Some(*qt)),
            NodeKind::GenericSelection(_) => {
                let info = self.semantic_info.or(self.ast.semantic_info.as_ref());
                if let Some(info) = info
                    && let Some(selected_expr) = info.generic_selections.get(&expr_node.index())
                {
                    return self.eval_int(*selected_expr);
                }
                None
            }
            NodeKind::BuiltinConstantP(expr) => {
                Some((self.eval_int(*expr).is_some() || self.eval_float(*expr).is_some()) as i64)
            }
            NodeKind::BuiltinExpect(exp, _) => self.eval_int(*exp),
            NodeKind::BuiltinChooseExpr(cond, true_expr, false_expr) => {
                let info = self.semantic_info.or(self.ast.semantic_info.as_ref());
                if let Some(info) = info
                    && let Some(selected_expr) = info.choose_expressions.get(&expr_node.index())
                {
                    return self.eval_int(*selected_expr);
                }
                let cond_val = self.eval_int(*cond)?;
                if cond_val != 0 {
                    self.eval_int(*true_expr)
                } else {
                    self.eval_int(*false_expr)
                }
            }
            NodeKind::TernaryOp(cond, then_expr, else_expr) => {
                let cond_val = self.eval_int(*cond)?;
                if cond_val != 0 {
                    self.eval_int(*then_expr)
                } else {
                    self.eval_int(*else_expr)
                }
            }
            NodeKind::Cast(target_qt, expr) => self.eval_cast(*target_qt, *expr),
            NodeKind::BuiltinOffsetof(ty, expr) => {
                if let Some(info) = self.semantic_info
                    && let Some(&offset) = info.offsetof_results.get(&expr_node.index())
                {
                    return Some(offset);
                }
                eval_offsetof(self, *ty, *expr)
            }
            NodeKind::BuiltinTypesCompatibleP(t1, t2) => {
                Some(self.registry.is_compatible(t1.strip_all(), t2.strip_all()) as i64)
            }
            NodeKind::BuiltinPopcount(exp) | NodeKind::BuiltinPopcountL(exp) | NodeKind::BuiltinPopcountLL(exp) => {
                self.eval_int(*exp).map(|v| v.count_ones() as i64)
            }
            NodeKind::BuiltinClz(exp) | NodeKind::BuiltinClzL(exp) | NodeKind::BuiltinClzLL(exp) => {
                let val = self.eval_int(*exp)?;
                if val == 0 {
                    return None;
                }
                let target_ty = match node_kind {
                    NodeKind::BuiltinClz(_) => self.registry.type_int,
                    NodeKind::BuiltinClzL(_) => self.registry.type_long,
                    NodeKind::BuiltinClzLL(_) => self.registry.type_long_long,
                    _ => unreachable!(),
                };
                let width = self.registry.get(target_ty).layout.as_ref()?.size * 8;
                let mask = if width == 64 { !0u64 } else { (1u64 << width) - 1 };
                let val_truncated = (val as u64) & mask;
                Some(val_truncated.leading_zeros() as i64 - (64 - width as i64))
            }
            NodeKind::BuiltinCtz(exp) | NodeKind::BuiltinCtzL(exp) | NodeKind::BuiltinCtzLL(exp) => {
                let val = self.eval_int(*exp)?;
                if val == 0 {
                    return None;
                }
                Some(val.trailing_zeros() as i64)
            }
            NodeKind::BuiltinFfs(exp) | NodeKind::BuiltinFfsL(exp) | NodeKind::BuiltinFfsLL(exp) => self
                .eval_int(*exp)
                .map(|v| if v == 0 { 0 } else { (v.trailing_zeros() + 1) as i64 }),
            NodeKind::BuiltinBswap16(exp) => self.eval_int(*exp).map(|v| (v as u16).swap_bytes() as i64),
            NodeKind::BuiltinBswap32(exp) => self.eval_int(*exp).map(|v| (v as u32).swap_bytes() as i64),
            NodeKind::BuiltinBswap64(exp) => self.eval_int(*exp).map(|v| (v as u64).swap_bytes() as i64),
            NodeKind::BuiltinFabs(exp) | NodeKind::BuiltinFabsf(exp) | NodeKind::BuiltinFabsl(exp) => {
                self.eval_float(*exp).map(|v| v.abs() as i64)
            }
            _ => None,
        }
    }

    pub(crate) fn eval_float(&self, expr: NodeRef) -> Option<f64> {
        match self.ast.get_kind(expr) {
            NodeKind::Literal(Literal::Float { val, .. }) => {
                if let Some(qt) = self.get_resolved_type(expr)
                    && qt.builtin() == Some(BuiltinType::Float)
                {
                    return Some((*val as f32) as f64);
                }
                Some(*val)
            }
            NodeKind::Literal(Literal::Int { val, .. }) => Some(*val as f64),
            NodeKind::Literal(Literal::Char(val, _)) => Some(*val as f64),
            NodeKind::Literal(Literal::True) => Some(1.0),
            NodeKind::Literal(Literal::False) => Some(0.0),
            NodeKind::BinaryOp(op, left, right) => {
                let l = self.eval_float(*left)?;
                let r = self.eval_float(*right)?;
                match op {
                    BinaryOp::Add => Some(l + r),
                    BinaryOp::Sub => Some(l - r),
                    BinaryOp::Mul => Some(l * r),
                    BinaryOp::Div => Some(l / r),
                    BinaryOp::Less => Some((l < r) as i64 as f64),
                    BinaryOp::LessEqual => Some((l <= r) as i64 as f64),
                    BinaryOp::Greater => Some((l > r) as i64 as f64),
                    BinaryOp::GreaterEqual => Some((l >= r) as i64 as f64),
                    BinaryOp::Equal => Some((l == r) as i64 as f64),
                    BinaryOp::NotEqual => Some((l != r) as i64 as f64),
                    _ => None,
                }
            }
            NodeKind::UnaryOp(op, expr) => match op {
                UnaryOp::Plus => self.eval_float(*expr),
                UnaryOp::Minus => self.eval_float(*expr).map(|v| -v),
                UnaryOp::LogicNot => self.eval_float(*expr).map(|v| (v == 0.0) as i64 as f64),
                UnaryOp::Real => self.eval_complex_part(*expr, true),
                UnaryOp::Imag => self.eval_complex_part(*expr, false),
                _ => None,
            },
            NodeKind::Cast(target_qt, expr) => {
                let val = self.eval_float(*expr)?;
                if target_qt.is_integer() {
                    Some(val.trunc())
                } else if target_qt.builtin() == Some(BuiltinType::Float) {
                    Some((val as f32) as f64)
                } else {
                    Some(val)
                }
            }
            NodeKind::BuiltinExpect(exp, _) => self.eval_float(*exp),
            NodeKind::BuiltinChooseExpr(cond, true_expr, false_expr) => {
                let info = self.semantic_info.or(self.ast.semantic_info.as_ref());
                if let Some(info) = info
                    && let Some(selected_expr) = info.choose_expressions.get(&expr.index())
                {
                    return self.eval_float(*selected_expr);
                }
                let cond_val = self.eval_int(*cond)?;
                if cond_val != 0 {
                    self.eval_float(*true_expr)
                } else {
                    self.eval_float(*false_expr)
                }
            }
            NodeKind::BuiltinFabs(exp) | NodeKind::BuiltinFabsf(exp) | NodeKind::BuiltinFabsl(exp) => {
                self.eval_float(*exp).map(|v| v.abs())
            }
            NodeKind::FunctionCall(call) => {
                let callee_kind = self.ast.get_kind(call.callee);
                let name_id = match callee_kind {
                    NodeKind::Ident(name_id, _) => name_id,
                    _ => return None,
                };

                let bn = builtin_names();
                if *name_id == bn.inff || *name_id == bn.huge_valf {
                    Some(f32::INFINITY as f64)
                } else if *name_id == bn.inf || *name_id == bn.huge_val {
                    Some(f64::INFINITY)
                } else if *name_id == bn.nanf {
                    Some(f32::NAN as f64)
                } else if *name_id == bn.nan {
                    Some(f64::NAN)
                } else {
                    None
                }
            }
            _ => self.eval_int(expr).map(|v| v as f64),
        }
    }

    fn eval_binary(&self, op: BinaryOp, left: NodeRef, right: NodeRef) -> Option<i64> {
        let is_cmp_or_logic = matches!(
            op,
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
            let is_float_op = self.resolve_type(left).is_some_and(|qt| qt.is_floating())
                || self.resolve_type(right).is_some_and(|qt| qt.is_floating());
            if is_float_op && let (Some(left_f), Some(right_f)) = (self.eval_float(left), self.eval_float(right)) {
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

        let left_val = match self.eval_int(left) {
            Some(v) => v,
            None => {
                if matches!(op, BinaryOp::LogicAnd | BinaryOp::LogicOr)
                    && let Some(left_f) = self.eval_float(left)
                {
                    if op == BinaryOp::LogicAnd {
                        if left_f == 0.0 {
                            return Some(0);
                        }
                        if let Some(right_f) = self.eval_float(right) {
                            return Some((right_f != 0.0) as i64);
                        }
                    } else {
                        if left_f != 0.0 {
                            return Some(1);
                        }
                        if let Some(right_f) = self.eval_float(right) {
                            return Some((right_f != 0.0) as i64);
                        }
                    }
                }
                return None;
            }
        };

        match op {
            BinaryOp::LogicAnd => {
                if left_val == 0 {
                    return Some(0);
                }
                return self.eval_int(right).map(|v| (v != 0) as i64);
            }
            BinaryOp::LogicOr => {
                if left_val != 0 {
                    return Some(1);
                }
                return self.eval_int(right).map(|v| (v != 0) as i64);
            }
            _ => {}
        }

        let right_val = self.eval_int(right)?;

        let (is_unsigned, is_unsigned_cmp) = self.get_unsigned_info(left, right);

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
            BinaryOp::BitOr => Some(left_val | right_val),
            BinaryOp::BitAnd => Some(left_val & right_val),
            BinaryOp::BitXor => Some(left_val ^ right_val),
            BinaryOp::LShift => Some(left_val.wrapping_shl(right_val as u32)),
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
            if let Some(res_ty) = self.get_result_type(op, left, right) {
                return Some(self.truncate_to_type(v, res_ty));
            }
            return Some(v);
        }
        None
    }

    fn eval_unary(&self, op: UnaryOp, expr: NodeRef) -> Option<i64> {
        let result = if let Some(val) = self.eval_int(expr) {
            match op {
                UnaryOp::LogicNot => Some((val == 0) as i64),
                UnaryOp::Plus => Some(val),
                UnaryOp::Minus => Some(val.wrapping_neg()),
                UnaryOp::BitNot => Some(!val),
                _ => None,
            }
        } else if let Some(f_val) = self.eval_float(expr) {
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
            if let Some(res_ty) = self.get_unary_result_type(op, expr) {
                return Some(self.truncate_to_type(v, res_ty));
            }
            return Some(v);
        }
        None
    }

    fn eval_cast(&self, target_qt: QualType, expr: NodeRef) -> Option<i64> {
        if target_qt.builtin() == Some(BuiltinType::Bool) {
            if let Some(val) = self.eval_int(expr) {
                return Some((val != 0) as i64);
            }
            if let Some(f_val) = self.eval_float(expr) {
                return Some((f_val != 0.0) as i64);
            }
            return None;
        }

        if let Some(val) = self.eval_int(expr) {
            if !target_qt.is_integer() && !target_qt.is_pointer() {
                return None;
            }
            return Some(self.truncate_to_type(val, target_qt));
        }

        if let Some(f_val) = self.eval_float(expr) {
            if !target_qt.is_integer() && !target_qt.is_pointer() {
                return None;
            }
            let op_kind = self.ast.get_kind(expr);
            if !matches!(op_kind, NodeKind::Literal(Literal::Float { .. }) | NodeKind::Cast(..)) {
                return None;
            }
            if !f_val.is_finite() {
                return None;
            }

            const I64_MIN_F64: f64 = i64::MIN as f64;
            const I64_MAX_PLUS_1_F64: f64 = 9223372036854775808.0; // 2^63

            let truncated = f_val.trunc();
            if !(I64_MIN_F64..I64_MAX_PLUS_1_F64).contains(&truncated) {
                return None;
            }
            return Some(self.truncate_to_type(truncated as i64, target_qt));
        }
        None
    }

    fn eval_sizeof(&self, expr: Option<NodeRef>, qt: Option<QualType>) -> Option<i64> {
        let ty = if let Some(e) = expr {
            self.resolve_type(e)?.ty()
        } else {
            qt?.ty()
        };
        let layout = self.registry.try_get_layout(ty)?;
        Some(layout.size as i64)
    }

    fn eval_alignof(&self, expr: Option<NodeRef>, qt: Option<QualType>) -> Option<i64> {
        if let Some(e) = expr
            && let NodeKind::Ident(_, sym) = self.ast.get_kind(e)
        {
            let symbol = self.symbol_table.get_symbol(*sym);
            if let SymbolKind::Variable { alignment, .. } = &symbol.kind
                && let Some(align) = alignment
            {
                return Some(*align as i64);
            }
        }
        let ty = if let Some(e) = expr {
            self.resolve_type(e)?.ty()
        } else {
            qt?.ty()
        };
        let layout = self.registry.try_get_layout(ty)?;
        Some(layout.alignment as i64)
    }

    fn get_unsigned_info(&self, left: NodeRef, right: NodeRef) -> (bool, bool) {
        let left_qt = self.resolve_type(left);
        let right_qt = self.resolve_type(right);
        match (left_qt, right_qt) {
            (Some(lt), Some(rt)) => {
                let lb = self.registry.get(lt.ty());
                let rb = self.registry.get(rt.ty());
                let is_unsigned = (!lb.is_signed() && lb.is_int()) || (!rb.is_signed() && rb.is_int());
                (is_unsigned, is_unsigned || lb.is_pointer() || rb.is_pointer())
            }
            (Some(qt), None) | (None, Some(qt)) => {
                let ty_obj = self.registry.get(qt.ty());
                let is_unsigned = !ty_obj.is_signed() && ty_obj.is_int();
                (is_unsigned, is_unsigned || ty_obj.is_pointer())
            }
            _ => (false, false),
        }
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
                let Some(index_val) = ctx.eval_int(index) else {
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

struct BuiltinNames {
    inff: StringId,
    huge_valf: StringId,
    inf: StringId,
    huge_val: StringId,
    nanf: StringId,
    nan: StringId,
}

fn builtin_names() -> &'static BuiltinNames {
    static NAMES: std::sync::OnceLock<BuiltinNames> = std::sync::OnceLock::new();
    NAMES.get_or_init(|| BuiltinNames {
        inff: StringId::new("__builtin_inff"),
        huge_valf: StringId::new("__builtin_huge_valf"),
        inf: StringId::new("__builtin_inf"),
        huge_val: StringId::new("__builtin_huge_val"),
        nanf: StringId::new("__builtin_nanf"),
        nan: StringId::new("__builtin_nan"),
    })
}
