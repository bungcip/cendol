//! Constant expression evaluation
//!
//! This module provides the functionality to evaluate constant expressions
//! at compile time, as required by the C11 standard for contexts like
//! static assertions and array sizes.

use crate::ast::literal::{FloatSuffix, LitVal};
use crate::ast::{Ast, BinaryOp, NodeKind, NodeRef, StringId, UnaryOp};
use crate::semantic::conversions::{integer_promotion, usual_arithmetic_conversions};
use crate::semantic::literal_utils::{get_string_builtin_type, get_string_literal_size};
use crate::semantic::types::ArraySizeType;
use crate::semantic::{BuiltinType, QualType, SemanticInfo, SymbolKind, SymbolTable, TypeKind, TypeRef, TypeRegistry};

fn has_unresolved_typeof(registry: &TypeRegistry, ty: TypeRef) -> bool {
    let mut current = ty;
    // Follow aliases first
    loop {
        match &registry.get(current).kind {
            TypeKind::Alias(inner) => current = *inner,
            TypeKind::TypeofExpr(_) | TypeKind::TypeofUnqualExpr(_) => return true,
            _ => break,
        }
    }
    // Now check recursively for pointer or array elements
    match &registry.get(current).kind {
        TypeKind::Pointer { pointee } => has_unresolved_typeof(registry, pointee.ty()),
        TypeKind::Array { element_type, .. } => has_unresolved_typeof(registry, *element_type),
        _ => false,
    }
}

/// Context for constant expression evaluation
pub(crate) struct ConstEvalCtx<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: &'a SymbolTable,
    pub(crate) registry: &'a TypeRegistry,
    pub(crate) semantic_info: &'a SemanticInfo,
}

impl<'a> ConstEvalCtx<'a> {
    fn get_resolved_type(&self, node: NodeRef) -> Option<QualType> {
        self.semantic_info
            .types
            .get(node.index())
            .and_then(|t| *t)
            .or_else(|| self.ast.get_resolved_type(node))
    }

    /// Resolve type of a node, with inference fallback if semantic info is missing.
    fn resolve_type(&self, node: NodeRef) -> Option<QualType> {
        self.get_resolved_type(node).or_else(|| self.infer_type_from_node(node))
    }

    fn select_generic_branch(&self, gs: &crate::ast::nodes::GenericSelection) -> Option<NodeRef> {
        let ctrl_ty = self.resolve_type(gs.control)?;
        let decayed_ctrl = self.registry.find_decayed_type(ctrl_ty)?;
        let unqualified_ctrl = decayed_ctrl.strip_all();

        let mut selected_expr = None;
        let mut default_expr = None;

        for assoc_node in gs.assoc_start.range(gs.assoc_len) {
            if let NodeKind::GenericAssociation(ga) = self.ast.get_kind(assoc_node) {
                if let Some(assoc_qt) = ga.ty {
                    let decayed_assoc = self.registry.find_decayed_type(assoc_qt).unwrap_or(assoc_qt);
                    if self.registry.is_compatible(unqualified_ctrl, decayed_assoc) {
                        selected_expr = Some(ga.result_expr);
                        break;
                    }
                } else {
                    default_expr = Some(ga.result_expr);
                }
            }
        }

        selected_expr.or(default_expr)
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
            NodeKind::UnaryOp(op, expr) => {
                let qt = self.resolve_type(*expr)?;
                match op {
                    UnaryOp::AddrOf => {
                        let ptr = self.registry.find_pointer_to(qt)?;
                        Some(QualType::unqualified(ptr))
                    }
                    UnaryOp::LogicNot => Some(QualType::unqualified(self.registry.type_int)),
                    UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => {
                        Some(integer_promotion(self.registry, qt, None))
                    }
                    _ => None,
                }
            }
            NodeKind::BinaryOp(op, left, right) => self.get_result_type(*op, *left, *right),
            NodeKind::TernaryOp(_, then_expr, else_expr) => {
                let t = self.resolve_type(*then_expr)?;
                let e = self.resolve_type(*else_expr)?;

                if t.is_arithmetic() && e.is_arithmetic() {
                    usual_arithmetic_conversions(self.registry, t, e)
                } else if t.ty() == e.ty() {
                    self.registry.find_composite_type(t, e)
                } else if t.is_void() {
                    Some(t)
                } else if e.is_void() {
                    Some(e)
                } else if t.is_pointer() && e.is_pointer() {
                    let p_t = self.registry.get_pointee(t.ty())?;
                    let p_e = self.registry.get_pointee(e.ty())?;
                    if p_t.is_void() || p_e.is_void() {
                        let res_quals = p_t.qualifiers() | p_e.qualifiers();
                        let void_ptr = self
                            .registry
                            .find_pointer_to(QualType::new(self.registry.type_void, res_quals))?;
                        Some(QualType::unqualified(void_ptr))
                    } else if self.registry.is_compatible(p_t.strip_all(), p_e.strip_all()) {
                        let res_p_quals = p_t.qualifiers() | p_e.qualifiers();
                        let p_composite = self.registry.find_composite_type(p_t.strip_all(), p_e.strip_all())?;
                        let res_p_ty = QualType::new(p_composite.ty(), res_p_quals);
                        let ptr = self.registry.find_pointer_to(res_p_ty)?;
                        Some(QualType::unqualified(ptr))
                    } else {
                        None
                    }
                } else {
                    usual_arithmetic_conversions(self.registry, t, e)
                }
            }
            NodeKind::Cast(target_ty, _) => Some(target_ty.strip_all()),
            NodeKind::Literal(literal) => Some(self.get_literal_type(&literal.get_val())),
            NodeKind::StatementExpr(_, result_expr) => self.resolve_type(*result_expr),
            NodeKind::GenericSelection(gs) => {
                let selected = self.select_generic_branch(gs)?;
                self.resolve_type(selected)
            }
            _ => None,
        }
    }

    fn get_literal_type(&self, literal: &LitVal) -> QualType {
        let ty = match literal {
            LitVal::Int { value, suffix, radix } => {
                let is_decimal = *radix == 10;
                let mut ty = self.registry.type_long_long_unsigned;
                for cand in suffix.get_candidates(self.registry, is_decimal) {
                    if self.registry.is_literal_fitting(*value, cand) {
                        ty = cand;
                        break;
                    }
                }
                ty
            }
            LitVal::Char(_, prefix) => prefix.get_type(self.registry),
            LitVal::Float { suffix, .. } => suffix.get_type(self.registry),
            LitVal::String { value, prefix } => {
                // Bolt ⚡: Use metadata-only accessors.
                let builtin_type = get_string_builtin_type(*prefix);
                let size = get_string_literal_size(value, *prefix);
                let builtin_base = match builtin_type {
                    BuiltinType::Char => self.registry.type_char,
                    BuiltinType::Int => self.registry.type_int,
                    BuiltinType::UShort => self.registry.type_short_unsigned,
                    BuiltinType::UInt => self.registry.type_int_unsigned,
                    BuiltinType::UChar => self.registry.type_char_unsigned,
                    _ => self.registry.type_char,
                };
                self.registry
                    .find_array_type(builtin_base, ArraySizeType::Constant(size))
                    .unwrap_or(self.registry.type_error)
            }
            LitVal::Nullptr => self.registry.type_nullptr_t,
            LitVal::True | LitVal::False => self.registry.type_bool,
        };
        QualType::unqualified(ty)
    }

    fn eval_complex_part(&self, node: NodeRef, is_real: bool) -> Option<f64> {
        match self.ast.get_kind(node) {
            NodeKind::Literal(lid) => {
                if let lit @ LitVal::Float { suffix, .. } = &lid.get_val() {
                    let is_imaginary = matches!(suffix, FloatSuffix::I | FloatSuffix::IF | FloatSuffix::IL);
                    Some(if is_real == is_imaginary { 0.0 } else { lit.as_f64() })
                } else {
                    None
                }
            }
            NodeKind::CompoundLiteral(_, init_list) => {
                if let NodeKind::InitializerList(list) = self.ast.get_kind(*init_list) {
                    let index = if is_real { 0 } else { 1 };
                    if index < list.init_len {
                        let item_kind = self.ast.get_kind(list.init_start.add_offset(index));
                        if let NodeKind::InitializerItem(item) = item_kind {
                            return self.eval_float(item.initializer);
                        }
                    }
                    Some(0.0)
                } else {
                    None
                }
            }
            NodeKind::Cast(_, expr) => self.eval_complex_part(*expr, is_real),
            NodeKind::BuiltinComplex(real, imag) => self.eval_float(if is_real { *real } else { *imag }),
            _ => {
                if is_real {
                    self.eval_float(node)
                } else {
                    let qt = self.resolve_type(node)?;
                    (!qt.is_complex()).then_some(0.0)
                }
            }
        }
    }

    pub(crate) fn eval_int(&self, expr_node: NodeRef) -> Option<i64> {
        let node_kind = self.ast.get_kind(expr_node);
        match node_kind {
            NodeKind::Literal(lit) => match lit.get_val() {
                LitVal::Int { value, .. } => Some(value),
                LitVal::Char(value, _) => Some(value as i64),
                LitVal::True => Some(1),
                LitVal::False => Some(0),
                _ => None,
            },
            NodeKind::Ident(_, sym) => {
                let symbol = self.symbol_table.get_symbol(*sym);
                match &symbol.kind {
                    SymbolKind::EnumConstant { value } => Some(*value),
                    _ => None,
                }
            }
            NodeKind::BinaryOp(op, left, right) => self.eval_binary(*op, *left, *right),
            NodeKind::UnaryOp(op, expr) => self.eval_unary(*op, *expr),
            NodeKind::SizeOfExpr(expr) => self.eval_sizeof(Some(*expr), None),
            NodeKind::SizeOfType(qt) => self.eval_sizeof(None, Some(*qt)),
            NodeKind::AlignOfExpr(expr) => self.eval_alignof(Some(*expr), None),
            NodeKind::AlignOfType(qt) => self.eval_alignof(None, Some(*qt)),
            NodeKind::GenericSelection(gs) => {
                let selected = self
                    .semantic_info
                    .generic_selections
                    .get(&expr_node.index())
                    .copied()
                    .or_else(|| self.select_generic_branch(gs))?;
                self.eval_int(selected)
            }
            NodeKind::BuiltinChooseExpr(cond, true_expr, false_expr) => {
                if let Some(&selected) = self.semantic_info.choose_expressions.get(&expr_node.index()) {
                    return self.eval_int(selected);
                }
                if self.eval_int(*cond)? != 0 {
                    self.eval_int(*true_expr)
                } else {
                    self.eval_int(*false_expr)
                }
            }
            NodeKind::TernaryOp(cond, then_expr, else_expr) => {
                if self.eval_int(*cond)? != 0 {
                    self.eval_int(*then_expr)
                } else {
                    self.eval_int(*else_expr)
                }
            }
            NodeKind::Cast(target_qt, expr) => self.eval_cast(*target_qt, *expr),
            NodeKind::BuiltinOffsetof(ty, expr) => {
                if let Some(&offset) = self.semantic_info.offsetof_results.get(&expr_node.index()) {
                    return Some(offset);
                }
                eval_offsetof(self, *ty, *expr)
            }
            NodeKind::BuiltinTypesCompatibleP(t1, t2) => {
                if has_unresolved_typeof(self.registry, t1.ty()) || has_unresolved_typeof(self.registry, t2.ty()) {
                    return None;
                }
                let res = self.registry.is_compatible(t1.strip_all(), t2.strip_all());
                Some(res as i64)
            }
            NodeKind::BuiltinComplex(real, _) => self.eval_int(*real),
            NodeKind::FunctionCall(call) => {
                let callee_kind = self.ast.get_kind(call.callee);
                let name_id = match callee_kind {
                    NodeKind::Ident(name_id, _) => name_id,
                    _ => return None,
                };

                let bn = builtin_names();
                if *name_id == bn.popcount || *name_id == bn.popcountl || *name_id == bn.popcountll {
                    let arg = call.arg_start;
                    return self.eval_int(arg).map(|v| v.count_ones() as i64);
                }
                if *name_id == bn.clz || *name_id == bn.clzl || *name_id == bn.clzll {
                    let arg = call.arg_start;
                    let val = self.eval_int(arg)?;
                    if val == 0 {
                        return None;
                    }
                    let target_ty = if *name_id == bn.clz {
                        self.registry.type_int
                    } else if *name_id == bn.clzl {
                        self.registry.type_long
                    } else {
                        self.registry.type_long_long
                    };
                    let width = self.registry.get(target_ty).width() as i64;
                    let val_truncated = (val as u64) & if width == 64 { !0u64 } else { (1u64 << width) - 1 };
                    return Some(val_truncated.leading_zeros() as i64 - (64 - width));
                }
                if *name_id == bn.ctz || *name_id == bn.ctzl || *name_id == bn.ctzll {
                    let arg = call.arg_start;
                    let val = self.eval_int(arg)?;
                    if val == 0 {
                        return None;
                    }
                    return Some(val.trailing_zeros() as i64);
                }
                if *name_id == bn.ffs || *name_id == bn.ffsl || *name_id == bn.ffsll {
                    let arg = call.arg_start;
                    return self
                        .eval_int(arg)
                        .map(|v| if v == 0 { 0 } else { (v.trailing_zeros() + 1) as i64 });
                }
                if *name_id == bn.bswap16 || *name_id == bn.bswap32 || *name_id == bn.bswap64 {
                    let arg = call.arg_start;
                    let val = self.eval_int(arg)?;
                    return Some(if *name_id == bn.bswap16 {
                        (val as u16).swap_bytes() as i64
                    } else if *name_id == bn.bswap32 {
                        (val as u32).swap_bytes() as i64
                    } else {
                        (val as u64).swap_bytes() as i64
                    });
                }
                if *name_id == bn.constant_p {
                    let arg = call.arg_start;
                    return Some((self.eval_int(arg).is_some() || self.eval_float(arg).is_some()) as i64);
                }
                if *name_id == bn.expect {
                    let arg = call.arg_start;
                    return self.eval_int(arg);
                }
                if *name_id == bn.fabs || *name_id == bn.fabsf || *name_id == bn.fabsl {
                    return self.eval_float(expr_node).map(|v| v as i64);
                }
                None
            }
            _ => None,
        }
    }

    pub(crate) fn eval_float(&self, expr: NodeRef) -> Option<f64> {
        match self.ast.get_kind(expr) {
            NodeKind::Literal(lit) => match lit.get_val() {
                lit @ LitVal::Float { .. } => {
                    let fval = lit.as_f64();
                    if let Some(qt) = self.get_resolved_type(expr)
                        && qt.builtin() == Some(BuiltinType::Float)
                    {
                        return Some((fval as f32) as f64);
                    }
                    Some(fval)
                }
                LitVal::Int { value, .. } => Some(value as f64),
                LitVal::Char(value, _) => Some(value as f64),
                LitVal::True => Some(1.0),
                LitVal::False => Some(0.0),
                _ => None,
            },
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
            NodeKind::BuiltinChooseExpr(cond, true_expr, false_expr) => {
                if let Some(&selected) = self.semantic_info.choose_expressions.get(&expr.index()) {
                    return self.eval_float(selected);
                }
                if self.eval_int(*cond)? != 0 {
                    self.eval_float(*true_expr)
                } else {
                    self.eval_float(*false_expr)
                }
            }
            NodeKind::BuiltinComplex(real, _) => self.eval_float(*real),
            NodeKind::FunctionCall(call) => {
                let callee_kind = self.ast.get_kind(call.callee);
                let name_id = match callee_kind {
                    NodeKind::Ident(name_id, _) => name_id,
                    _ => return None,
                };

                let bn = builtin_names();
                if *name_id == bn.inff || *name_id == bn.huge_valf {
                    return Some(f32::INFINITY as f64);
                }
                if *name_id == bn.inf || *name_id == bn.huge_val {
                    return Some(f64::INFINITY);
                }
                if *name_id == bn.nanf {
                    return Some(f32::NAN as f64);
                }
                if *name_id == bn.nan {
                    return Some(f64::NAN);
                }
                if *name_id == bn.fabs || *name_id == bn.fabsf || *name_id == bn.fabsl {
                    let arg = call.arg_start;
                    let val = self.eval_float(arg);
                    return val.map(|v| v.abs());
                }
                if *name_id == bn.expect {
                    let arg = call.arg_start;
                    return self.eval_float(arg);
                }
                let is_int_builtin = *name_id == bn.popcount
                    || *name_id == bn.popcountl
                    || *name_id == bn.popcountll
                    || *name_id == bn.clz
                    || *name_id == bn.clzl
                    || *name_id == bn.clzll
                    || *name_id == bn.ctz
                    || *name_id == bn.ctzl
                    || *name_id == bn.ctzll
                    || *name_id == bn.ffs
                    || *name_id == bn.ffsl
                    || *name_id == bn.ffsll
                    || *name_id == bn.bswap16
                    || *name_id == bn.bswap32
                    || *name_id == bn.bswap64
                    || *name_id == bn.constant_p;
                if is_int_builtin {
                    return self.eval_int(expr).map(|v| v as f64);
                }
                None
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
            if !matches!(
                op_kind,
                NodeKind::Literal(_) | NodeKind::Cast(..) | NodeKind::FunctionCall(..)
            ) {
                return None;
            }
            if !f_val.is_finite() {
                return None;
            }

            let truncated = f_val.trunc();
            let width = self.registry.get(target_qt.ty()).width();
            let (min, max) = if target_qt.is_signed() {
                if width >= 64 {
                    (i64::MIN as f64, i64::MAX as f64)
                } else {
                    (-(1i64 << (width - 1)) as f64, (1i64 << (width - 1)) as f64)
                }
            } else {
                if width >= 64 {
                    (0.0, u64::MAX as f64)
                } else {
                    (0.0, (1u64 << width) as f64)
                }
            };

            if !(min..max).contains(&truncated) {
                return None;
            }
            return Some(self.truncate_to_type(truncated as i64, target_qt));
        }
        None
    }

    fn eval_sizeof(&self, expr: Option<NodeRef>, qt: Option<QualType>) -> Option<i64> {
        if let Some(e) = expr
            && let NodeKind::Literal(literal_ref) = self.ast.get_kind(e)
            && let LitVal::String { value, prefix } = literal_ref.get_val()
        {
            let builtin_type = get_string_builtin_type(prefix);
            let size = get_string_literal_size(&value, prefix);
            let elem_size = match builtin_type {
                BuiltinType::Char | BuiltinType::UChar => 1,
                BuiltinType::UShort => 2,
                BuiltinType::Int | BuiltinType::UInt => 4,
                _ => 1,
            };
            return Some((size * elem_size) as i64);
        }

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
            if let SymbolKind::Variable(v) = &symbol.kind
                && let Some(align) = v.alignment
            {
                return Some(align as i64);
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
    popcount: StringId,
    popcountl: StringId,
    popcountll: StringId,
    clz: StringId,
    clzl: StringId,
    clzll: StringId,
    ctz: StringId,
    ctzl: StringId,
    ctzll: StringId,
    ffs: StringId,
    ffsl: StringId,
    ffsll: StringId,
    bswap16: StringId,
    bswap32: StringId,
    bswap64: StringId,
    fabs: StringId,
    fabsf: StringId,
    fabsl: StringId,
    constant_p: StringId,
    expect: StringId,
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
        popcount: StringId::new("__builtin_popcount"),
        popcountl: StringId::new("__builtin_popcountl"),
        popcountll: StringId::new("__builtin_popcountll"),
        clz: StringId::new("__builtin_clz"),
        clzl: StringId::new("__builtin_clzl"),
        clzll: StringId::new("__builtin_clzll"),
        ctz: StringId::new("__builtin_ctz"),
        ctzl: StringId::new("__builtin_ctzl"),
        ctzll: StringId::new("__builtin_ctzll"),
        ffs: StringId::new("__builtin_ffs"),
        ffsl: StringId::new("__builtin_ffsl"),
        ffsll: StringId::new("__builtin_ffsll"),
        bswap16: StringId::new("__builtin_bswap16"),
        bswap32: StringId::new("__builtin_bswap32"),
        bswap64: StringId::new("__builtin_bswap64"),
        fabs: StringId::new("__builtin_fabs"),
        fabsf: StringId::new("__builtin_fabsf"),
        fabsl: StringId::new("__builtin_fabsl"),
        constant_p: StringId::new("__builtin_constant_p"),
        expect: StringId::new("__builtin_expect"),
    })
}
