//! Constant expression evaluation
//!
//! This module provides the functionality to evaluate constant expressions
//! at compile time, as required by the C11 standard for contexts like
//! static assertions and array sizes.

use crate::ast::{Ast, BinaryOp, NodeKind, NodeRef, UnaryOp, literal};
use crate::semantic::{QualType, SemanticInfo, SymbolKind, SymbolTable, TypeRegistry};

/// Context for constant expression evaluation
pub(crate) struct ConstEvalCtx<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: &'a SymbolTable,
    pub(crate) registry: &'a TypeRegistry,
    pub(crate) semantic_info: Option<&'a SemanticInfo>,
}

/// Evaluate a constant expression node to an i64 value
pub(crate) fn eval_const_expr(ctx: &ConstEvalCtx, expr_node_ref: NodeRef) -> Option<i64> {
    let node_kind = ctx.ast.get_kind(expr_node_ref);
    match node_kind {
        NodeKind::Literal(literal::Literal::Int { val, .. }) => Some(*val),
        NodeKind::Literal(literal::Literal::Char(val)) => Some(*val as i64),
        NodeKind::Ident(_, sym_ref) => {
            let symbol = ctx.symbol_table.get_symbol(*sym_ref);
            if let SymbolKind::EnumConstant(value) = &symbol.kind {
                Some(*value)
            } else {
                None
            }
        }
        NodeKind::BinaryOp(op, left_ref, right_ref) => {
            let left_val = eval_const_expr(ctx, *left_ref)?;

            // Short-circuiting logic
            match op {
                BinaryOp::LogicAnd => {
                    if left_val == 0 {
                        return Some(0);
                    }
                    let right_val = eval_const_expr(ctx, *right_ref)?;
                    return Some((right_val != 0) as i64);
                }
                BinaryOp::LogicOr => {
                    if left_val != 0 {
                        return Some(1);
                    }
                    let right_val = eval_const_expr(ctx, *right_ref)?;
                    return Some((right_val != 0) as i64);
                }
                _ => {}
            }

            let right_val = eval_const_expr(ctx, *right_ref)?;
            match op {
                BinaryOp::Add => Some(left_val.wrapping_add(right_val)),
                BinaryOp::Sub => Some(left_val.wrapping_sub(right_val)),
                BinaryOp::Mul => Some(left_val.wrapping_mul(right_val)),
                BinaryOp::Div => {
                    if right_val != 0 {
                        Some(left_val.wrapping_div(right_val))
                    } else {
                        None
                    }
                }
                BinaryOp::Equal => Some((left_val == right_val) as i64),
                BinaryOp::NotEqual => Some((left_val != right_val) as i64),
                BinaryOp::Less => Some((left_val < right_val) as i64),
                BinaryOp::LessEqual => Some((left_val <= right_val) as i64),
                BinaryOp::Greater => Some((left_val > right_val) as i64),
                BinaryOp::GreaterEqual => Some((left_val >= right_val) as i64),
                // LogicAnd/LogicOr handled above
                BinaryOp::BitOr => Some(left_val | right_val),
                BinaryOp::BitAnd => Some(left_val & right_val),
                BinaryOp::BitXor => Some(left_val ^ right_val),
                BinaryOp::LShift => {
                    // Safe shift, handle overflow or large shift count by wrapping or masking
                    Some(left_val.wrapping_shl(right_val as u32))
                }
                BinaryOp::RShift => Some(left_val.wrapping_shr(right_val as u32)),
                _ => None,
            }
        }
        NodeKind::UnaryOp(op, operand_ref) => {
            let operand_val = eval_const_expr(ctx, *operand_ref)?;
            match op {
                UnaryOp::LogicNot => Some((operand_val == 0) as i64),
                UnaryOp::Plus => Some(operand_val),
                UnaryOp::Minus => Some(operand_val.wrapping_neg()),
                UnaryOp::BitNot => Some(!operand_val),
                _ => None,
            }
        }
        NodeKind::SizeOfExpr(expr) => {
            let ty = ctx.ast.get_resolved_type(*expr).expect("Type not resolved");
            let layout = ctx.registry.get_layout(ty.ty());
            Some(layout.size as i64)
        }
        NodeKind::AlignOf(ty) => {
            let layout = ctx.registry.get_layout(ty.ty());
            Some(layout.alignment as i64)
        }
        NodeKind::SizeOfType(ty) => {
            let layout = ctx.registry.get_layout(ty.ty());
            Some(layout.size as i64)
        }
        NodeKind::GenericSelection(_) => {
            let info = ctx.semantic_info.or(ctx.ast.semantic_info.as_ref());
            if let Some(info) = info
                && let Some(selected_expr) = info.generic_selections.get(&expr_node_ref.index())
            {
                return eval_const_expr(ctx, *selected_expr);
            }
            None
        }
        NodeKind::TernaryOp(cond, then_ref, else_ref) => {
            let cond_val = eval_const_expr(ctx, *cond)?;
            if cond_val != 0 {
                eval_const_expr(ctx, *then_ref)
            } else {
                eval_const_expr(ctx, *else_ref)
            }
        }
        NodeKind::Cast(_, expr) => eval_const_expr(ctx, *expr),
        NodeKind::BuiltinOffsetof(ty, expr) => eval_offsetof(ctx, *ty, *expr),
        _ => None,
    }
}

pub(crate) fn eval_offsetof(ctx: &ConstEvalCtx, ty: QualType, expr_ref: NodeRef) -> Option<i64> {
    let mut current_ty = ty;
    let mut offset = 0i64;

    fn walk(ctx: &ConstEvalCtx, node_ref: NodeRef, current_ty: &mut QualType, offset: &mut i64) -> bool {
        match *ctx.ast.get_kind(node_ref) {
            NodeKind::Dummy => true,
            NodeKind::MemberAccess(base, member_name, is_arrow) => {
                if !walk(ctx, base, current_ty, offset) {
                    return false;
                }

                let record_ty = if is_arrow {
                    ctx.registry.get_pointee(current_ty.ty()).map(|qt| qt.ty())
                } else {
                    Some(current_ty.ty())
                };

                let Some(record_ty) = record_ty else {
                    return false;
                };
                if !record_ty.is_record() {
                    return false;
                }

                let mut flat_members = Vec::new();
                let mut flat_offsets = Vec::new();
                let ty_obj = ctx.registry.get(record_ty);
                ty_obj.flatten_members_with_layouts(ctx.registry, &mut flat_members, &mut flat_offsets, 0);

                if let Some(idx) = flat_members.iter().position(|m| m.name == Some(member_name)) {
                    *offset += flat_offsets[idx] as i64;
                    *current_ty = flat_members[idx].member_type;
                    true
                } else {
                    false
                }
            }
            NodeKind::IndexAccess(base, index) => {
                if !walk(ctx, base, current_ty, offset) {
                    return false;
                }

                let Some(elem_ty) = ctx.registry.get_array_element(current_ty.ty()) else {
                    return false;
                };
                let Some(index_val) = eval_const_expr(ctx, index) else {
                    return false;
                };

                let layout = ctx.registry.get_layout(elem_ty);
                *offset += index_val * (layout.size as i64);
                *current_ty = QualType::unqualified(elem_ty);
                true
            }
            _ => false,
        }
    }

    if walk(ctx, expr_ref, &mut current_ty, &mut offset) {
        Some(offset)
    } else {
        None
    }
}
