//! Constant expression evaluation
//!
//! This module provides the functionality to evaluate constant expressions
//! at compile time, as required by the C11 standard for contexts like
//! static assertions and array sizes.

use crate::ast::{Ast, BinaryOp, NodeKind, NodeRef, UnaryOp, literal};
use crate::semantic::{SemanticInfo, SymbolKind, SymbolTable, TypeRegistry};

/// Context for constant expression evaluation
pub(crate) struct ConstEvalCtx<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: &'a SymbolTable,
    pub(crate) type_registry: &'a TypeRegistry,
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
            if let SymbolKind::EnumConstant { value } = &symbol.kind {
                Some(*value)
            } else {
                None
            }
        }
        NodeKind::BinaryOp(op, left_ref, right_ref) => {
            let left_val = eval_const_expr(ctx, *left_ref)?;
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
                BinaryOp::LogicAnd => Some(((left_val != 0) && (right_val != 0)) as i64),
                BinaryOp::LogicOr => Some(((left_val != 0) || (right_val != 0)) as i64),
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
            let ty = ctx
                .semantic_info
                .and_then(|si| si.types[expr.index()])
                .or_else(|| ctx.ast.get_resolved_type(*expr))
                .unwrap();
            let layout = ctx.type_registry.get_layout(ty.ty());
            Some(layout.size as i64)
        }
        NodeKind::SizeOfType(ty) => {
            let layout = ctx.type_registry.get_layout(ty.ty());
            Some(layout.size as i64)
        }
        NodeKind::AlignOf(ty) => {
            let layout = ctx.type_registry.get_layout(ty.ty());
            Some(layout.alignment as i64)
        }
        _ => None,
    }
}
