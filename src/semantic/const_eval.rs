//! Constant expression evaluation
//!
//! This module provides the functionality to evaluate constant expressions
//! at compile time, as required by the C11 standard for contexts like
//! static assertions and array sizes.

use crate::ast::{Ast, BinaryOp, NodeKind, NodeRef, UnaryOp};

/// Context for constant expression evaluation
pub struct ConstEvalCtx<'a> {
    pub ast: &'a Ast,
    // Add other necessary context here, like symbol table access
}

/// Evaluate a constant expression node to an i64 value
pub fn eval_const_expr(ctx: &ConstEvalCtx, expr_node_ref: NodeRef) -> Option<i64> {
    let node = ctx.ast.get_node(expr_node_ref);
    match &node.kind {
        NodeKind::LiteralInt(val) => Some(*val),
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
                _ => None,
            }
        }
        _ => None,
    }
}
