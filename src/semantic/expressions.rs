use crate::parser::ast::{BinOp, TypedExpr};
use crate::types::TypeId;

pub(crate) struct TypedExpression {
    op: BinOp,
    lhs: TypedExpr,
    rhs: TypedExpr,
    ty: TypeId,
}

impl TypedExpression {
    pub(crate) fn new(op: BinOp, lhs: TypedExpr, rhs: TypedExpr, ty: TypeId) -> Self {
        Self { op, lhs, rhs, ty }
    }
}

impl From<TypedExpression> for TypedExpr {
    fn from(expr: TypedExpression) -> Self {
        let span = expr.lhs.span(); // Use lhs span as the span for the binary operation
        let lhs = Box::new(expr.lhs);
        let rhs = Box::new(expr.rhs);
        let ty = expr.ty;

        match expr.op {
            BinOp::Add => TypedExpr::Add(lhs, rhs, span, ty),
            BinOp::Sub => TypedExpr::Sub(lhs, rhs, span, ty),
            BinOp::Mul => TypedExpr::Mul(lhs, rhs, span, ty),
            BinOp::Div => TypedExpr::Div(lhs, rhs, span, ty),
            BinOp::Mod => TypedExpr::Mod(lhs, rhs, span, ty),
            BinOp::Equal => TypedExpr::Equal(lhs, rhs, span, ty),
            BinOp::NotEqual => TypedExpr::NotEqual(lhs, rhs, span, ty),
            BinOp::LessThan => TypedExpr::LessThan(lhs, rhs, span, ty),
            BinOp::GreaterThan => TypedExpr::GreaterThan(lhs, rhs, span, ty),
            BinOp::LessThanOrEqual => TypedExpr::LessThanOrEqual(lhs, rhs, span, ty),
            BinOp::GreaterThanOrEqual => TypedExpr::GreaterThanOrEqual(lhs, rhs, span, ty),
            BinOp::LogicalAnd => TypedExpr::LogicalAnd(lhs, rhs, span, ty),
            BinOp::LogicalOr => TypedExpr::LogicalOr(lhs, rhs, span, ty),
            BinOp::BitwiseOr => TypedExpr::BitwiseOr(lhs, rhs, span, ty),
            BinOp::BitwiseXor => TypedExpr::BitwiseXor(lhs, rhs, span, ty),
            BinOp::BitwiseAnd => TypedExpr::BitwiseAnd(lhs, rhs, span, ty),
            BinOp::LeftShift => TypedExpr::LeftShift(lhs, rhs, span, ty),
            BinOp::RightShift => TypedExpr::RightShift(lhs, rhs, span, ty),
            BinOp::Comma => TypedExpr::Comma(lhs, rhs, span, ty),
        }
    }
}
