use crate::parser::ast::{BinOp, Type, TypedExpr};

pub(crate) struct TypedExpression {
    op: BinOp,
    lhs: TypedExpr,
    rhs: TypedExpr,
    ty: Type,
}

impl TypedExpression {
    pub(crate) fn new(op: BinOp, lhs: TypedExpr, rhs: TypedExpr, ty: Type) -> Self {
        Self { op, lhs, rhs, ty }
    }
}

impl From<TypedExpression> for TypedExpr {
    fn from(expr: TypedExpression) -> Self {
        let lhs = Box::new(expr.lhs);
        let rhs = Box::new(expr.rhs);
        let ty = expr.ty;

        match expr.op {
            BinOp::Add => TypedExpr::Add(lhs, rhs, ty),
            BinOp::Sub => TypedExpr::Sub(lhs, rhs, ty),
            BinOp::Mul => TypedExpr::Mul(lhs, rhs, ty),
            BinOp::Div => TypedExpr::Div(lhs, rhs, ty),
            BinOp::Mod => TypedExpr::Mod(lhs, rhs, ty),
            BinOp::Equal => TypedExpr::Equal(lhs, rhs, ty),
            BinOp::NotEqual => TypedExpr::NotEqual(lhs, rhs, ty),
            BinOp::LessThan => TypedExpr::LessThan(lhs, rhs, ty),
            BinOp::GreaterThan => TypedExpr::GreaterThan(lhs, rhs, ty),
            BinOp::LessThanOrEqual => TypedExpr::LessThanOrEqual(lhs, rhs, ty),
            BinOp::GreaterThanOrEqual => TypedExpr::GreaterThanOrEqual(lhs, rhs, ty),
            BinOp::LogicalAnd => TypedExpr::LogicalAnd(lhs, rhs, ty),
            BinOp::LogicalOr => TypedExpr::LogicalOr(lhs, rhs, ty),
            BinOp::BitwiseOr => TypedExpr::BitwiseOr(lhs, rhs, ty),
            BinOp::BitwiseXor => TypedExpr::BitwiseXor(lhs, rhs, ty),
            BinOp::BitwiseAnd => TypedExpr::BitwiseAnd(lhs, rhs, ty),
            BinOp::LeftShift => TypedExpr::LeftShift(lhs, rhs, ty),
            BinOp::RightShift => TypedExpr::RightShift(lhs, rhs, ty),
            BinOp::Comma => TypedExpr::Comma(lhs, rhs, ty),
        }
    }
}
