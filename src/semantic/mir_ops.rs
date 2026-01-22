use crate::ast::{BinaryOp, UnaryOp};
use crate::mir::{BinaryFloatOp, BinaryIntOp, Operand, Rvalue, UnaryFloatOp, UnaryIntOp};

pub(crate) fn emit_binary_rvalue(op: &BinaryOp, lhs: Operand, rhs: Operand, is_float: bool) -> Rvalue {
    if is_float {
        let mir_op = map_ast_binary_op_to_mir_float(op);
        Rvalue::BinaryFloatOp(mir_op, lhs, rhs)
    } else {
        let mir_op = map_ast_binary_op_to_mir_int(op);
        Rvalue::BinaryIntOp(mir_op, lhs, rhs)
    }
}

pub(crate) fn emit_unary_rvalue(op: &UnaryOp, operand: Operand, is_float: bool) -> Rvalue {
    if is_float {
        let mir_op = map_ast_unary_op_to_mir_float(op);
        Rvalue::UnaryFloatOp(mir_op, operand)
    } else {
        let mir_op = map_ast_unary_op_to_mir_int(op);
        Rvalue::UnaryIntOp(mir_op, operand)
    }
}

pub fn map_ast_binary_op_to_mir_int(ast_op: &BinaryOp) -> BinaryIntOp {
    let op = ast_op.without_assignment().unwrap_or(*ast_op);
    match op {
        BinaryOp::Add => BinaryIntOp::Add,
        BinaryOp::Sub => BinaryIntOp::Sub,
        BinaryOp::Mul => BinaryIntOp::Mul,
        BinaryOp::Div => BinaryIntOp::Div,
        BinaryOp::Mod => BinaryIntOp::Mod,
        BinaryOp::BitAnd => BinaryIntOp::BitAnd,
        BinaryOp::BitOr => BinaryIntOp::BitOr,
        BinaryOp::BitXor => BinaryIntOp::BitXor,
        BinaryOp::LShift => BinaryIntOp::LShift,
        BinaryOp::RShift => BinaryIntOp::RShift,
        BinaryOp::Equal => BinaryIntOp::Eq,
        BinaryOp::NotEqual => BinaryIntOp::Ne,
        BinaryOp::Less => BinaryIntOp::Lt,
        BinaryOp::LessEqual => BinaryIntOp::Le,
        BinaryOp::Greater => BinaryIntOp::Gt,
        BinaryOp::GreaterEqual => BinaryIntOp::Ge,
        // Logic ops are handled separately (short-circuit)
        BinaryOp::LogicAnd | BinaryOp::LogicOr => panic!("Logic ops should be handled separately"),
        BinaryOp::Comma => panic!("Comma op should be handled separately"), // Comma usually handled in expression lowering
        _ => panic!("Unsupported integer binary operator: {:?}", ast_op),
    }
}

pub fn map_ast_binary_op_to_mir_float(ast_op: &BinaryOp) -> BinaryFloatOp {
    let op = ast_op.without_assignment().unwrap_or(*ast_op);
    match op {
        BinaryOp::Add => BinaryFloatOp::Add,
        BinaryOp::Sub => BinaryFloatOp::Sub,
        BinaryOp::Mul => BinaryFloatOp::Mul,
        BinaryOp::Div => BinaryFloatOp::Div,
        BinaryOp::Equal => BinaryFloatOp::Eq,
        BinaryOp::NotEqual => BinaryFloatOp::Ne,
        BinaryOp::Less => BinaryFloatOp::Lt,
        BinaryOp::LessEqual => BinaryFloatOp::Le,
        BinaryOp::Greater => BinaryFloatOp::Gt,
        BinaryOp::GreaterEqual => BinaryFloatOp::Ge,
        _ => panic!("Unsupported float binary operator: {:?}", ast_op),
    }
}

pub fn map_ast_unary_op_to_mir_int(ast_op: &UnaryOp) -> UnaryIntOp {
    match ast_op {
        UnaryOp::Minus => UnaryIntOp::Neg,
        UnaryOp::BitNot => UnaryIntOp::BitwiseNot,
        UnaryOp::LogicNot => UnaryIntOp::LogicalNot,
        _ => panic!("Unsupported integer unary operator: {:?}", ast_op),
    }
}

pub fn map_ast_unary_op_to_mir_float(ast_op: &UnaryOp) -> UnaryFloatOp {
    match ast_op {
        UnaryOp::Minus => UnaryFloatOp::Neg,
        _ => panic!("Unsupported float unary operator: {:?}", ast_op),
    }
}
