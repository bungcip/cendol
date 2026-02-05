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

pub(crate) fn map_ast_binary_op_to_mir_int(ast_op: &BinaryOp) -> BinaryIntOp {
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

pub(crate) fn map_ast_binary_op_to_mir_float(ast_op: &BinaryOp) -> BinaryFloatOp {
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

pub(crate) fn map_ast_unary_op_to_mir_int(ast_op: &UnaryOp) -> UnaryIntOp {
    match ast_op {
        UnaryOp::Minus => UnaryIntOp::Neg,
        UnaryOp::BitNot => UnaryIntOp::BitwiseNot,
        UnaryOp::LogicNot => UnaryIntOp::LogicalNot,
        _ => panic!("Unsupported integer unary operator: {:?}", ast_op),
    }
}

pub(crate) fn map_ast_unary_op_to_mir_float(ast_op: &UnaryOp) -> UnaryFloatOp {
    match ast_op {
        UnaryOp::Minus => UnaryFloatOp::Neg,
        _ => panic!("Unsupported float unary operator: {:?}", ast_op),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinaryOp, UnaryOp};
    use crate::mir::{BinaryFloatOp, BinaryIntOp, Operand, Rvalue, UnaryFloatOp, UnaryIntOp};
    use std::num::NonZeroU32;

    #[test]
    fn test_mir_ops_mapping() {
        // Test map_ast_binary_op_to_mir_int
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Add), BinaryIntOp::Add);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Sub), BinaryIntOp::Sub);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Mul), BinaryIntOp::Mul);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Div), BinaryIntOp::Div);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Mod), BinaryIntOp::Mod);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::BitAnd), BinaryIntOp::BitAnd);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::BitOr), BinaryIntOp::BitOr);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::BitXor), BinaryIntOp::BitXor);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::LShift), BinaryIntOp::LShift);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::RShift), BinaryIntOp::RShift);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Equal), BinaryIntOp::Eq);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::NotEqual), BinaryIntOp::Ne);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Less), BinaryIntOp::Lt);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::LessEqual), BinaryIntOp::Le);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::Greater), BinaryIntOp::Gt);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::GreaterEqual), BinaryIntOp::Ge);

        // Test assignment stripping
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::AssignAdd), BinaryIntOp::Add);
        assert_eq!(map_ast_binary_op_to_mir_int(&BinaryOp::AssignSub), BinaryIntOp::Sub);

        // Test map_ast_binary_op_to_mir_float
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::Add), BinaryFloatOp::Add);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::Sub), BinaryFloatOp::Sub);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::Mul), BinaryFloatOp::Mul);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::Div), BinaryFloatOp::Div);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::Equal), BinaryFloatOp::Eq);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::NotEqual), BinaryFloatOp::Ne);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::Less), BinaryFloatOp::Lt);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::LessEqual), BinaryFloatOp::Le);
        assert_eq!(map_ast_binary_op_to_mir_float(&BinaryOp::Greater), BinaryFloatOp::Gt);
        assert_eq!(
            map_ast_binary_op_to_mir_float(&BinaryOp::GreaterEqual),
            BinaryFloatOp::Ge
        );

        // Test map_ast_unary_op_to_mir_int
        assert_eq!(map_ast_unary_op_to_mir_int(&UnaryOp::Minus), UnaryIntOp::Neg);
        assert_eq!(map_ast_unary_op_to_mir_int(&UnaryOp::BitNot), UnaryIntOp::BitwiseNot);
        assert_eq!(map_ast_unary_op_to_mir_int(&UnaryOp::LogicNot), UnaryIntOp::LogicalNot);

        // Test map_ast_unary_op_to_mir_float
        assert_eq!(map_ast_unary_op_to_mir_float(&UnaryOp::Minus), UnaryFloatOp::Neg);

        // Test emit_binary_rvalue
        let op1 = Operand::Constant(NonZeroU32::new(1).unwrap());
        let op2 = Operand::Constant(NonZeroU32::new(2).unwrap());

        // Integer emission
        match emit_binary_rvalue(&BinaryOp::Add, op1.clone(), op2.clone(), false) {
            Rvalue::BinaryIntOp(op, _, _) => assert_eq!(op, BinaryIntOp::Add),
            _ => panic!("Expected BinaryIntOp"),
        }

        // Float emission
        match emit_binary_rvalue(&BinaryOp::Add, op1.clone(), op2.clone(), true) {
            Rvalue::BinaryFloatOp(op, _, _) => assert_eq!(op, BinaryFloatOp::Add),
            _ => panic!("Expected BinaryFloatOp"),
        }

        // Unary emission
        match emit_unary_rvalue(&UnaryOp::Minus, op1.clone(), false) {
            Rvalue::UnaryIntOp(op, _) => assert_eq!(op, UnaryIntOp::Neg),
            _ => panic!("Expected UnaryIntOp"),
        }

        match emit_unary_rvalue(&UnaryOp::Minus, op1.clone(), true) {
            Rvalue::UnaryFloatOp(op, _) => assert_eq!(op, UnaryFloatOp::Neg),
            _ => panic!("Expected UnaryFloatOp"),
        }
    }
}
