use std::fs;

fn main() {
    let mut content = fs::read_to_string("src/semantic/const_eval.rs").unwrap();

    let to_insert1 = r#"            let is_cmp_or_logic = matches!(op, BinaryOp::Equal | BinaryOp::NotEqual | BinaryOp::Less | BinaryOp::LessEqual | BinaryOp::Greater | BinaryOp::GreaterEqual | BinaryOp::LogicAnd | BinaryOp::LogicOr);

            if is_cmp_or_logic {
                let is_float_op = ctx.get_resolved_type(*left).map_or(false, |ty| ty.is_floating_point()) ||
                                  ctx.get_resolved_type(*right).map_or(false, |ty| ty.is_floating_point());
                if is_float_op {
                    if let (Some(left_f), Some(right_f)) = (eval_const_expr_float(ctx, *left), eval_const_expr_float(ctx, *right)) {
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
            }

"#;

    let target1 = "            let left_val = eval_const_expr(ctx, *left)?;\n\n            // Short-circuiting logic";

    content = content.replace(target1, &format!("{}{}", to_insert1, target1));

    let to_insert2 = r#"
pub(crate) fn eval_const_expr_float(ctx: &ConstEvalCtx, expr_node: NodeRef) -> Option<f64> {
    let node_kind = ctx.ast.get_kind(expr_node);
    match node_kind {
        NodeKind::Literal(literal::Literal::Float { val, .. }) => Some(*val),
        NodeKind::Literal(literal::Literal::Int { val, .. }) => Some(*val as f64),
        NodeKind::Literal(literal::Literal::Char(val)) => Some(*val as f64),
        NodeKind::BinaryOp(op, left, right) => {
            let left_val = eval_const_expr_float(ctx, *left)?;
            let right_val = eval_const_expr_float(ctx, *right)?;
            match op {
                BinaryOp::Add => Some(left_val + right_val),
                BinaryOp::Sub => Some(left_val - right_val),
                BinaryOp::Mul => Some(left_val * right_val),
                BinaryOp::Div => Some(left_val / right_val),
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
"#;

    let target2 = "fn eval_offsetof(ctx: &ConstEvalCtx, qt: QualType, expr: NodeRef) -> Option<i64> {";
    content = content.replace(target2, &format!("{}{}", to_insert2, target2));

    fs::write("src/semantic/const_eval.rs", content).unwrap();
}
