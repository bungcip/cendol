use std::fs;

fn main() {
    let mut content = fs::read_to_string("src/semantic/const_eval.rs").unwrap();
    content = content.replace(
        "            let left_val = eval_const_expr(ctx, *left)?;\n\n            // Short-circuiting logic",
        r#"
            // If the operator is logic and/or, try fallback to float evaluation if it doesn't evaluate as an integer
            let left_val = match eval_const_expr(ctx, *left) {
                Some(v) => v,
                None => {
                    if matches!(op, BinaryOp::LogicAnd | BinaryOp::LogicOr) {
                        let is_float_op = ctx.get_resolved_type(*left).map_or(false, |ty| ty.ty().is_floating()) ||
                                          ctx.get_resolved_type(*right).map_or(false, |ty| ty.ty().is_floating());
                        if is_float_op {
                            if op == BinaryOp::LogicAnd {
                                if let Some(left_f) = eval_const_expr_float(ctx, *left) {
                                    if left_f == 0.0 {
                                        return Some(0);
                                    }
                                    if let Some(right_f) = eval_const_expr_float(ctx, *right) {
                                        return Some((right_f != 0.0) as i64);
                                    }
                                }
                            } else {
                                if let Some(left_f) = eval_const_expr_float(ctx, *left) {
                                    if left_f != 0.0 {
                                        return Some(1);
                                    }
                                    if let Some(right_f) = eval_const_expr_float(ctx, *right) {
                                        return Some((right_f != 0.0) as i64);
                                    }
                                }
                            }
                        }
                    }
                    return None;
                }
            };

            // Short-circuiting logic"#
    );
    fs::write("src/semantic/const_eval.rs", content).unwrap();
}
