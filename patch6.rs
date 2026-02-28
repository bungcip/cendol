use std::fs;

fn main() {
    let mut content = fs::read_to_string("src/semantic/const_eval.rs").unwrap();
    content = content.replace("if op == BinaryOp::LogicAnd", "if *op == BinaryOp::LogicAnd");
    fs::write("src/semantic/const_eval.rs", content).unwrap();
}
