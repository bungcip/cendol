use std::fs;

fn main() {
    let mut content = fs::read_to_string("src/semantic/const_eval.rs").unwrap();
    content = content.replace("is_floating_point()", "is_float()");
    fs::write("src/semantic/const_eval.rs", content).unwrap();
}
