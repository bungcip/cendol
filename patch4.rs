use std::fs;

fn main() {
    let mut content = fs::read_to_string("src/semantic/const_eval.rs").unwrap();
    content = content.replace("ctx.registry.get(ty.ty()).is_floating()", "ty.ty().is_floating()");
    fs::write("src/semantic/const_eval.rs", content).unwrap();
}
