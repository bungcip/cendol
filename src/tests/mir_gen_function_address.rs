use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_function_pointer_address_of() {
    let source = r#"
typedef void (*Pfunc)(void);

void runner(Pfunc f) {
    f();
}

void my_func(void) {}

int main() {
    runner(my_func);
    runner(&my_func);
    return 0;
}
"#;
    run_pass(source, CompilePhase::Cranelift);
}
