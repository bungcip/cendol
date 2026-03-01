use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_typedef_visible_in_declarator() {
    let source = r#"
typedef int T, T1(T); // T is visible when declaring T1.
void f(void) {
    int (*T)(T x) = 0;
    int T1 = sizeof((int)T1);
}
"#;
    run_pass(source, CompilePhase::SemanticLowering);
}
