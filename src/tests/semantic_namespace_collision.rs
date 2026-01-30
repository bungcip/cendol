use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_pass;

#[test]
fn allows_typedef_and_struct_tag_with_same_name() {
    run_pass(
        r#"
typedef int T;
struct T { int i; };
int main() {
    struct T var;
    var.i = 0;
    T other_var = 1;
    return 0;
}
        "#,
        CompilePhase::Mir,
    );
}
