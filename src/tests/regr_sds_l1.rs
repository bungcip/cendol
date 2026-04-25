use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_regr_sds_l1() {
    let source = r#"
typedef unsigned long size_t;
int main() {
    size_t l1 = 1;
    size_t l2 = 2;
    return l1 > l2;
}
"#;
    run_pass(source, CompilePhase::Mir);
}
