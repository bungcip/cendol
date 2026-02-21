use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_large_array_zero_init() {
    let source = "
        int bigarray[2147483647];
        int main() { return 0; }
    ";
    run_pass(source, CompilePhase::EmitObject);
}
