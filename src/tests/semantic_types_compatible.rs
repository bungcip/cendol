use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_types_compatible_unresolved_typeof() {
    run_pass(
        "
        int main() {
            int a = 1;
            int x = __builtin_types_compatible_p(typeof(({ a; })), typeof(1));
            return x;
        }
        ",
        CompilePhase::Mir,
    );
}
