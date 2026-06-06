use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_typeof_ternary_with_decay_and_void() {
    run_pass(
        r#"
        static void f(void) {}
        void (*fp)(void) = f;
        int main() {
            _Generic((__typeof(1?f:f)*){0}, void (**)(void): (void)0);
            _Generic((__typeof(fp?0L:(void)0)*){0}, void*: (void)0);
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}
