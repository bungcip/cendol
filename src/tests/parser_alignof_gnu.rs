use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_alignof_gnu_struct() {
    run_pass(
        r#"
        int main() {
            return __alignof__(struct { int a; });
        }
        "#,
        CompilePhase::Parse,
    );
}

#[test]
fn test_alignas_gnu_int() {
    run_pass(
        r#"
        __alignas__(16) int x;
        __alignas(double) int y;
        int main() { return 0; }
        "#,
        CompilePhase::Parse,
    );
}

#[test]
fn test_alignof_macro_expansion() {
    run_pass(
        r#"
        #define alignof(x) __alignof__(x)
        int main() {
            return alignof(struct { int a; });
        }
        "#,
        CompilePhase::Parse,
    );
}
