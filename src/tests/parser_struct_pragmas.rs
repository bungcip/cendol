use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_struct_with_pragmas() {
    run_pass(
        r#"
        struct S {
            #pragma pack(1)
            int a;
            #pragma GCC visibility push(default)
            char b;
        };
        int main() { return 0; }
        "#,
        CompilePhase::Parse,
    );
}
