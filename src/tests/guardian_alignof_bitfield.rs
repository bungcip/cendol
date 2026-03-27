use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn test_alignof_bitfield_prohibited() {
    // While _Alignof(expression) is a GCC/Clang extension, it should still
    // prohibit bit-fields because they don't have a byte-aligned address.
    run_fail_with_diagnostic(
        r#"
        struct S {
            int x : 1;
        };
        int main() {
            struct S s;
            return _Alignof(s.x);
        }
        "#,
        CompilePhase::Mir,
        "cannot apply '_Alignof' to a bit-field",
        7,
        20,
    );
}
