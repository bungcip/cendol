use crate::tests::test_utils::{run_fail_with_message, run_pass};
use crate::driver::artifact::CompilePhase;

#[test]
fn test_alignas_redeclaration_constraints() {
    // C11 6.7.5p5: "If any declaration of an identifier has an alignment specifier,
    // then the first declaration shall specify an alignment at least as strict as
    // that specified by any subsequent declaration of that identifier."
    //
    // And "if any declaration of an identifier has an alignment specifier,
    // every other declaration of that identifier shall either specify no
    // alignment or specify an alignment that is the same as the first one."

    // 1. First declaration must specify alignment if any subsequent one does.
    run_fail_with_message(
        r#"
        int x;
        _Alignas(8) int x;
        "#,
        "first declaration of 'x' does not specify an alignment",
    );

    // 2. Mismatched alignment in subsequent declaration.
    run_fail_with_message(
        r#"
        _Alignas(8) int x;
        _Alignas(16) int x;
        "#,
        "alignment of 'x' (16) does not match the first declaration (8)",
    );

    // 3. Subsequent declaration can omit alignment.
    run_pass(
        r#"
        _Alignas(8) int x;
        int x;
        int main() {
            _Static_assert(_Alignof(x) == 8, "Alignment should be inherited");
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );

    // 4. Same alignment in subsequent declaration is OK.
    run_pass(
        r#"
        _Alignas(8) int x;
        _Alignas(8) int x;
        int main() {
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
