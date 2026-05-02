use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_generic_selection_distinguishes_different_enums() {
    // C11 6.2.7p1: "Two types have compatible type if they are the same."
    // Two different enum types are NOT the same and thus NOT compatible,
    // even if they have the same underlying integer type.
    run_pass(
        r#"
        enum E1 { A };
        enum E2 { B };
        int main() {
            enum E1 e = A;
            return _Generic(e, enum E1: 0, enum E2: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}
