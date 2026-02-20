use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_selection_accepts_void_controlling_expression() {
    // C11 6.5.1.1p2: "The controlling expression shall be an expression of a complete object type, or the void type."
    // Currently this fails in Cendol, but it should pass.
    run_pass(
        r#"
        void foo(void);
        int main() {
            return _Generic(foo(), default: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_rejects_function_type_association() {
    // C11 6.5.1.1p2: "The type name in a generic association shall specify a complete object type..."
    // A function type is not an object type.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, void(int): 1, default: 2);
        }
        "#,
        "generic association specifies function type",
    );
}

#[test]
fn test_generic_selection_rejects_vla_association() {
    // C11 6.5.1.1p2: "The type name in a generic association shall specify a complete object type other than a variably modified type."
    run_fail_with_message(
        r#"
        void f(int n) {
            _Generic(0, int[n]: 1, default: 2);
        }
        "#,
        "variably modified type",
    );
}
