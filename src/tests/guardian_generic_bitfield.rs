use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_selection_bitfield_constraints() {
    // C11 6.5.3.4p1: "The sizeof operator shall not be applied to... a bit-field member."
    // C11 6.5.3.2p1: "The operand of the unary & operator shall be... an lvalue that designates an object that is not a bit-field..."
    // Even when wrapped in _Generic, these constraints must be enforced on the selected expression.

    // 1. sizeof(bit-field) via _Generic
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return sizeof(_Generic(0, int: s.x));
        }
        "#,
        "cannot apply 'sizeof' to a bit-field",
    );

    // 2. &(bit-field) via _Generic
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            void *p = &_Generic(0, int: s.x);
        }
        "#,
        "cannot take address of bit-field",
    );
}

#[test]
fn test_generic_selection_register_constraints() {
    // C11 6.5.3.2p1: "The operand of the unary & operator shall be... an lvalue that designates an object... not declared with the register storage-class specifier."

    run_fail_with_message(
        r#"
        int main() {
            register int x = 0;
            void *p = &_Generic(0, int: x);
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_generic_selection_lvalue_preservation() {
    // Verify that _Generic preserves lvalue-ness for assignments.
    run_pass(
        r#"
        int main() {
            int x = 0;
            _Generic(0, int: x) = 10;
            return x == 10 ? 0 : 1;
        }
        "#,
        CompilePhase::Mir,
    );
}
