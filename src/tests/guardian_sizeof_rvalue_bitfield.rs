use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_sizeof_rvalue_bitfield_allowed() {
    // C11 6.5.3.4p1: "The sizeof operator shall not be applied to... an expression that designates a bit-field member."
    // An rvalue (like from a comma operator or statement expression) that was derived from a bit-field no longer "designates" a bit-field member.
    run_pass(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return sizeof(0, s.x);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_alignof_rvalue_bitfield_allowed() {
    // Similarly for _Alignof on expressions (GCC/Clang extension).
    run_pass(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return _Alignof(0, s.x);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_sizeof_lvalue_bitfield_rejected() {
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return sizeof(s.x);
        }
        "#,
        "cannot apply 'sizeof' to a bit-field",
    );
}

#[test]
fn test_alignof_lvalue_bitfield_rejected() {
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return _Alignof(s.x);
        }
        "#,
        "cannot apply '_Alignof' to a bit-field",
    );
}
