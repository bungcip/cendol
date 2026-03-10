use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_offsetof_bitfield_prohibited() {
    // C11 7.19p3: "The member-designator shall be such that given:
    // static type t; the expression &(t.member-designator) is a constant expression."
    // 6.5.3.2p1: "The operand of the unary & operator shall be... an lvalue that
    // designates an object that is not a bit-field..."
    // Therefore, offsetof cannot be applied to a bit-field.

    run_fail_with_message(
        r#"
        struct S {
            int x : 1;
        };
        int x = __builtin_offsetof(struct S, x);
        "#,
        "cannot apply 'offsetof' to a bit-field",
    );
}

#[test]
fn test_offsetof_incomplete_type_prohibited() {
    // C11 7.19p3: "The type name shall be such that given:
    // static type t; the expression &(t.member-designator) is a constant expression."
    // If 'type' is incomplete, 't.member-designator' is invalid because the layout
    // of an incomplete type is unknown.

    run_fail_with_message(
        r#"
        struct S;
        int x = __builtin_offsetof(struct S, a);
        "#,
        "cannot apply 'offsetof' to an incomplete type 'struct S'",
    );
}

#[test]
fn test_offsetof_anonymous_bitfield_prohibited() {
    // Ensure bit-fields inside anonymous structs/unions are also rejected.
    run_fail_with_message(
        r#"
        struct S {
            struct {
                int x : 1;
            };
        };
        int x = __builtin_offsetof(struct S, x);
        "#,
        "cannot apply 'offsetof' to a bit-field",
    );
}

#[test]
fn test_offsetof_nested_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        struct Inner { int x : 1; };
        struct Outer { struct Inner i; };
        int x = __builtin_offsetof(struct Outer, i.x);
        "#,
        "cannot apply 'offsetof' to a bit-field",
    );
}
