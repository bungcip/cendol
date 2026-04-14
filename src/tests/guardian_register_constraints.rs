use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_register_struct_member_address_prohibited() {
    // C11 6.7.1p6: "If an object... is declared with the register storage-class specifier...
    // any part of the object... shall not have its address taken"
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            register struct S s;
            int *p = &s.x;
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_register_union_member_address_prohibited() {
    run_fail_with_message(
        r#"
        union U { int x; float y; };
        int main() {
            register union U u;
            int *p = &u.x;
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_register_array_decay_prohibited() {
    // Implicit decay of a register array is effectively taking the address of its first element.
    run_fail_with_message(
        r#"
        int main() {
            register int a[10];
            int *p = a;
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_register_array_index_address_prohibited() {
    run_fail_with_message(
        r#"
        int main() {
            register int a[10];
            int *p = &a[0];
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_register_nested_member_address_prohibited() {
    run_fail_with_message(
        r#"
        struct Inner { int x; };
        struct Outer { struct Inner inner; };
        int main() {
            register struct Outer o;
            int *p = &o.inner.x;
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_register_selection_expression_member_address_prohibited() {
    // _Generic
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            register struct S s;
            int *p = &_Generic(0, int: s.x);
        }
        "#,
        "cannot take address of 'register' variable",
    );

    // __builtin_choose_expr
    run_fail_with_message(
        r#"
        struct S { int x; };
        int main() {
            register struct S s;
            int *p = &__builtin_choose_expr(1, s.x, s.x);
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_register_selection_expression_array_decay_prohibited() {
    run_fail_with_message(
        r#"
        int main() {
            register int a[10];
            int *p = _Generic(0, int: a);
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_non_register_aggregate_address_allowed() {
    run_pass(
        r#"
        struct S { int x; };
        int main() {
            struct S s;
            int *p = &s.x;
            int a[10];
            int *pa = a;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
