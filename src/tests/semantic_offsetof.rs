use crate::tests::test_utils::{run_fail_with_message};

#[test]
fn test_offsetof_member_on_non_record_base() {
    let source = r#"
        struct S {
            int a;
        };
        void test() {
            __builtin_offsetof(struct S, a.b);
        }
    "#;
    // Error: "member reference base type 'int' is not a structure or union"
    run_fail_with_message(
        source,
        "member reference base type 'int' is not a structure or union",
    );
}

#[test]
fn test_offsetof_member_not_found() {
    let source = r#"
        struct S {
            int a;
        };
        void test() {
            __builtin_offsetof(struct S, b);
        }
    "#;
    // Error: "no member named 'b' in 'struct S'"
    run_fail_with_message(source, "no member named 'b' in 'struct S'");
}

#[test]
fn test_offsetof_expected_array() {
    let source = r#"
        struct S {
            int a;
        };
        void test() {
            __builtin_offsetof(struct S, a[0]);
        }
    "#;
    // Error: "subscripted value is not an array (have 'int')"
    run_fail_with_message(source, "subscripted value is not an array (have 'int')");
}

#[test]
fn test_offsetof_non_constant_index() {
    let source = r#"
        struct S {
            int a[10];
        };
        int var;
        void test() {
            __builtin_offsetof(struct S, a[var]);
        }
    "#;
    // Error: "Initializer element is not a compile-time constant"
    run_fail_with_message(source, "Initializer element is not a compile-time constant");
}

#[test]
fn test_offsetof_member_on_pointer_with_dot() {
    let source = r#"
        struct S {
            int *p;
        };
        void test() {
            __builtin_offsetof(struct S, p.x);
        }
    "#;
    // Error: "member reference base type 'int*' is not a structure or union"
    run_fail_with_message(
        source,
        "member reference base type 'int*' is not a structure or union",
    );
}
