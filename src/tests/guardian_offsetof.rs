use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_offsetof_incomplete_struct() {
    let source = r#"
        struct S;
        void test() {
            __builtin_offsetof(struct S, a);
        }
    "#;
    run_fail_with_message(source, "offsetof of incomplete type 'struct S'");
}

#[test]
fn test_offsetof_incomplete_union() {
    let source = r#"
        union U;
        void test() {
            __builtin_offsetof(union U, a);
        }
    "#;
    run_fail_with_message(source, "offsetof of incomplete type 'union U'");
}

#[test]
fn test_offsetof_bitfield() {
    let source = r#"
        struct S {
            int a : 4;
            int b : 4;
        };
        void test() {
            __builtin_offsetof(struct S, a);
        }
    "#;
    run_fail_with_message(source, "cannot apply 'offsetof' to a bit-field");
}

#[test]
fn test_offsetof_nested_bitfield() {
    let source = r#"
        struct Outer {
            struct {
                int a : 4;
            } inner;
        };
        void test() {
            __builtin_offsetof(struct Outer, inner.a);
        }
    "#;
    run_fail_with_message(source, "cannot apply 'offsetof' to a bit-field");
}

#[test]
fn test_offsetof_anonymous_bitfield() {
    let source = r#"
        struct S {
            int a : 4;
            struct {
                int b : 4;
            };
        };
        void test() {
            __builtin_offsetof(struct S, b);
        }
    "#;
    run_fail_with_message(source, "cannot apply 'offsetof' to a bit-field");
}
