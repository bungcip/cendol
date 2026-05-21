use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_assignment_to_incomplete_struct() {
    run_fail_with_message(
        r#"
        struct S;
        extern struct S s1, s2;
        void f() {
            s1 = s2;
        }
        "#,
        "incomplete type",
    );
}

#[test]
fn test_assignment_to_void_lvalue() {
    run_fail_with_message(
        r#"
        void f(void *p) {
            *p = *p;
        }
        "#,
        "incomplete type",
    );
}

#[test]
fn test_assignment_to_const_struct() {
    run_fail_with_message(
        r#"
        struct S { const int x; };
        int main() {
            struct S s1 = {1}, s2 = {2};
            s1 = s2;
            return 0;
        }
        "#,
        "cannot assign to read-only location",
    );
}

#[test]
fn test_assignment_to_const_nested_struct() {
    run_fail_with_message(
        r#"
        struct Inner { const int x; };
        struct S { struct Inner inner; };
        int main() {
            struct S s1 = {{1}}, s2 = {{2}};
            s1 = s2;
            return 0;
        }
        "#,
        "cannot assign to read-only location",
    );
}

#[test]
fn test_increment_const_member() {
    run_fail_with_message(
        r#"
        struct S { const int x; };
        int main() {
            struct S s;
            s.x++;
            return 0;
        }
        "#,
        "cannot assign to read-only location",
    );
}

#[test]
fn test_increment_incomplete_type() {
    run_fail_with_message(
        r#"
        struct S;
        extern struct S s1;
        void f() {
            s1++;
        }
        "#,
        "incomplete type",
    );
}
