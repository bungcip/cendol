use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_const_pointer_member() {
    let src = r#"
        struct S {
            int * const p;
        };
        void f() {
            struct S s1;
            struct S s2;
            s1 = s2;
        }
    "#;
    run_fail_with_message(src, "cannot assign to read-only location");
}

#[test]
fn test_const_array_member() {
    let src = r#"
        struct S {
            const int a[10];
        };
        void f() {
            struct S s1;
            struct S s2;
            s1 = s2;
        }
    "#;
    run_fail_with_message(src, "cannot assign to read-only location");
}

#[test]
fn test_nested_const_array_member() {
    let src = r#"
        struct Inner {
            const int x;
        };
        struct Outer {
            struct Inner arr[5];
        };
        void f() {
            struct Outer o1;
            struct Outer o2;
            o1 = o2;
        }
    "#;
    run_fail_with_message(src, "cannot assign to read-only location");
}

#[test]
fn test_const_pointer_array_member() {
    let src = r#"
        struct S {
            int * const arr[5];
        };
        void f() {
            struct S s1;
            struct S s2;
            s1 = s2;
        }
    "#;
    run_fail_with_message(src, "cannot assign to read-only location");
}
