use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_typedef_struct_union_mismatch() {
    run_fail_with_message(
        r#"
        typedef struct _a a;
        union _a {
          int x;
          int y;
        };
        "#,
        "does not match previous declaration",
    );
}

#[test]
fn test_struct_enum_mismatch() {
    run_fail_with_message(
        r#"
        struct _a;
        enum _a { A };
        "#,
        "does not match previous declaration",
    );
}

#[test]
fn test_enum_struct_mismatch() {
    run_fail_with_message(
        r#"
        enum _a { A };
        struct _a;
        "#,
        "does not match previous declaration",
    );
}
