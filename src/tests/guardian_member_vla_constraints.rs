use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_struct_member_vla_prohibited() {
    // C11 6.7.2.1p9: A member of a structure or union shall not have a variably modified type.
    run_fail_with_message(
        r#"
        void f(int n) {
            struct S {
                int a[n];
            };
        }
        "#,
        "variably modified type (VLA) as struct member",
    );
}

#[test]
fn test_struct_member_vla_fam_prohibited() {
    // C11 6.7.2.1p9: A member of a structure or union shall not have a variably modified type.
    // A FAM is an incomplete array type, but if its element type is variably modified (like int a[][n]),
    // then the FAM itself is a variably modified type and must be rejected.
    run_fail_with_message(
        r#"
        void f(int n) {
            struct S {
                int x;
                int a[][n];
            };
        }
        "#,
        "variably modified type (VLA) as struct member",
    );
}

#[test]
fn test_struct_member_pointer_to_vla_prohibited() {
    // C11 6.7.2.1p9: A member of a structure or union shall not have a variably modified type.
    // A pointer to a VLA is a variably modified type.
    run_fail_with_message(
        r#"
        void f(int n) {
            struct S {
                int (*p)[n];
            };
        }
        "#,
        "variably modified type (VLA) as struct member",
    );
}

#[test]
fn test_union_member_vla_prohibited() {
    // C11 6.7.2.1p9: A member of a structure or union shall not have a variably modified type.
    run_fail_with_message(
        r#"
        void f(int n) {
            union U {
                int a[n];
            };
        }
        "#,
        "variably modified type (VLA) as struct member",
    );
}

#[test]
fn test_union_member_pointer_to_vla_prohibited() {
    // C11 6.7.2.1p9: A member of a structure or union shall not have a variably modified type.
    run_fail_with_message(
        r#"
        void f(int n) {
            union U {
                int (*p)[n];
            };
        }
        "#,
        "variably modified type (VLA) as struct member",
    );
}
