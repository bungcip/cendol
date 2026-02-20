use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_void_member_prohibited() {
    // C11 6.7.2.1p3: "A structure or union shall not contain a member with incomplete or function type"
    run_fail_with_message(
        r#"
        struct S {
            void v;
        };
        "#,
        "incomplete type",
    );
}

#[test]
fn test_incomplete_struct_member_prohibited() {
    // C11 6.7.2.1p3: "A structure or union shall not contain a member with incomplete or function type"
    run_fail_with_message(
        r#"
        struct Incomplete;
        struct T {
            struct Incomplete s;
        };
        "#,
        "incomplete type",
    );
}

#[test]
fn test_function_member_prohibited() {
    // C11 6.7.2.1p3: "A structure or union shall not contain a member with incomplete or function type"
    run_fail_with_message(
        r#"
        struct S {
            void f(void);
        };
        "#,
        "member 'f' has function type",
    );
}

#[test]
fn test_vla_member_prohibited() {
    // C11 6.7.2.1p3: "A structure or union shall not contain a member with [...] variably modified type"
    run_fail_with_message(
        r#"
        void f(int n) {
            struct S {
                int a[n];
            };
        }
        "#,
        "variably modified type",
    );
}

#[test]
fn test_vla_member_in_middle_prohibited() {
    run_fail_with_message(
        r#"
        void f(int n) {
            struct S {
                int a[n];
                int x;
            };
        }
        "#,
        "variably modified type",
    );
}

#[test]
fn test_fam_in_union_prohibited() {
    // C11 6.7.2.1p18: FAM is a special case for structures, not mentioned for unions.
    // Also 6.7.2.1p3 says unions shall not contain incomplete types.
    run_fail_with_message(
        r#"
        union U {
            int x;
            int a[];
        };
        "#,
        "incomplete/VLA array in union",
    );
}

#[test]
fn test_fam_not_last_prohibited() {
    // C11 6.7.2.1p18: "the last element of a structure ... may have an incomplete array type"
    run_fail_with_message(
        r#"
        struct S {
            int a[];
            int x;
        };
        "#,
        "flexible array member must be the last member of a structure",
    );
}

#[test]
fn test_fam_in_otherwise_empty_struct_prohibited() {
    // C11 6.7.2.1p18: "the last element of a structure with more than one named member ..."
    run_fail_with_message(
        r#"
        struct S {
            int a[];
        };
        "#,
        "flexible array member in otherwise empty structure",
    );
}
