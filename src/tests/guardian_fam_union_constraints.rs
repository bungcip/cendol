use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_union_can_contain_fam_struct() {
    // C11 6.7.2.1p18: "the last element of a structure... may have an incomplete array type"
    // It doesn't explicitly prohibit unions from having such a structure as a member.
    // However, the resulting union ITSELF must then be treated as having a FAM
    // for subsequent constraints.
    run_pass(
        r#"
        struct s { int n; int a[]; };
        union u { int x; struct s s; };
        "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_struct_cannot_contain_union_with_fam() {
    // C11 6.7.2.1p3: "A structure or union shall not contain a member with... an incomplete type,
    // except that the last member of a structure with more than one named member may have
    // incomplete array type".
    // A structure with a FAM member is treated as a structure with a FAM.
    // If a union contains such a structure, the union also "has a flexible array member".
    // Thus, it cannot be a member of another structure unless it's the last one.

    // 1. Union with FAM as non-last member
    run_fail_with_message(
        r#"
        struct s { int n; int a[]; };
        union u { int x; struct s s; };
        struct outer { union u u; int y; };
        "#,
        "invalid use of structure with flexible array member as a member",
    );

    // 2. Union with FAM as array element
    run_fail_with_message(
        r#"
        struct s { int n; int a[]; };
        union u { int x; struct s s; };
        union u array[10];
        "#,
        "invalid use of structure with flexible array member as an array element",
    );
}

#[test]
fn test_nested_fam_constraints() {
    // Test multiple levels of nesting
    run_fail_with_message(
        r#"
        struct s { int n; int a[]; };
        union u1 { struct s s; };
        union u2 { union u1 u1; };
        struct outer { union u2 u2; int y; };
        "#,
        "invalid use of structure with flexible array member as a member",
    );
}

#[test]
fn test_union_with_fam_as_last_member_prohibited() {
    // C11 6.7.2.1p18: "the last element of a structure... may have an incomplete array type".
    // It says "an incomplete array type", not "a type that has a flexible array member".
    // Strictly, only direct incomplete array types are allowed as the FAM of a struct.
    // GCC/Clang also reject structs/unions as the FAM.
    run_fail_with_message(
        r#"
        struct s { int n; int a[]; };
        union u { int x; struct s s; };
        struct outer { int n; union u u; };
        "#,
        "invalid use of structure with flexible array member as a member",
    );
}
