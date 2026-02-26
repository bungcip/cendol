use crate::tests::semantic_common::{find_layout, find_record_type, find_var_decl, setup_lowering};
use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_struct_member_alignas() {
    let (_, registry, _) = setup_lowering(
        r#"
        struct S {
            char a;
            _Alignas(8) char b;
        };
        "#,
    );

    let layout = find_layout(&registry, "S");
    assert_eq!(layout.alignment, 8, "Struct S should have alignment 8");

    // Offset of 'b' should be 8 (or at least 8-byte aligned)
    if let crate::semantic::types::LayoutKind::Record { fields, .. } = &layout.kind {
        assert_eq!(fields[1].offset, 8, "Member 'b' should be at offset 8");
    } else {
        panic!("Expected Record layout");
    }
}

#[test]
fn test_member_alignas_type() {
    let (_, registry, _) = setup_lowering(
        r#"
        struct S {
            char a;
            _Alignas(double) char b;
        };
        "#,
    );

    let layout = find_layout(&registry, "S");
    assert_eq!(layout.alignment, 8, "Struct S should have alignment 8 (double)");
}

#[test]
fn test_alignas_zero() {
    let (ast, _, _) = setup_lowering(r#"_Alignas(0) int x;"#);
    let x = find_var_decl(&ast, "x");
    assert_eq!(x.alignment, None, "_Alignas(0) should have no effect (None alignment)");
}

#[test]
fn test_union_member_alignas() {
    let (_, registry, _) = setup_lowering(
        r#"
        union U {
            char a;
            _Alignas(16) char b;
        };
        "#,
    );

    let u_ty = find_record_type(&registry, "U");
    let layout = u_ty.layout.as_ref().expect("Layout not computed for U");

    assert_eq!(layout.alignment, 16, "Union U should have alignment 16");
    assert_eq!(layout.size, 16, "Union U should have size 16");
}

#[test]
fn test_anonymous_struct_member_alignas() {
    let (_, registry, _) = setup_lowering(
        r#"
        struct S {
            char a;
            struct {
                _Alignas(8) char b;
            } c;
        };
        "#,
    );

    let layout = find_layout(&registry, "S");
    assert_eq!(layout.alignment, 8, "Struct S should have alignment 8");

    if let crate::semantic::types::LayoutKind::Record { fields, .. } = &layout.kind {
        // 'c' should be at offset 8 because it has alignment 8
        assert_eq!(fields[1].offset, 8, "Member 'c' should be at offset 8");
    } else {
        panic!("Expected Record layout");
    }
}

#[test]
fn test_alignas_constraints() {
    // C11 6.7.5p3: An alignment specifier shall not be used in a typedef declaration,
    // or in the declaration of a function or a bit-field, or in the declaration
    // of a function parameter, or an object with storage-class specifier register.

    // 1. Typedef
    run_fail_with_message(
        "typedef _Alignas(16) int aligned_int;",
        "alignment specifier cannot be used in a typedef",
    );

    // 2. Function
    run_fail_with_message(
        "_Alignas(16) void f(void);",
        "alignment specifier cannot be used in a function",
    );

    // 3. Bit-field
    run_fail_with_message(
        "struct S { _Alignas(16) int x : 1; };",
        "alignment specifier cannot be used in a bit-field",
    );

    // 4. Function parameter
    run_fail_with_message(
        "void f(_Alignas(8) int x) {}",
        "alignment specifier cannot be used in a function parameter",
    );

    // 5. Register object
    run_fail_with_message(
        "void f() { register _Alignas(8) int x; }",
        "alignment specifier cannot be used in a register object",
    );

    // C11 6.7.5p4: alignment must be at least as strict as natural alignment
    run_fail_with_message(
        "_Alignas(1) int x;",
        "alignment specifier specifies 1-byte alignment, but 4-byte alignment is required",
    );
}
