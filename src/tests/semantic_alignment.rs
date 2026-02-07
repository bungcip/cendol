use crate::tests::semantic_common::{find_layout, find_record_type, find_var_decl, setup_lowering};

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
