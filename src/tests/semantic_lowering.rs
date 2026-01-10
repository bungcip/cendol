use super::semantic_common::setup_lowering;
use crate::ast::NodeKind;
use crate::semantic::TypeQualifiers;

#[test]
fn test_record_decl_members_populated() {
    let (ast, _) = setup_lowering(
        r#"
        struct Point {
            int x;
            int y;
        };
    "#,
    );

    // Find the RecordDecl node
    let mut found_record_decl = false;
    for kind in &ast.kinds {
        if let NodeKind::RecordDecl(record_decl) = kind
            && record_decl.name.map(|n| n.as_str()) == Some("Point")
        {
            found_record_decl = true;

            // Assert that members are populated
            assert_eq!(record_decl.member_len, 2, "RecordDecl should have 2 members");

            let member_start_idx = record_decl.member_start.index();

            // Check first member
            let x_kind = &ast.kinds[member_start_idx];
            if let NodeKind::FieldDecl(x) = x_kind {
                assert_eq!(x.name.map(|n| n.as_str()), Some("x"));
            } else {
                panic!("Expected FieldDecl at index {}, found {:?}", member_start_idx, x_kind);
            }

            // Check second member
            let y_kind = &ast.kinds[member_start_idx + 1];
            if let NodeKind::FieldDecl(y) = y_kind {
                assert_eq!(y.name.map(|n| n.as_str()), Some("y"));
            } else {
                panic!(
                    "Expected FieldDecl at index {}, found {:?}",
                    member_start_idx + 1,
                    y_kind
                );
            }
        }
    }

    assert!(found_record_decl, "Did not find RecordDecl for 'Point'");
}

#[test]
fn test_enum_decl_members_populated() {
    let (ast, _) = setup_lowering(
        r#"
        enum Color {
            RED,
            GREEN,
            BLUE
        };
    "#,
    );

    // Find the EnumDecl node
    let mut found_enum_decl = false;
    for kind in &ast.kinds {
        if let NodeKind::EnumDecl(enum_decl) = kind
            && enum_decl.name.map(|n| n.as_str()) == Some("Color")
        {
            found_enum_decl = true;

            // Assert that members are populated
            assert_eq!(enum_decl.members.len(), 3, "EnumDecl should have 3 members");

            let red = &enum_decl.members[0];
            assert_eq!(red.name.as_str(), "RED");
            assert_eq!(red.value, 0);

            let green = &enum_decl.members[1];
            assert_eq!(green.name.as_str(), "GREEN");
            assert_eq!(green.value, 1);

            let blue = &enum_decl.members[2];
            assert_eq!(blue.name.as_str(), "BLUE");
            assert_eq!(blue.value, 2);
        }
    }

    assert!(found_enum_decl, "Did not find EnumDecl for 'Color'");
}

#[test]
fn test_struct_member_qualifiers_preserved() {
    let (ast, _registry) = setup_lowering(
        r#"
        struct S {
            const int x;
            volatile int *y;
        };
    "#,
    );

    // Find RecordDecl
    let mut found = false;
    for kind in &ast.kinds {
        if let NodeKind::RecordDecl(decl) = kind
            && decl.name.map(|n| n.as_str()) == Some("S")
        {
            found = true;
            assert_eq!(decl.member_len, 2);

            let member_start_idx = decl.member_start.index();

            // Check first member x
            let x_kind = &ast.kinds[member_start_idx];
            if let NodeKind::FieldDecl(x_decl) = x_kind {
                // We access the QualType directly from FieldDeclData
                assert!(
                    x_decl.ty.qualifiers().contains(TypeQualifiers::CONST),
                    "Struct member 'x' should be const, but has qualifiers: {:?}",
                    x_decl.ty.qualifiers()
                );
            } else {
                panic!("Expected FieldDecl for x");
            }

            // Check second member y
            let y_kind = &ast.kinds[member_start_idx + 1];
            if let NodeKind::FieldDecl(y_decl) = y_kind {
                assert!(
                    y_decl.ty.qualifiers().contains(TypeQualifiers::VOLATILE),
                    "Struct member 'y' should be volatile, but has qualifiers: {:?}",
                    y_decl.ty.qualifiers()
                );
            } else {
                panic!("Expected FieldDecl for y");
            }
        }
    }
    assert!(found, "Did not find RecordDecl for 'S'");
}
