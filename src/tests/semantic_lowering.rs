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
            assert_eq!(enum_decl.member_len, 3, "EnumDecl should have 3 members");

            let member_start_idx = enum_decl.member_start.index();

            // Check first member RED
            let red_kind = &ast.kinds[member_start_idx];
            if let NodeKind::EnumMember(red) = red_kind {
                assert_eq!(red.name.as_str(), "RED");
                assert_eq!(red.value, 0);
            } else {
                panic!("Expected EnumMember at index {}", member_start_idx);
            }

            // Check second member GREEN
            let green_kind = &ast.kinds[member_start_idx + 1];
            if let NodeKind::EnumMember(green) = green_kind {
                assert_eq!(green.name.as_str(), "GREEN");
                assert_eq!(green.value, 1);
            } else {
                panic!("Expected EnumMember at index {}", member_start_idx + 1);
            }

            // Check third member BLUE
            let blue_kind = &ast.kinds[member_start_idx + 2];
            if let NodeKind::EnumMember(blue) = blue_kind {
                assert_eq!(blue.name.as_str(), "BLUE");
                assert_eq!(blue.value, 2);
            } else {
                panic!("Expected EnumMember at index {}", member_start_idx + 2);
            }
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

#[test]
fn test_function_call_args_contiguity() {
    let (ast, _) = setup_lowering(
        r#"
        int add(int a, int b) { return a + b; }
        int main() {
            return add(1 + 2, 3);
        }
    "#,
    );

    let mut found_call = false;

    // Iterate through all nodes to find the FunctionCall
    for kind in &ast.kinds {
        if let NodeKind::FunctionCall(call) = kind {
            found_call = true;

            // We expect 2 arguments
            assert_eq!(call.arg_len, 2, "FunctionCall should have 2 arguments");

            let arg_start_idx = call.arg_start.index();

            // Check first argument: 1 + 2 (BinaryOp)
            // Note: The BinaryOp node itself should be at arg_start_idx.
            let first_arg = &ast.kinds[arg_start_idx];
            if let NodeKind::BinaryOp(op, ..) = first_arg {
                assert_eq!(*op, crate::ast::BinaryOp::Add, "First argument should be Add BinaryOp");
            } else {
                panic!("Expected BinaryOp at index {}, found {:?}", arg_start_idx, first_arg);
            }

            // Check second argument: 3 (LiteralInt)
            // This node MUST be at arg_start_idx + 1 for contiguity to hold.
            let second_arg = &ast.kinds[arg_start_idx + 1];
            if let NodeKind::LiteralInt(val) = second_arg {
                assert_eq!(*val, 3, "Second argument should be LiteralInt(3)");
            } else {
                panic!(
                    "Expected LiteralInt at index {}, found {:?}",
                    arg_start_idx + 1,
                    second_arg
                );
            }
        }
    }

    assert!(found_call, "Did not find FunctionCall node");
}
