use crate::ast::NodeKind;
use crate::driver::compiler::CompilePhase;
use crate::driver::{cli::CompileConfig, compiler::CompilerDriver};

#[test]
fn test_record_decl_members_populated() {
    let source = r#"
        struct Point {
            int x;
            int y;
        };
    "#;

    // Use SymbolResolver phase to get the AST right after lowering
    let phase = CompilePhase::SymbolResolver;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);

    let out = driver.run_pipeline(phase).unwrap();
    let unit = out.units.values().next().unwrap();
    let ast = unit.ast.as_ref().unwrap();

    // Find the RecordDecl node
    let mut found_record_decl = false;
    for node in &ast.nodes {
        if let NodeKind::RecordDecl(record_decl) = &node.kind {
            if record_decl.name.map(|n| n.as_str()) == Some("Point") {
                found_record_decl = true;

                // Assert that members are populated
                assert_eq!(record_decl.members.len(), 2, "RecordDecl should have 2 members");

                let x = &record_decl.members[0];
                assert_eq!(x.name.map(|n| n.as_str()), Some("x"));

                let y = &record_decl.members[1];
                assert_eq!(y.name.map(|n| n.as_str()), Some("y"));
            }
        }
    }

    assert!(found_record_decl, "Did not find RecordDecl for 'Point'");
}

#[test]
fn test_enum_decl_members_populated() {
    let source = r#"
        enum Color {
            RED,
            GREEN,
            BLUE
        };
    "#;

    // Use SymbolResolver phase to get the AST right after lowering
    let phase = CompilePhase::SymbolResolver;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);

    let out = driver.run_pipeline(phase).unwrap();
    let unit = out.units.values().next().unwrap();
    let ast = unit.ast.as_ref().unwrap();

    // Find the EnumDecl node
    let mut found_enum_decl = false;
    for node in &ast.nodes {
        if let NodeKind::EnumDecl(enum_decl) = &node.kind {
            if enum_decl.name.map(|n| n.as_str()) == Some("Color") {
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
    }

    assert!(found_enum_decl, "Did not find EnumDecl for 'Color'");
}

#[test]
fn test_struct_member_qualifiers_preserved() {
    // This test demonstrates that qualifiers on struct members are preserved.
    use crate::semantic::{TypeKind, TypeQualifiers};

    let source = r#"
        struct S {
            const int x;
            volatile int *y;
        };
    "#;

    let phase = CompilePhase::SymbolResolver;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);

    let out = driver.run_pipeline(phase).unwrap();
    let unit = out.units.values().next().unwrap();
    let ast = unit.ast.as_ref().unwrap();
    let registry = unit.type_registry.as_ref().unwrap();

    // Find RecordDecl
    for node in &ast.nodes {
        if let NodeKind::RecordDecl(decl) = &node.kind {
            if decl.name.map(|n| n.as_str()) == Some("S") {
                let members = &decl.members;
                assert_eq!(members.len(), 2);

                if let TypeKind::Record { members, .. } = &registry.get(decl.ty).kind {
                    let x_mem = &members[0];
                    // We expect CONST.
                    assert!(
                        x_mem.member_type.qualifiers().contains(TypeQualifiers::CONST),
                        "Struct member 'x' should be const, but has qualifiers: {:?}",
                        x_mem.member_type.qualifiers()
                    );

                    let y_mem = &members[1];
                    // 'y' is volatile pointer to int.
                    // My fix makes it `volatile pointer`.
                    assert!(
                        y_mem.member_type.qualifiers().contains(TypeQualifiers::VOLATILE),
                        "Struct member 'y' should be volatile, but has qualifiers: {:?}",
                        y_mem.member_type.qualifiers()
                    );
                }
            }
        }
    }
}
