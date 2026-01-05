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
