#![cfg(test)]
use crate::ast::*;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

#[test]
fn test_function_decl_visit_children_with_c_source() {
    // 1. Setup: Parse some C code to get a valid environment (AST, TypeRegistry, etc.)
    let source = "void f(void);"; // A simple function declaration
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;

    // Get mutable access to the AST
    let ast = artifact.ast.as_mut().unwrap();

    // 2. Locate the FunctionDecl node created from "void f(void);"
    let root = ast.get_root();

    // Scope the borrow of ast
    let decl_node = {
        let kind = ast.get_kind(root);
        if let NodeKind::TranslationUnit(data) = kind {
            // data is &TranslationUnitData. data.decl_start is Copy.
            data.decl_start
        } else {
            panic!("Expected TranslationUnit as root");
        }
    };

    // Ensure it is a FunctionDecl and copy its data
    let mut func_decl_data = {
        let kind = ast.get_kind(decl_node);
        if let NodeKind::FunctionDecl(data) = kind {
            *data // Copy the data
        } else {
            panic!("Expected FunctionDecl, found {:?}", kind);
        }
    };

    // 3. Create a dummy body node and attach it to the FunctionDecl
    let dummy_body_span = SourceSpan::default();
    let dummy_body = ast.push_node(NodeKind::Dummy, dummy_body_span);

    func_decl_data.body = Some(dummy_body);

    // Update the node in the AST
    // We overwrite the existing node with the modified data
    ast.kinds[decl_node.index()] = NodeKind::FunctionDecl(func_decl_data);

    // 4. Verify visit_children visits the body
    let mut visited = false;
    // Borrow ast again for visitation
    let node = &ast.kinds[decl_node.index()];

    node.visit_children(|child| {
        if child == dummy_body {
            visited = true;
        }
    });

    assert!(visited, "FunctionDecl body should be visited when present");
}
