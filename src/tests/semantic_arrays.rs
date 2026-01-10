#[cfg(test)]
mod tests {
    use crate::driver::artifact::CompilePhase;
    use crate::semantic::{ArraySizeType, TypeKind};
    use crate::tests::test_utils;

    #[test]
    fn test_array_declaration_with_constant_size() {
        let source = r#"
            int main() {
                int arr[2];
                arr[0] = 1;
                arr[1] = 2;
                return arr[0] + arr[1] - 3;
            }
        "#;

        // 1. Ensure MIR generation does not crash (this was the original bug)
        let (_, result_mir) = test_utils::run_pipeline(source, CompilePhase::Mir);
        result_mir.expect("MIR compilation failed");

        // 2. Ensure AST structure is correct (using SemanticLowering phase to keep AST)
        let (_, result_ast) = test_utils::run_pipeline(source, CompilePhase::SemanticLowering);
        let outputs = result_ast.expect("AST compilation failed");
        let (_, artifact) = outputs.units.first().expect("Compile artifact missing");

        let ast = artifact.ast.as_ref().expect("AST missing");
        let symbol_table = artifact.symbol_table.as_ref().expect("Symbol table missing");
        let registry = artifact.type_registry.as_ref().expect("Type registry missing");

        // Inspect the AST to ensure array size is correct
        let root = ast.get_root();

        // Root is TranslationUnit. It has decl_start and decl_len
        let global_decls = if let crate::ast::NodeKind::TranslationUnit(tu) = &ast.kinds[root.index()] {
            tu.decl_start.range(tu.decl_len)
        } else {
            panic!("Root is not TranslationUnit");
        };

        let main_func = global_decls
            .filter(|d| {
                if let crate::ast::NodeKind::Function(f) = &ast.kinds[d.index()] {
                    let name = symbol_table.get_symbol(f.symbol).name;
                    name.to_string() == "main"
                } else {
                    false
                }
            })
            .next()
            .expect("Main function not found");

        if let crate::ast::NodeKind::Function(f) = &ast.kinds[main_func.index()] {
            // Find 'arr' declaration in body
            let body = f.body;
            // Body is a CompoundStatement
            if let crate::ast::NodeKind::CompoundStatement(cs) = &ast.kinds[body.index()] {
                // Find VarDecl in statements
                let arr_decl = cs
                    .stmt_start
                    .range(cs.stmt_len)
                    .find_map(|idx| {
                        if let crate::ast::NodeKind::VarDecl(v) = &ast.kinds[idx.index()] {
                            if v.name.to_string() == "arr" { Some(v) } else { None }
                        } else {
                            None
                        }
                    })
                    .expect("arr declaration not found");

                // Check type of arr
                let ty_ref = arr_decl.ty.ty();

                // It should be an inline array or registry array with constant size 2
                let ty = registry.get(ty_ref);
                if let TypeKind::Array { size, .. } = &ty.kind {
                    match size {
                        ArraySizeType::Constant(s) => assert_eq!(*s, 2, "Array size should be 2"),
                        _ => panic!("Array size should be constant"),
                    }
                } else {
                    panic!("Expected array type, found {:?}", ty.kind);
                }
            }
        }
    }
}
