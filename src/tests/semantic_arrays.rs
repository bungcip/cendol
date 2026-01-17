#[cfg(test)]
mod tests {
    use crate::semantic::{ArraySizeType, TypeKind, TypeQualifiers, types::TypeClass};
    use crate::tests::semantic_common::{setup_lowering, setup_mir};

    fn find_var_type(ast: &crate::ast::Ast, target_name: &str) -> crate::semantic::types::QualType {
        for kind in &ast.kinds {
            if let crate::ast::NodeKind::VarDecl(v) = kind
                && v.name.to_string() == target_name
            {
                return v.ty;
            }
        }
        panic!("Variable '{}' not found in AST", target_name);
    }

    #[test]
    fn test_array_of_qualified_type() {
        // const int arr[5];
        let source = r#"
            void f() {
                const int arr[5];
            }
        "#;

        let (ast, registry, _) = setup_lowering(source);
        let ty = find_var_type(&ast, "arr");

        // Check that top-level QualType has Const qualifier
        assert!(
            ty.qualifiers().contains(TypeQualifiers::CONST),
            "Array type should have CONST qualifier"
        );

        // Check underlying type is Array of Int
        let type_info = registry.get(ty.ty());
        if let TypeKind::Array { size, element_type } = &type_info.kind {
            assert_eq!(size, &ArraySizeType::Constant(5));
            assert!(registry.get(*element_type).kind.to_class() == TypeClass::Builtin);
        } else {
            panic!("Expected Array type, found {:?}", type_info.kind);
        }
    }

    #[test]
    fn test_multidimensional_array_qualified() {
        // const int arr[2][3];
        let source = r#"
            void f() {
                const int arr[2][3];
            }
        "#;

        let (ast, registry, _) = setup_lowering(source);
        let ty = find_var_type(&ast, "arr");

        assert!(
            ty.qualifiers().contains(TypeQualifiers::CONST),
            "Outer array should have CONST"
        );

        // Outer array [2]
        let outer_info = registry.get(ty.ty());
        if let TypeKind::Array {
            element_type: inner_ref,
            size,
        } = &outer_info.kind
        {
            assert_eq!(size, &ArraySizeType::Constant(2));

            // Inner array [3]
            let inner_info = registry.get(*inner_ref);
            if let TypeKind::Array {
                element_type: base_ref,
                size: inner_size,
            } = &inner_info.kind
            {
                assert_eq!(inner_size, &ArraySizeType::Constant(3));
                // Base is Int
                assert!(registry.get(*base_ref).kind.to_class() == TypeClass::Builtin);
            } else {
                panic!("Expected inner array");
            }
        } else {
            panic!("Expected outer array");
        }
    }

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

        // 1. Ensure MIR generation does not crash
        setup_mir(source);

        // 2. Ensure AST structure is correct
        let (ast, registry, _) = setup_lowering(source);
        let ty_ref = find_var_type(&ast, "arr").ty();

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
