use crate::semantic::{ArraySizeType, TypeKind, TypeQualifiers, types::TypeClass};
use crate::tests::semantic_common::{setup_lowering, setup_mir};

fn find_var_type(ast: &crate::ast::Ast, target_name: &str) -> crate::semantic::types::QualType {
    crate::tests::semantic_common::find_var_decl(ast, target_name).ty
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

#[test]
fn test_vla_ice_fix() {
    let source = r#"
            void f1(int argc)
            {
              char test[argc];
              if(0)
              label:
                (void)0;
              if(argc-- == 0)
                return;
              goto label;
            }
        "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i32
    type %t2 = i8
    type %t3 = [0]%t2

    fn f1(%param0: i32) -> void
    {
      locals {
        %test: [0]i8
        %3: i32
        %4: i32
        %5: i32
      }

      bb1:
        cond_br const 0, bb3, bb4

      bb2:
        br bb5

      bb3:
        br bb2

      bb4:
        br bb5

      bb5:
        %3 = %param0
        %4 = %param0 + const -1
        %param0 = %4
        %5 = %3 == const 0
        cond_br %5, bb6, bb7

      bb6:
        return

      bb7:
        br bb8

      bb8:
        br bb2
    }
    ");
}

#[test]
fn test_vla_in_block_scope() {
    let source = r#"
            void f() {
                int n = 10;
                {
                    int m = 5;
                    int arr[n + m];
                }
            }
        "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i32
    type %t2 = [0]%t1

    fn f() -> void
    {
      locals {
        %n: i32
        %m: i32
        %arr: [0]i32
      }

      bb1:
        %n = const 10
        %m = const 5
        return
    }
    ");
}
