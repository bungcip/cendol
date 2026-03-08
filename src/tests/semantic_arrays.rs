use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::{setup_lowering, setup_mir};
use crate::tests::test_utils::{run_fail_with_message, run_pass, run_pass_with_diagnostic_message};

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
    assert_eq!(registry.display_qual_type(ty), "const int[5]");
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
    assert_eq!(registry.display_qual_type(ty), "const int[3][2]");
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

    // Ensure compilation passes and check the type
    run_pass(source, CompilePhase::Mir);
    let (ast, registry, _) = setup_lowering(source);
    assert_eq!(registry.display_qual_type(find_var_type(&ast, "arr")), "int[2]");
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
    type %t4 = u64
    type %t5 = ptr<%t2>
    type %t6 = ptr<%t0>

    fn f1(%param0: i32) -> void
    {
      locals {
        %test: ptr<i8>
        %3: u64
        %4: u64
        %6: i32
        %7: i32
        %8: i32
      }

      bb1:
        %4 = cast<u64>(%param0) * const 1
        %3 = %4
        %test = call malloc(%4)
        cond_br const 0, bb3, bb4

      bb2:
        br bb5

      bb3:
        br bb2

      bb4:
        br bb5

      bb5:
        %6 = %param0
        %7 = %param0 + const -1
        %param0 = %7
        %8 = %6 == const 0
        cond_br %8, bb6, bb7

      bb6:
        return

      bb7:
        br bb8

      bb8:
        br bb2
    }

    extern fn malloc(%param0: u64) -> ptr<void>
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
    type %t3 = u64
    type %t4 = ptr<%t1>
    type %t5 = ptr<%t0>

    fn f() -> void
    {
      locals {
        %n: i32
        %m: i32
        %arr: ptr<i32>
        %4: u64
        %5: i32
        %6: u64
      }

      bb1:
        %n = const 10
        %m = const 5
        %5 = %n + %m
        %6 = cast<u64>(%5) * const 4
        %4 = %6
        %arr = call malloc(%6)
        return
    }

    extern fn malloc(%param0: u64) -> ptr<void>
    ");
}

#[test]
fn test_array_in_condition_warning() {
    let source = r#"
        int main() {
            int a[5];
            if (a) {
                return 0;
            }
            return 1;
        }
    "#;
    run_pass_with_diagnostic_message(
        source,
        CompilePhase::Mir,
        "address of array 'a' will always evaluate to 'true'",
    );
}

#[test]
fn test_array_parameter_qualifiers_pass() {
    // C11 6.7.6.3p7: a[const] is adjusted to * const a
    run_fail_with_message(
        "void f(int a[const 10]) { a = 0; }",
        "cannot assign to read-only location",
    );
}

#[test]
fn test_array_parameter_static_pass() {
    run_pass("void f(int a[static 10]) { }", CompilePhase::Mir);
}

#[test]
fn test_array_of_pointers_static_pass() {
    // int *a[static 10] -> array 10 of pointer to int.
    // Adjusted to: int ** const a (or similar)
    // Dimension 10 is outermost.
    run_pass("void f(int *a[static 10]) { }", CompilePhase::Mir);
}

#[test]
fn test_array_qualifiers_outside_parameter_fail() {
    run_fail_with_message(
        "int a[const 10];",
        "type qualifiers in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_array_static_outside_parameter_fail() {
    run_fail_with_message(
        "int a[static 10];",
        "static in array declarator only allowed in function parameters",
    );
}

#[test]
fn test_array_static_not_outermost_fail() {
    run_fail_with_message(
        "void f(int a[10][static 5]) { }",
        "static in array declarator only allowed in outermost array type",
    );
}

#[test]
fn test_array_qualifier_not_outermost_fail() {
    run_fail_with_message(
        "void f(int a[10][const 5]) { }",
        "type qualifiers in array declarator only allowed in outermost array type",
    );
}

#[test]
fn test_pointer_to_array_static_fail() {
    // int (*a)[static 10] -> pointer to array 10 of int.
    // Top level is Pointer. Array is NOT outermost derivation of the parameter.
    run_fail_with_message(
        "void f(int (*a)[static 10]) { }",
        "static in array declarator only allowed in outermost array type",
    );
}

#[test]
fn test_array_of_incomplete_type() {
    run_fail_with_message(
        r#"
        struct A;
        int main() {
            struct A arr[10];
        }
        "#,
        "incomplete type",
    );
}

#[test]
fn test_negative_array_size() {
    run_fail_with_message(
        r#"
        int main() {
            int a[-1];
        }
        "#,
        "size of array is negative",
    );
}
