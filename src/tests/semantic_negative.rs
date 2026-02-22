use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_message;

// A. Lvalue & Assignment Constraints
#[test]
fn test_assignment_to_const() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 1;
            const int y = 2;
            y = x;
        }
        "#,
        "read-only",
    );
}

#[test]
fn test_assignment_to_deref_const_ptr() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 1;
            const int *p = &x;
            *p = 2;
        }
        "#,
        "read-only",
    );
}

#[test]
fn test_increment_const() {
    run_fail_with_message(
        r#"
        int main() {
            const int x = 1;
            x++;
        }
        "#,
        "read-only",
    );
}

// B. Function Semantics
#[test]
fn test_void_function_return_value() {
    run_fail_with_message(
        r#"
        void foo() {
            return 1;
        }
        "#,
        "void function",
    );
}

// B3. Conflicting function declarations
#[test]
fn test_conflicting_function_decl() {
    run_fail_with_message(
        r#"
        int foo(int x);
        int foo(double x);
        int main() { return 0; }
        "#,
        "conflicting types",
    );
}

// C. Pointer & Address Semantics
#[test]
fn test_addrof_rvalue() {
    run_fail_with_message(
        r#"
        int main() {
            int *p = &(1 + 2);
        }
        "#,
        "lvalue",
    );
}

#[test]
fn test_deref_incomplete_type() {
    run_fail_with_message(
        r#"
        struct A;
        int main() {
            struct A *p;
            p->x = 1;
        }
        "#,
        "incomplete type",
    );
}

#[test]
fn test_pointer_comparison_incompatible() {
    use crate::tests::test_utils::run_pass_with_diagnostic;

    // Should warn but proceed
    let source = r#"
        int main() {
            int x;
            double y;
            int *p = &x;
            double *q = &y;
            if (p == q) {}
        }
    "#;

    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "comparison of incompatible pointer types 'int*' and 'double*'",
        7,
        17,
    );
}

#[test]
fn test_incompatible_struct_pointer_argument() {
    use crate::tests::test_utils::{run_pass, setup_driver};

    // Should warn but proceed - similar to clang's behavior
    let source = r#"
        struct TWO_INTS {int a;int b;};
        int add_two_ints(struct TWO_INTS *p);
        struct A{int a; int b;};
        int main(){
            struct A a;
            a.a = 100;
            a.b = 74;
            struct A b = a;
            return add_two_ints(&b);
        }
    "#;

    run_pass(source, CompilePhase::Mir);

    // Verify the warning was emitted
    let driver = setup_driver(source, CompilePhase::Mir);
    let mut driver = driver;
    let _ = driver.run_pipeline(CompilePhase::Mir);

    let diagnostics = driver.get_diagnostics();
    let found = diagnostics.iter().any(|d| {
        d.message.contains("incompatible pointer types")
            && d.message.contains("struct A*")
            && d.message.contains("struct TWO_INTS*")
    });
    assert!(
        found,
        "Expected warning about incompatible struct pointer types. Got: {:?}",
        diagnostics
    );
}

// D. Struct / Union Rules
#[test]
fn test_duplicate_member() {
    run_fail_with_message(
        r#"
        struct A {
            int x;
            float x;
        };
        "#,
        "duplicate member",
    );
}

#[test]
fn test_flexible_array_not_last() {
    run_fail_with_message(
        r#"
        struct A {
            int x;
            int arr[];
            int y;
        };
        "#,
        "flexible array",
    );
}

#[test]
fn test_bitfield_invalid_type() {
    run_fail_with_message(
        r#"
        struct A {
            float x : 3;
        };
        "#,
        "bit-field",
    );
}

// E. Enum Semantics
#[test]
fn test_enum_redefinition_enumerator() {
    run_fail_with_message(
        r#"
        enum E {
            A,
            B,
            A
        };
        "#,
        "redefinition",
    );
}

#[test]
fn test_enumerator_outside_enum() {
    run_fail_with_message(
        r#"
        enum E { A, B };
        int main() {
            int x = C;
        }
        "#,
        "Undeclared",
    );
}

// F. Array & Type Completeness
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
        "size of array has non-positive value",
    );
}

// G. Control Flow Constraints
#[test]
fn test_case_outside_switch() {
    run_fail_with_message(
        r#"
        int main() {
            case 1:
                break;
        }
        "#,
        "not in switch",
    );
}

#[test]
fn test_duplicate_case() {
    run_fail_with_message(
        r#"
        int main() {
            switch (1) {
                case 1: break;
                case 1: break;
            }
        }
        "#,
        "duplicate case",
    );
}

// H. Initializer Semantics
#[test]
fn test_designated_init_field_not_found() {
    run_fail_with_message(
        r#"
        struct A { int x; };
        int main() {
            struct A a = {.y = 1};
        }
        "#,
        "no member named",
    );
}

#[test]
fn test_scalar_init_brace_list() {
    run_fail_with_message(
        r#"
        int main() {
            int x = {1, 2};
        }
        "#,
        "excess elements",
    );
}

// I. Storage Duration & Linkage
#[test]
fn test_global_variable_redefinition() {
    run_fail_with_message(
        r#"
        int x = 5;
        int x = 10;
        "#,
        "redefinition of",
    );
}

#[test]
fn test_extern_init_block_scope() {
    run_fail_with_message(
        r#"
        int main() {
            extern int x = 10;
        }
        "#,
        "invalid initializer",
    );
}

// J. Advanced / Compiler-grade features
#[test]
fn test_sizeof_function_type() {
    run_fail_with_message(
        r#"
        int foo(int);
        int main() {
            int x = sizeof(foo);
        }
        "#,
        "Invalid application of 'sizeof' to a function type",
    );
}

#[test]
fn test_invalid_restrict() {
    run_fail_with_message(
        r#"
        int main() {
            int restrict x;
        }
        "#,
        "restrict",
    );
}

#[test]
fn test_call_non_function() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 10;
            x();
        }
        "#,
        "called object type 'int' is not a function or function pointer",
    );
}

#[test]
fn test_multiple_storage_class_specifiers() {
    run_fail_with_message(
        r#"
        typedef static int my_int;
        "#,
        "conflicting storage class specifiers",
    );
}

#[test]
fn test_recursive_struct_definition() {
    run_fail_with_message(
        r#"
        struct A {
            struct A x;
        };
        "#,
        "recursive type definition",
    );
}

#[test]
fn test_incomplete_array_in_union() {
    run_fail_with_message(
        r#"
        union U {
            int x[];
        };
        "#,
        "incomplete/VLA array in union",
    );
}

#[test]
fn test_variable_of_void_type() {
    run_fail_with_message(
        r#"
        void x;
        "#,
        "variable has incomplete type 'void'",
    );
}

#[test]
fn test_invalid_alignas_non_power_of_two() {
    run_fail_with_message(
        r#"
        _Alignas(3) int x;
        "#,
        "requested alignment is not a positive power of 2",
    );
}

// K. Type System Edge Cases
#[test]
fn test_sizeof_incomplete_struct() {
    run_fail_with_message(
        r#"
        struct S;
        int main() {
            int x = sizeof(struct S);
        }
        "#,
        "Invalid application of 'sizeof' to an incomplete type",
    );
}

// L. More Control Flow Edge Cases
#[test]
fn test_break_outside_loop() {
    run_fail_with_message(
        r#"
        int main() {
            break;
        }
        "#,
        "break statement not in loop or switch",
    );
}

#[test]
fn test_continue_outside_loop() {
    run_fail_with_message(
        r#"
        int main() {
            continue;
        }
        "#,
        "continue statement not in loop",
    );
}

// M. Expression Validation
#[test]
fn test_invalid_use_of_void_in_expr() {
    run_fail_with_message(
        r#"
        void foo() {}
        int main() {
            int x = foo();
        }
        "#,
        "void",
    );
}

// NOTE: Currently the compiler accepts non-constant global initializers
// This should be rejected but isn't yet implemented

#[test]
fn test_member_access_on_non_struct() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 5;
            x.field = 10;
        }
        "#,
        "not a structure or union",
    );
}

// N. Alignment & Atomic
#[test]
fn test_non_constant_alignment() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 8;
            _Alignas(x) int arr[10];
        }
        "#,
        "not a constant expression",
    );
}

#[test]
fn test_incomplete_return_type() {
    run_fail_with_message(
        r#"
        struct S;
        struct S foo();
        "#,
        "incomplete return type",
    );
}

#[test]
fn test_flexible_array_in_empty_struct() {
    run_fail_with_message(
        r#"
        struct A {
            int arr[];
        };
        "#,
        "flexible array member in otherwise empty structure",
    );
}

// R. Bitfield Edge Cases
#[test]
fn test_bitfield_zero_width() {
    run_fail_with_message(
        r#"
        struct A {
            int x : 0;
        };
        "#,
        "zero-width bit-field shall not specify a declarator",
    );
}

#[test]
fn test_bitfield_non_constant_width() {
    run_fail_with_message(
        r#"
        int main() {
            int n = 5;
            struct A {
                int x : n;
            } a;
        }
        "#,
        "bit-field width is not a constant expression",
    );
}

// S. Undeclared Identifiers
#[test]
fn test_undeclared_variable() {
    run_fail_with_message(
        r#"
        int main() {
            x = 5;
        }
        "#,
        "Undeclared",
    );
}

#[test]
fn test_undeclared_function() {
    run_fail_with_message(
        r#"
        int main() {
            return foo();
        }
        "#,
        "Undeclared",
    );
}
