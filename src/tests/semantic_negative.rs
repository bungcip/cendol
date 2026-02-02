use super::semantic_common::run_fail_with_message;
use crate::driver::artifact::CompilePhase;

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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
        "incomplete type",
    );
}

#[test]
fn test_pointer_comparison_incompatible() {
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
    use crate::tests::semantic_common::check_diagnostic;
    use crate::tests::test_utils;

    let (driver, result) = test_utils::run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok(), "Compilation should succeed with warning");

    assert!(result.is_ok(), "Compilation should succeed with warning");

    // Check for improved message
    check_diagnostic(
        &driver,
        "comparison of incompatible pointer types 'int*' and 'double*'",
        7,
        17,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::SemanticLowering,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
        "called object type 'int' is not a function or function pointer",
    );
}

#[test]
fn test_multiple_storage_class_specifiers() {
    run_fail_with_message(
        r#"
        typedef static int my_int;
        "#,
        CompilePhase::SemanticLowering,
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
        CompilePhase::SemanticLowering,
        "recursive type definition",
    );
}

#[test]
fn test_noreturn_function_returns() {
    run_fail_with_message(
        r#"
        _Noreturn void foo() {
            return;
        }
        "#,
        CompilePhase::Mir,
        "function 'foo' declared '_Noreturn' contains a return statement",
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
        CompilePhase::Mir,
        "incomplete/VLA array in union",
    );
}

#[test]
fn test_variable_of_void_type() {
    run_fail_with_message(
        r#"
        void x;
        "#,
        CompilePhase::Mir,
        "variable has incomplete type 'void'",
    );
}

#[test]
fn test_invalid_alignas_non_power_of_two() {
    run_fail_with_message(
        r#"
        _Alignas(3) int x;
        "#,
        CompilePhase::SemanticLowering,
        "requested alignment is not a positive power of 2",
    );
}
