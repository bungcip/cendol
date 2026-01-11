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
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
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
        "redeclaration",
    );
}

#[test]
#[ignore = "still not implemented"]
fn test_enumerator_outside_enum() {
    run_fail_with_message(
        r#"
        enum E { A, B };
        int main() {
            int x = C;
        }
        "#,
        CompilePhase::Mir,
        "undeclared",
    );
}

// F. Array & Type Completeness
#[test]
#[ignore = "still not implemented"]
fn test_array_of_incomplete_type() {
    run_fail_with_message(
        r#"
        struct A;
        int main() {
            struct A arr[10];
        }
        "#,
        CompilePhase::Mir,
        "incomplete element",
    );
}

#[test]
#[ignore = "still not implemented"]
fn test_negative_array_size() {
    run_fail_with_message(
        r#"
        int main() {
            int a[-1];
        }
        "#,
        CompilePhase::Mir,
        "size must be positive",
    );
}

// G. Control Flow Constraints
#[test]
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
fn test_designated_init_field_not_found() {
    run_fail_with_message(
        r#"
        struct A { int x; };
        int main() {
            struct A a = {.y = 1};
        }
        "#,
        CompilePhase::Mir,
        "no such member",
    );
}

#[test]
#[ignore = "still not implemented"]
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
#[ignore = "still not implemented"]
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

#[test]
#[ignore = "still not implemented"]
fn test_static_redeclared_non_static() {
    run_fail_with_message(
        r#"
        static int foo(void);
        int foo(void) {
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "conflicting linkage",
    );
}

// J. Advanced / Compiler-grade features
#[test]
#[ignore = "still not implemented"]
fn test_modifying_string_literal() {
    // This assumes checking if we directly modify "string"[0] or similar.
    // If it tracks `p` from `char *p = "hello"`, that is harder.
    // The user example was: char *p = "hello"; p[0] = 'H';
    // We will try that.
    run_fail_with_message(
        r#"
        int main() {
            ("hello")[0] = 'H';
        }
        "#,
        CompilePhase::Mir,
        "read-only",
    );
}

#[test]
#[ignore = "still not implemented"]
fn test_sizeof_function_type() {
    run_fail_with_message(
        r#"
        int foo(int);
        int main() {
            int x = sizeof(foo);
        }
        "#,
        CompilePhase::Mir,
        "invalid application of 'sizeof'",
    );
}

#[test]
#[ignore = "still not implemented"]
fn test_invalid_restrict() {
    run_fail_with_message(
        r#"
        int main() {
            int x;
            int * restrict p = &x;
            int * restrict q = p;
        }
        "#,
        CompilePhase::Mir,
        "restrict",
    );
}
