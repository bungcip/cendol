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

// G. Control Flow Constraints
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
fn test_multiple_storage_class_specifiers() {
    run_fail_with_message(
        r#"
        typedef static int my_int;
        "#,
        "conflicting storage class specifiers",
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

// Consolidated from guardian_linkage.rs and guardian_tentative_definitions.rs
#[test]
fn test_extern_followed_by_static_variable_mismatch() {
    run_fail_with_message(
        r#"
        extern int x;
        static int x;
        "#,
        "conflicting linkage",
    );
}

#[test]
fn test_plain_followed_by_static_variable_mismatch() {
    run_fail_with_message(
        r#"
        int x;
        static int x;
        "#,
        "conflicting linkage",
    );
}

#[test]
fn test_extern_followed_by_static_function_mismatch() {
    run_fail_with_message(
        r#"
        extern void f(void);
        static void f(void) {}
        "#,
        "conflicting linkage",
    );
}

#[test]
fn test_static_tentative_incomplete_type_prohibited() {
    run_fail_with_message("static int arr[];", "incomplete type 'int[]'");
    run_fail_with_message("struct S; static struct S x;", "incomplete type 'struct S'");
}

#[test]
fn test_no_linkage_incomplete_type_prohibited() {
    run_fail_with_message("void f() { int arr[]; }", "incomplete type 'int[]'");
    run_fail_with_message("void f() { static int arr[]; }", "incomplete type 'int[]'");
    run_fail_with_message(
        "void f() { struct S; static struct S x; }",
        "incomplete type 'struct S'",
    );
}

#[test]
fn test_function_parameter_incomplete_type_prohibited() {
    run_fail_with_message("void f(void x) {}", "incomplete type 'void'");
    run_fail_with_message("void f(int x, void y) {}", "incomplete type 'void'");
}
// S. Undeclared Identifiers

// Consolidated from guardian_pointer_assignment_qualifiers.rs and guardian_restrict_constraints.rs
#[test]
fn test_pointer_assignment_discards_const_warning() {
    use crate::tests::test_utils::run_pass_with_diagnostic;
    run_pass_with_diagnostic(
        r#"
        int main() {
            const int *cp;
            int *p;
            p = cp;
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "discards qualifiers",
        5,
        13,
    );
}

#[test]
fn test_restrict_on_function_pointer_prohibited() {
    run_fail_with_message(
        r#"
        void (* restrict f)(void);
        "#,
        "restrict requires a pointer type",
    );
}

#[test]
fn test_restrict_on_non_pointer_prohibited() {
    run_fail_with_message(
        r#"
        int restrict x;
        "#,
        "restrict requires a pointer type",
    );
}

#[test]
fn test_void_pointer_sub_int() {
    run_fail_with_message(
        r#"
        int main() {
            void *p;
            p - 1;
        }
        "#,
        "Invalid operands for binary operation",
    );
}

#[test]
fn test_pointer_sub_incompatible() {
    run_fail_with_message(
        r#"
        int main(void) {
            int *p1 = 0;
            float *p2 = 0;
            return p1 - p2;
        }
        "#,
        "Invalid operands for binary operation",
    );
}

#[test]
fn test_pointer_sub_incomplete() {
    run_fail_with_message(
        r#"
        struct A;
        int main(void) {
            struct A *p1 = 0;
            struct A *p2 = 0;
            return p1 - p2;
        }
        "#,
        "Invalid operands for binary operation",
    );
}
