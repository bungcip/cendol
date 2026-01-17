use super::semantic_common::setup_diagnostics_output;

// A. Lvalue & Assignment Constraints
#[test]
fn test_assignment_to_const() {
    let source = r#"
        int main() {
            int x = 1;
            const int y = 2;
            y = x;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_assignment_to_deref_const_ptr() {
    let source = r#"
        int main() {
            int x = 1;
            const int *p = &x;
            *p = 2;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_increment_const() {
    let source = r#"
        int main() {
            const int x = 1;
            x++;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// B. Function Semantics
#[test]
fn test_void_function_return_value() {
    let source = r#"
        void foo() {
            return 1;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// B3. Conflicting function declarations
#[test]
fn test_conflicting_function_decl() {
    let source = r#"
        int foo(int x);
        int foo(double x);
        int main() { return 0; }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// C. Pointer & Address Semantics
#[test]
fn test_addrof_rvalue() {
    let source = r#"
        int main() {
            int *p = &(1 + 2);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_deref_incomplete_type() {
    let source = r#"
        struct A;
        int main() {
            struct A *p;
            p->x = 1;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// D. Struct / Union Rules
#[test]
fn test_duplicate_member() {
    let source = r#"
        struct A {
            int x;
            float x;
        };
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_flexible_array_not_last() {
    let source = r#"
        struct A {
            int x;
            int arr[];
            int y;
        };
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_bitfield_invalid_type() {
    let source = r#"
        struct A {
            float x : 3;
        };
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// E. Enum Semantics
#[test]
fn test_enum_redefinition_enumerator() {
    let source = r#"
        enum E {
            A,
            B,
            A
        };
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_enumerator_outside_enum() {
    let source = r#"
        enum E { A, B };
        int main() {
            int x = C;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// F. Array & Type Completeness
#[test]
fn test_array_of_incomplete_type() {
    let source = r#"
        struct A;
        int main() {
            struct A arr[10];
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_negative_array_size() {
    let source = r#"
        int main() {
            int a[-1];
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// G. Control Flow Constraints
#[test]
fn test_case_outside_switch() {
    let source = r#"
        int main() {
            case 1:
                break;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_duplicate_case() {
    let source = r#"
        int main() {
            switch (1) {
                case 1: break;
                case 1: break;
            }
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// H. Initializer Semantics
#[test]
fn test_designated_init_field_not_found() {
    let source = r#"
        struct A { int x; };
        int main() {
            struct A a = {.y = 1};
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_scalar_init_brace_list() {
    let source = r#"
        int main() {
            int x = {1, 2};
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// I. Storage Duration & Linkage
#[test]
fn test_extern_init_block_scope() {
    let source = r#"
        int main() {
            extern int x = 10;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_static_redeclared_non_static() {
    let source = r#"
        static int foo(void);
        int foo(void) {
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

// J. Advanced / Compiler-grade features
#[test]
fn test_modifying_string_literal() {
    let source = r#"
        int main() {
            ("hello")[0] = 'H';
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_sizeof_function_type() {
    let source = r#"
        int foo(int);
        int main() {
            int x = sizeof(foo);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_invalid_restrict() {
    let source = r#"
        int main() {
            int restrict x;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_call_non_function() {
    let source = r#"
        int main() {
            int x = 10;
            x();
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
