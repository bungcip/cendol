use super::semantic_common::{setup_diagnostics_output};

#[test]
fn test_assignment_to_const() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int x = 1;
            const int y = 2;
            y = x;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: cannot assign to read-only location
    Location: 5:13
    "###);
}

#[test]
fn test_assignment_to_deref_const_ptr() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int x = 1;
            const int *p = &x;
            *p = 2;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: cannot assign to read-only location
    Location: 5:13
    "###);
}

#[test]
fn test_increment_const() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            const int x = 1;
            x++;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: cannot assign to read-only location
    Location: 4:13
    "###);
}

#[test]
fn test_void_function_return_value() {
    let output = setup_diagnostics_output(
        r#"
        void foo() {
            return 1;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: void function 'foo' should not return a value
    Location: 3:20
    "###);
}

#[test]
fn test_conflicting_function_decl() {
    let output = setup_diagnostics_output(
        r#"
        int foo(int x);
        int foo(double x);
        int main() { return 0; }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 2

    Level: Error
    Message: conflicting types for 'foo'
    Location: 3:9

    Level: Note
    Message: previous declaration is here
    Location: 2:9
    "###);
}

#[test]
fn test_addrof_rvalue() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int *p = &(1 + 2);
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: Expression is not assignable (not an lvalue)
    Location: 3:22
    "###);
}

#[test]
fn test_deref_incomplete_type() {
    let output = setup_diagnostics_output(
        r#"
        struct A;
        int main() {
            struct A *p;
            p->x = 1;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: incomplete type 'struct A'
    Location: 5:13
    "###);
}

#[test]
fn test_pointer_comparison_incompatible() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int x;
            double y;
            int *p = &x;
            double *q = &y;
            if (p == q) {}
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Warning
    Message: comparison of incompatible pointer types 'int*' and 'double*'
    Location: 7:17
    "###);
}

#[test]
fn test_duplicate_member() {
    let output = setup_diagnostics_output(
        r#"
        struct A {
            int x;
            float x;
        };
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 2

    Level: Error
    Message: duplicate member 'x'
    Location: 4:19

    Level: Note
    Message: previous declaration is here
    Location: 3:17
    "###);
}

#[test]
fn test_flexible_array_not_last() {
    let output = setup_diagnostics_output(
        r#"
        struct A {
            int x;
            int arr[];
            int y;
        };
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: flexible array member must be the last member of a structure
    Location: 4:17
    "###);
}

#[test]
fn test_bitfield_invalid_type() {
    let output = setup_diagnostics_output(
        r#"
        struct A {
            float x : 3;
        };
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: bit-field type 'float' is invalid
    Location: 3:19
    "###);
}

#[test]
fn test_enum_redefinition_enumerator() {
    let output = setup_diagnostics_output(
        r#"
        enum E {
            A,
            B,
            A
        };
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 2

    Level: Error
    Message: redefinition of 'A'
    Location: 5:13

    Level: Note
    Message: previous definition is here
    Location: 3:13
    "###);
}

#[test]
fn test_enumerator_outside_enum() {
    let output = setup_diagnostics_output(
        r#"
        enum E { A, B };
        int main() {
            int x = C;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: Undeclared identifier 'C'
    Location: 4:21
    "###);
}

#[test]
fn test_array_of_incomplete_type() {
    let output = setup_diagnostics_output(
        r#"
        struct A;
        int main() {
            struct A arr[10];
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: incomplete type 'struct A'
    Location: 4:22
    "###);
}

#[test]
fn test_negative_array_size() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int a[-1];
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: size of array has non-positive value
    Location: 3:19
    "###);
}

#[test]
fn test_case_outside_switch() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            case 1:
                break;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: 'case' or 'default' label not in switch statement
    Location: 2:20
    "###);
}

#[test]
fn test_duplicate_case() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            switch (1) {
                case 1: break;
                case 1: break;
            }
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: duplicate case value '1'
    Location: 3:24
    "###);
}

#[test]
fn test_designated_init_field_not_found() {
    let output = setup_diagnostics_output(
        r#"
        struct A { int x; };
        int main() {
            struct A a = {.y = 1};
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: no member named 'y' in 'struct A'
    Location: 4:26
    "###);
}

#[test]
fn test_scalar_init_brace_list() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int x = {1, 2};
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: excess elements in scalar initializer
    Location: 3:21
    "###);
}

#[test]
fn test_global_variable_redefinition() {
    let output = setup_diagnostics_output(
        r#"
        int x = 5;
        int x = 10;
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 2

    Level: Error
    Message: redefinition of 'x'
    Location: 3:9

    Level: Note
    Message: previous definition is here
    Location: 2:9
    "###);
}

#[test]
fn test_extern_init_block_scope() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            extern int x = 10;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: invalid initializer
    Location: 2:20
    "###);
}

#[test]
fn test_static_redeclared_non_static() {
    let output = setup_diagnostics_output(
        r#"
        static int foo(void);
        int foo(void) {
            return 0;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 2

    Level: Error
    Message: conflicting linkage for 'foo'
    Location: 3:9

    Level: Note
    Message: previous declaration is here
    Location: 2:9
    "###);
}

#[test]
fn test_modifying_string_literal() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            ("hello")[0] = 'H';
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: cannot assign to read-only location
    Location: 3:14
    "###);
}

#[test]
fn test_sizeof_function_type() {
    let output = setup_diagnostics_output(
        r#"
        int foo(int);
        int main() {
            int x = sizeof(foo);
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: Invalid application of 'sizeof' to a function type
    Location: 4:21
    "###);
}

#[test]
fn test_invalid_restrict() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int restrict x;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: restrict requires a pointer type
    Location: 3:13
    "###);
}

#[test]
fn test_call_non_function() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int x = 10;
            x();
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: called object type 'int' is not a function or function pointer
    Location: 4:13
    "###);
}

#[test]
fn test_multiple_storage_class_specifiers() {
    let output = setup_diagnostics_output(
        r#"
        typedef static int my_int;
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 2

    Level: Error
    Message: conflicting storage class specifiers
    Location: 2:9

    Level: Error
    Message: conflicting storage class specifiers
    Location: 2:9
    "###);
}

#[test]
fn test_recursive_struct_definition() {
    let output = setup_diagnostics_output(
        r#"
        struct A {
            struct A x;
        };
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: recursive type definition
    Location: SourceSpan(1099511627776)
    "###);
}

#[test]
fn test_noreturn_function_returns() {
    let output = setup_diagnostics_output(
        r#"
        _Noreturn void foo() {
            return;
        }
        "#,
    );
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: function 'foo' declared '_Noreturn' should not return
    Location: 2:30
    "###);
}
