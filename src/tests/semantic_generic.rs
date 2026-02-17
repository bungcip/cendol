use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass, run_pipeline_to_mir};

#[test]
fn test_generic_controlling_expression_must_be_complete() {
    run_fail_with_message(
        r#"
        void foo();
        int main() {
            return _Generic(foo(), default: 1);
        }
        "#,
        "controlling expression type 'void' is an incomplete type",
    );
}

#[test]
fn test_generic_controlling_expression_incomplete_struct() {
    run_fail_with_message(
        r#"
        struct A;
        void f(struct A* p) {
            _Generic(*p, default: 1);
        }
        "#,
        "controlling expression type 'struct A' is an incomplete type",
    );
}

#[test]
fn test_generic_association_must_be_complete() {
    run_fail_with_message(
        r#"
        struct Incomplete;
        int main() {
            return _Generic(0, struct Incomplete: 1, default: 0);
        }
        "#,
        "generic association specifies incomplete type 'struct Incomplete'",
    );
}

#[test]
fn test_generic_association_void_is_incomplete() {
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, void: 1, default: 0);
        }
        "#,
        "generic association specifies incomplete type 'void'",
    );
}

#[test]
fn test_generic_allows_array_decay() {
    // This should pass because array decays to pointer, which is complete.
    run_pass(
        r#"
        int main() {
            int a[10];
            return _Generic(a, int*: 0, default: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_allows_function_decay() {
    run_pass(
        r#"
        void f() {}
        int main() {
            return _Generic(f, void (*)(void): 0, default: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_qualifiers_distinct() {
    run_pass(
        r#"
        int main() {
            int i = 0;
            const int ci = 0;
            // int and const int are distinct types, so both can appear in associations.
            // Note: _Generic controlling expression undergoes lvalue conversion, dropping qualifiers.
            // So 'ci' (const int) becomes 'int', matching 'int' association.
            int r1 = _Generic(ci, int: 1, const int: 2);
            int r2 = _Generic(i, int: 1, const int: 2);
            return r1 + r2;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_pointer_qualifiers_distinct() {
    run_pass(
        r#"
        int main() {
            int *p;
            // int *, const int *, and int * const are all distinct types.
            // p is int *. Matches int *.
            int r1 = _Generic(p, int *: 1, const int *: 2, int * const: 3);

            const int *cp;
            // cp is const int *. Matches const int *.
            int r2 = _Generic(cp, int *: 1, const int *: 2, int * const: 3);

            int * const pc = 0;
            // pc is int * const. Lvalue conversion drops top-level const -> int *. Matches int *.
            // Note: int * const association is unreachable for lvalues, but valid as distinct type.
            int r3 = _Generic(pc, int *: 1, const int *: 2, int * const: 3);

            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_correct_type_is_chosen() {
    run_pass(
        r#"
    struct A { int a_field; };
    struct B { int b_field; };
    int main() {
        long x = 0;
        struct A my_a_instance;
        struct B my_b_instance;
        // With a 'long' controlling expression, this should select the second
        // association, resulting in an expression of type 'struct A'.
        // Accessing '.a_field' on the result should succeed.
        int val = (_Generic(x, int: my_b_instance, long: my_a_instance, default: my_b_instance)).a_field;
        return 0;
    }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_rejects_multiple_defaults() {
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, default: 0, default: 1);
        }
        "#,
        "duplicate default association",
    );
}

#[test]
fn test_generic_selection_rejects_duplicate_types() {
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, int: 0, int: 1);
        }
        "#,
        "compatible with previously specified type 'int'",
    );
}

#[test]
fn test_generic_selection_rejects_multiple_matches_even_if_controlling_is_different() {
    // This should fail because int and int are compatible, regardless of the controlling expression being float.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(1.0f, int: 0, int: 1, default: 2);
        }
        "#,
        "compatible with previously specified type 'int'",
    );
}

#[test]
fn test_generic_function_decay() {
    run_pass(
        r#"
        void my_func() {}
        int main() {
            return _Generic(my_func, void (*)(void): 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_with_user_defined_type() {
    run_pass(
        r#"
    struct MyStruct { int x; };
    int main() {
        struct MyStruct s;
        _Generic(s, struct MyStruct: 1, default: 0);
        return 0;
    }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_invalid_type_name() {
    run_fail_with_message(
        r#"
    int main() {
        int x = 0;
        // 'NotARealType' is not a valid type.
        _Generic(x, int: 1, NotARealType: 2, default: 3);
        return 0;
    }
    "#,
        "Unexpected token: expected declaration specifiers",
    );
}

#[test]
fn test_generic_selection_no_match() {
    run_fail_with_message(
        r#"
    int main() {
        float f = 0.0;
        _Generic(f, int: 1, long: 2);
        return 0;
    }
    "#,
        "controlling expression type 'float' not compatible with any generic association",
    );
}

#[test]
fn test_generic_selection_strips_qualifiers_and_handles_default_correctly() {
    run_pass(
        r#"
    struct A { int a; };
    struct B { int b; };
    int main() {
        const int x = 0;
        struct A my_a;
        struct B my_b;
        int val = (_Generic(x, default: my_b, int: my_a)).a;
        return 0;
    }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_string_literal_decay() {
    run_pass(
        r#"
        int main() {
            // String literal decays to 'char *' (not 'const char *' in C)
            return _Generic("hello", char *: 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_pointer_qualifiers() {
    run_pass(
        r#"
        int main() {
            const char *ti;
            // Should match const char *
            return _Generic(ti, const char *: 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_pointer_to_const_vs_const_pointer() {
    run_pass(
        r#"
        int main() {
            char * const ptr;
            // Should match char * (because top-level const is stripped)
            return _Generic(ptr, char *: 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_complex_generic() {
    run_pipeline_to_mir(
        r#"
        int main() {
            float _Complex fc;
            double _Complex dc;
            int is_float_complex = _Generic(fc, float _Complex: 1, default: 0);
            int is_double_complex = _Generic(dc, double _Complex: 1, default: 0);
            return is_float_complex + is_double_complex;
        }
    "#,
    );
}

#[test]
fn test_complex_long_double() {
    run_pipeline_to_mir(
        r#"
        int main() {
            long double _Complex ldc;
            return _Generic(ldc, long double _Complex: 1, default: 0);
        }
    "#,
    );
}

#[test]
fn test_complex_order() {
    let source = r#"
        int main() {
            float _Complex fc1;
            _Complex float fc2;
            int same = _Generic(fc1, float _Complex: _Generic(fc2, float _Complex: 1, default: 0), default: 0);
            return same;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_generic_selection_lvalue() {
    run_pass(
        r#"
        int main() {
            int x = 0;
            _Generic(0, int: x, default: x) = 10;
            if (x != 10) return 1;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_lvalue_struct() {
    run_pass(
        r#"
        struct S { int a; };
        int main() {
            struct S s = {0};
            _Generic(0, int: s, default: s).a = 10;
            if (s.a != 10) return 1;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
