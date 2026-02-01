use crate::tests::semantic_common::{setup_diagnostics_output, setup_mir};

#[test]
fn test_generic_selection_correct_type_is_chosen() {
    let source = r#"
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
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_generic_selection_rejects_multiple_defaults() {
    let source = r#"
        int main() {
            return _Generic(0, default: 0, default: 1);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_generic_selection_rejects_duplicate_types() {
    let source = r#"
        int main() {
            return _Generic(0, int: 0, int: 1);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_generic_selection_rejects_compatible_types_due_to_qualifiers() {
    let source = r#"
        int main() {
            return _Generic(0, int: 0, const int: 1);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_generic_selection_rejects_multiple_matches_even_if_controlling_is_different() {
    // This should fail because int and int are compatible, regardless of the controlling expression being float.
    let source = r#"
        int main() {
            return _Generic(1.0f, int: 0, int: 1, default: 2);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_generic_function_decay() {
    let source = r#"
        void my_func() {}
        int main() {
            return _Generic(my_func, void (*)(void): 0, default: 1);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_generic_selection_with_user_defined_type() {
    let source = r#"
    struct MyStruct { int x; };
    int main() {
        struct MyStruct s;
        _Generic(s, struct MyStruct: 1, default: 0);
        return 0;
    }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_generic_selection_no_match() {
    let source = r#"
    int main() {
        float f = 0.0;
        _Generic(f, int: 1, long: 2);
        return 0;
    }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_generic_selection_strips_qualifiers_and_handles_default_correctly() {
    let source = r#"
    struct A { int a; };
    struct B { int b; };
    int main() {
        const int x = 0;
        struct A my_a;
        struct B my_b;
        int val = (_Generic(x, default: my_b, int: my_a)).a;
        return 0;
    }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_generic_string_literal_decay() {
    let source = r#"
        int main() {
            // String literal decays to 'char *' (not 'const char *' in C)
            return _Generic("hello", char *: 0, default: 1);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_generic_selection_pointer_qualifiers() {
    let source = r#"
        int main() {
            const char *ti;
            // Should match const char *
            return _Generic(ti, const char *: 0, default: 1);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_generic_selection_pointer_to_const_vs_const_pointer() {
    let source = r#"
        int main() {
            char * const ptr;
            // Should match char * (because top-level const is stripped)
            return _Generic(ptr, char *: 0, default: 1);
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}
