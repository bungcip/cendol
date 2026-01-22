//! semantic_generic.rs - Test cases for C11 _Generic expressions
//!
//! This module contains tests for the semantic analysis of _Generic expressions.
//! It verifies that the type resolver correctly determines the type of a
//! _Generic expression based on the type of its controlling expression.

use super::semantic_common::{setup_diagnostics_output, setup_mir};

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
fn test_generic_selection_invalid_type_name() {
    let source = r#"
    int main() {
        int x = 0;
        // 'NotARealType' is not a valid type.
        _Generic(x, int: 1, NotARealType: 2, default: 3);
        return 0;
    }
    "#;

    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    // The controlling expression `x` is `const int`.
    // C11 6.5.1.1p2: lvalue conversion drops qualifiers, so `x` becomes `int`.
    // The `int:` association should be chosen, resulting in `my_a`.
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
    // Verify that string literals decay to `char *` (or compatible) in `_Generic`.
    // C11 6.5.1.1p3 states the controlling expression undergoes lvalue conversion.
    let source = r#"
        int main() {
            // "hello" matches char* (1)
            return _Generic("hello", char *: 1, const char *: 2, default: 3);
        }
    "#;

    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_generic_duplicate_associations() {
    // FIXME: The compiler currently accepts duplicate associations, but C11 6.5.1.1p2 forbids them.
    // The snapshot currently shows 0 diagnostics.
    let source = r#"
    int main() {
        int x;
        _Generic(x, int: 1, int: 2);
        return 0;
    }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
