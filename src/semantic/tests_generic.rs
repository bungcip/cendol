//! tests_generic.rs - Test cases for C11 _Generic expressions
//!
//! This module contains tests for the semantic analysis of _Generic expressions.
//! It verifies that the type resolver correctly determines the type of a
//! _Generic expression based on the type of its controlling expression.

use crate::driver::{
    cli::CompileConfig,
    compiler::{CompilePhase, CompilerDriver},
};

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

    let phase = CompilePhase::Mir;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);

    // This should now succeed without errors.
    driver.run_pipeline(phase).expect("Compilation failed unexpectedly");
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

    let phase = CompilePhase::Mir;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);
    driver.run_pipeline(phase).expect("Compilation failed unexpectedly");
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

    let phase = CompilePhase::Mir;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(phase);

    assert!(result.is_err(), "Compilation should have failed");

    let diags = driver.get_diagnostics();
    assert!(!diags.is_empty(), "Expected at least one diagnostic");
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

    let phase = CompilePhase::Mir;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(phase);

    assert!(result.is_err(), "Compilation should have failed");

    let diags = driver.get_diagnostics();
    assert_eq!(diags.len(), 1);
    assert!(
        diags[0]
            .message
            .contains("controlling expression type does not match any generic association")
    );
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
        // The controlling expression 'x' has type 'const int'.
        // C11 requires stripping the top-level 'const' qualifier, so it should match 'int'.
        // The 'default' case is listed first to ensure that the type-based match is still preferred.
        // The result of the _Generic expression should be of type 'A'.
        int val = (_Generic(x, default: my_b, int: my_a)).a;
        return 0;
    }
    "#;

    let phase = CompilePhase::Mir;
    let config = CompileConfig::from_virtual_file(source.to_string(), phase);
    let mut driver = CompilerDriver::from_config(config);

    // This should now succeed. If it fails, it means the qualifier stripping and default handling are incorrect.
    driver.run_pipeline(phase).expect("Compilation failed unexpectedly");
}
