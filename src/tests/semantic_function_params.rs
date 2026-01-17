use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::setup_diagnostics_output_with_phase;

#[test]
fn test_array_param_qualifiers_decay() {
    let code = r#"
        void foo(int x[const 5]);
        void foo(int * const x); // Compatible
        
        void bar(int x[volatile 5]);
        void bar(int * volatile x); // Compatible
        
        void baz(int x[restrict 5]);
        void baz(int * restrict x); // Compatible
        
        void f(int x[5]);
        void f(int *x); // Compatible
    "#;
    let output = setup_diagnostics_output_with_phase(code, CompilePhase::SemanticLowering);
    insta::assert_snapshot!(output);
}

#[test]
fn test_array_param_qualifiers_definition_compatibility() {
    let code = r#"
        void foo(int x[const 5]);
        void foo(int x[volatile 5]) { 
            x[0] = 1;
        }
    "#;
    let output = setup_diagnostics_output_with_phase(code, CompilePhase::SemanticLowering);
    insta::assert_snapshot!(output);
}

#[test]
fn test_conflicting_types_basic() {
    let code = r#"
        void foo(int *x);
        void foo(const int *x); // Conflict
    "#;
    let output = setup_diagnostics_output_with_phase(code, CompilePhase::SemanticLowering);
    insta::assert_snapshot!(output);
}

#[test]
fn test_nested_array_qualifiers() {
    let code = r#"
        // int x[const 5][10] -> x has type array 5 of array 10.
        // Outermost derivation is [const 5].
        // Decays to: pointer to array 10. Pointer is const.
        // int (* const x)[10].
        void foo(int x[const 5][10]);
        void foo(int (* const x)[10]);
    "#;
    let output = setup_diagnostics_output_with_phase(code, CompilePhase::SemanticLowering);
    insta::assert_snapshot!(output);
}
