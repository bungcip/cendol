use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::setup_mir;
use crate::tests::test_utils::{run_pass, setup_diagnostics_output};

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
    run_pass(code, CompilePhase::SemanticLowering);
}

#[test]
fn test_array_param_qualifiers_definition_compatibility() {
    let code = r#"
        void foo(int x[const 5]);
        void foo(int x[volatile 5]) { 
            x[0] = 1;
        }
    "#;
    run_pass(code, CompilePhase::SemanticLowering);
}

#[test]
fn test_conflicting_types_basic() {
    let code = r#"
        void foo(int *x);
        void foo(const int *x); // Conflict
    "#;
    let output = setup_diagnostics_output(code);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 2

    Level: Error
    Message: conflicting types for 'foo'
    Span: SourceSpan(source_id=SourceId(2), start=35, end=58)

    Level: Note
    Message: previous declaration is here
    Span: SourceSpan(source_id=SourceId(2), start=9, end=26)
    ");
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
    run_pass(code, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_basic() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            printf("%s", __func__);
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_in_main() {
    let source = r#"
        int printf(const char *, ...);
        int main() {
            printf("%s", __func__);
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_type() {
    let source = r#"
        void foo() {
            // __func__ is static const char[]
            // so it decays to const char*
            const char *p = __func__;
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_redefinition() {
    let source = r#"
        void foo() {
            int __func__;
        }
    "#;
    // Shadows implicitly declared __func__ in SAME scope is an error in C11
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 2

    Level: Error
    Message: redefinition of '__func__'
    Span: SourceSpan(source_id=SourceId(2), start=34, end=47)

    Level: Note
    Message: previous definition is here
    Span: SourceSpan(source_id=SourceId(2), start=9, end=57)
    ");
}

#[test]
fn test_func_identifier_nested_scope() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            {
                 // Should access outer __func__
                 printf("%s", __func__);
            }
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_opt_unused() {
    let source = r#"
        void foo() {
            // __func__ is not used here
        }
    "#;
    // Check the MIR to ensure __func__ global is NOT generated.
    let mir_output = setup_mir(source);
    insta::assert_snapshot!(mir_output, @r"
    type %t0 = void

    fn foo() -> void
    {

      bb1:
        return
    }
    ");
}

#[test]
fn test_func_opt_used() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            printf("%s", __func__);
        }
    "#;
    let mir_output = setup_mir(source);
    insta::assert_snapshot!(mir_output, @r#"
    type %t0 = i32
    type %t1 = i8
    type %t2 = ptr<%t1>
    type %t3 = void
    type %t4 = fn(%t2, ...) -> %t0
    type %t5 = [3]%t1
    type %t6 = [3]%t1
    type %t7 = [4]%t1
    type %t8 = [4]%t1

    global @.L.str0: [3]i8 = const "%s"
    global @__func__.3: [4]i8 = const array_literal [const 102, const 111, const 111, const 0]

    extern fn printf(%param0: ptr<i8>, ...) -> i32

    fn foo() -> void
    {

      bb1:
        call printf(cast<ptr<i8>>(const @.L.str0), cast<ptr<i8>>(addr_of(@__func__.3)))
        return
    }
    "#);
}

#[test]
fn test_func_opt_shadowed() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            const char* __func__ = "local";
            printf("%s", __func__);
        }
    "#;
    // Redefinition in same scope
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 2

    Level: Error
    Message: redefinition of '__func__'
    Span: SourceSpan(source_id=SourceId(2), start=73, end=104)

    Level: Note
    Message: previous definition is here
    Span: SourceSpan(source_id=SourceId(2), start=48, end=150)
    ");
}

#[test]
fn test_noreturn_function_returns_error() {
    let a = r#"
            _Noreturn void foo() {
                return;
            }
        "#;
    let output = setup_diagnostics_output(a);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: function 'foo' declared '_Noreturn' contains a return statement
    Span: SourceSpan(source_id=SourceId(2), start=52, end=59)
    ");
}
// tests for _Noreturn function specifier

#[test]
fn test_noreturn_function_can_fall_through() {
    let src = r#"
    _Noreturn void foo() {
    }
    "#;
    let output = setup_diagnostics_output(src);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: function 'foo' declared '_Noreturn' can fall off the end
    Span: SourceSpan(source_id=SourceId(2), start=5, end=33)
    ");
}

#[test]
fn test_noreturn_function_returns() {
    let src = r#"
    _Noreturn int foo() {
        return 1;
    }
    "#;
    let output = setup_diagnostics_output(src);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: function 'foo' declared '_Noreturn' contains a return statement
    Span: SourceSpan(source_id=SourceId(2), start=35, end=44)
    ");
}

#[test]
fn test_noreturn_declaration_mismatch() {
    let src = r#"
    _Noreturn void foo();
    void foo() {
    }
    "#;
    let output = setup_diagnostics_output(src);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 2

    Level: Error
    Message: conflicting types for 'foo'
    Span: SourceSpan(source_id=SourceId(2), start=31, end=49)

    Level: Note
    Message: previous declaration is here
    Span: SourceSpan(source_id=SourceId(2), start=5, end=26)
    ");
}
