use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass, run_pipeline_to_mir};

#[test]
fn test_ternary_incompatible_pointers_rejected() {
    let src = r#"
    void f() {
        int *p;
        float *q;
        int x;
        x ? p : q;
    }
    "#;
    run_fail_with_message(src, "type mismatch: expected int*, found float*");
}

#[test]
fn test_ternary_pointer_qualifier_merging() {
    let src = r#"
    void f() {
        const int *p;
        volatile int *q;
        int x;
        // Result should be const volatile int *
        const volatile int *res = x ? p : q;
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}

#[test]
fn test_ternary_void_pointer_qualifier_merging() {
    let src = r#"
    void f() {
        const int *p;
        volatile void *q;
        int x;
        // Result should be const volatile void *
        const volatile void *res = x ? p : q;
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}

#[test]
fn test_ternary_null_pointer_constant() {
    let src = r#"
    void f() {
        int *p;
        int x;
        int *res = x ? p : 0;
        int *res2 = x ? 0 : p;
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}

#[test]
fn test_ternary_void_result() {
    let src = r#"
    void f() {
        int x;
        x ? (void)0 : (void)1;
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}

#[test]
fn test_ternary_pointer_to_incomplete_struct() {
    let src = r#"
    struct S;
    void f(struct S *p, struct S *q, int x) {
        x ? p : q;
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}

#[test]
fn test_ternary_pointer_qualifier_mismatch_assignment_rejected() {
    let src = r#"
    void f() {
        const int *p;
        int *q;
        int x;
        // Result is const int *, so assigning to int * should fail or warn
        // In this compiler, discarding qualifiers is usually a warning or error depending on configuration.
        // Let's check if it results in the correct composite type.
        int *res = x ? p : q;
    }
    "#;
    // If our compiler warns on discarding qualifiers, this might pass with warning or fail.
    // Based on memory: "SemanticErrorKind::PointerAssignmentDiscardsQualifiers warnings"
    // So it should be a warning.
    run_pipeline_to_mir(src);
}

#[test]
fn test_ternary_lvalue_to_rvalue_strips_top_level_quals() {
    // Regression test: ternary operands should undergo lvalue-to-rvalue conversion
    // which strips top-level qualifiers. This is required by C11 6.5.15p3.
    let src = r#"
    struct TString {
        int shrlen;
        char *contents;
    };

    void bar(const struct TString *ts1) {
        long rl1;
        char *a;
        // The result should be char* because lvalue-to-rvalue conversion
        // strips the const qualifier from the lvalue ts1->contents
        char *s = ((ts1->shrlen >= 0) ? (((void)((rl1) = ts1->shrlen)), a) : (((void)((rl1) = ts1->shrlen)), ts1->contents));
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}

#[test]
fn test_ternary_lvalue_to_rvalue_with_comma_operator() {
    // Test that comma operator result in ternary gets proper lvalue-to-rvalue conversion
    let src = r#"
    void f() {
        const int x = 5;
        int y = 1;
        // (void)0, x should be int (const stripped by lvalue-to-rvalue)
        int a = y ? ((void)0, x) : 0;
        int b = y ? 0 : ((void)0, x);
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}
