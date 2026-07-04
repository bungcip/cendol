use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_diagnostic;

#[test]
fn bitnot_float() {
    let source = r#"
void foo() {
    float f = 1.0;
    ~f;
}
"#;
    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'float'",
        4,
        5,
    );
}

#[test]
fn unary_plus_pointer() {
    let source = r#"
void foo() {
    int *p;
    +p;
}
"#;
    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'int*'",
        4,
        5,
    );
}

#[test]
fn increment_incomplete_type() {
    let source = r#"
struct Incomplete;
void foo(struct Incomplete *p) {
    p++;
}
"#;
    run_fail_with_diagnostic(
        source,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'struct Incomplete*'",
        4,
        5,
    );
}
