use crate::{
    driver::artifact::CompilePhase,
    tests::test_utils::{run_fail_with_message, run_pass, run_pass_with_diagnostic_message},
};

#[test]
fn test_return_struct_in_int_function() {
    let code = r#"
    typedef struct {
    } S;

    int main() {
        S s;
        return s;
    }
    "#;
    run_fail_with_message(code, "type mismatch: expected int, found struct (anonymous)");
}

#[test]
fn test_return_missing_value() {
    let code = r#"
    int foo() {
        return;
    }
    "#;
    run_fail_with_message(code, "non-void function 'foo' should return a value");
}

#[test]
fn test_return_pointer_as_int() {
    let source = r#"
int f() {
    int x;
    return &x;
}
"#;
    run_pass_with_diagnostic_message(
        source,
        CompilePhase::Mir,
        "assignment makes integer from pointer without a cast",
    );
}

#[test]
fn test_return_local_address() {
    let source = r#"
int *f() {
    int x;
    return &x;
}
"#;
    run_pass_with_diagnostic_message(
        source,
        CompilePhase::Mir,
        "address of stack memory associated with local variable 'x' returned",
    );
}

#[test]
fn test_return_global_address_ok() {
    let source = r#"
int x;
int *f() {
    return &x;
}
"#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_return_static_local_address_ok() {
    let source = r#"
int *f() {
    static int x;
    return &x;
}
"#;
    run_pass(source, CompilePhase::Mir);
}
