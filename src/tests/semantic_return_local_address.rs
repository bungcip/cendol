use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass, run_pass_with_diagnostic};

#[test]
fn test_return_pointer_as_int() {
    let source = r#"
int f() {
    int x;
    return &x;
}
"#;
    run_fail_with_message(source, "type mismatch: expected int, found int*");
}

#[test]
fn test_return_local_address() {
    let source = r#"
int *f() {
    int x;
    return &x;
}
"#;
    // Line 4, column 5 (4 spaces indent + 1)
    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "address of stack memory associated with local variable 'x' returned",
        4,
        5,
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
