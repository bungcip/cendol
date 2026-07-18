use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass_with_diagnostic;

#[test]
fn diagnostic_return_local_address() {
    let source = r#"
        int* f() {
            int x = 42;
            return &x;
        }
    "#;
    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "address of stack memory associated with local variable 'x' returned",
        4,
        13,
    );
}

#[test]
fn diagnostic_return_local_array_address() {
    let source = r#"
        int* f() {
            int x[10];
            return x;
        }
    "#;
    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "address of stack memory associated with local variable 'x' returned",
        4,
        13,
    );
}
