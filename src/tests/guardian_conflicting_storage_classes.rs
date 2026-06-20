use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn conflicting_storage_classes() {
    let source = "static extern int x;";
    run_fail_with_diagnostic(source, CompilePhase::SemanticLowering, "conflicting storage class specifiers", 1, 1);
}

#[test]
fn conflicting_storage_classes_auto() {
    let source = "void foo() { auto register int y; }";
    run_fail_with_diagnostic(source, CompilePhase::SemanticLowering, "conflicting storage class specifiers", 1, 14);
}

#[test]
fn conflicting_storage_classes_typedef() {
    let source = "typedef static int z;";
    run_fail_with_diagnostic(source, CompilePhase::SemanticLowering, "conflicting storage class specifiers", 1, 1);
}

#[test]
fn thread_local_allows_static() {
    let source = "_Thread_local static int a;";
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn thread_local_allows_extern() {
    let source = "_Thread_local extern int a;";
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn thread_local_conflicts_with_auto() {
    let source = "void foo() { _Thread_local auto int a; }";
    run_fail_with_diagnostic(source, CompilePhase::SemanticLowering, "conflicting storage class specifiers", 1, 14);
}

#[test]
fn thread_local_conflicts_with_register() {
    let source = "void foo() { _Thread_local register int a; }";
    run_fail_with_diagnostic(source, CompilePhase::SemanticLowering, "conflicting storage class specifiers", 1, 14);
}

#[test]
fn thread_local_conflicts_with_typedef() {
    let source = "_Thread_local typedef int a;";
    run_fail_with_diagnostic(source, CompilePhase::SemanticLowering, "conflicting storage class specifiers", 1, 1);
}
