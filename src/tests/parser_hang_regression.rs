use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail;

#[test]
fn test_missing_brace_compound_statement() {
    let source = "int main() { { }";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_missing_brace_compound_statement_at_start() {
    let source = "int main() {";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_missing_brace_nested_compound_statement() {
    let source = "int main() { { { } }";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_struct_missing_brace() {
    let source = "struct A { int a;";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_struct_missing_brace_empty() {
    let source = "struct A {";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_union_missing_brace() {
    let source = "union U { int a;";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_initializer_missing_brace() {
    let source = "int a[] = { 1, 2";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_initializer_missing_brace_empty() {
    let source = "int a[] = {";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_do_while_missing_semicolon() {
    let source = "int main() { do {} while(1) }";
    run_fail(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_enum_missing_brace() {
    let source = "enum E { A, B";
    run_fail(source, CompilePhase::SemanticLowering);
}
