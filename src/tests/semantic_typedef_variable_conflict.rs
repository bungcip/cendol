use crate::tests::semantic_common::setup_diagnostics_output;

#[test]
fn rejects_variable_declaration_conflicting_with_typedef() {
    let source = r#"
typedef int T;
int T;
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
