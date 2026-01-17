use crate::tests::semantic_common::setup_diagnostics_output;

#[test]
fn rejects_typedef_redefinition_with_different_type() {
    let source = r#"
typedef int T;
typedef long T;
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
