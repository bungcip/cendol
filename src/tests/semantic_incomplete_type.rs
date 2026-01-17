//! Semantic validation tests for incomplete types.
use crate::tests::semantic_common::setup_diagnostics_output;

#[test]
fn rejects_sizeof_on_incomplete_struct() {
    let source = r#"
        struct S;
        int main() {
            int x = sizeof(struct S);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn rejects_sizeof_on_incomplete_array() {
    let source = r#"
        extern int arr[];
        int main() {
            int x = sizeof(arr);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
