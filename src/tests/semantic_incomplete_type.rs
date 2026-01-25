//! Semantic validation tests for incomplete types.
use super::semantic_common::setup_diagnostics_output;

#[test]
fn rejects_sizeof_on_incomplete_struct() {
    let source = r#"
        struct S;
        int main() {
            int x = sizeof(struct S);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Invalid application of 'sizeof' to an incomplete type
    Span: SourceSpan(source_id=SourceId(2), start=60, end=76)
    ");
}

#[test]
fn rejects_function_returning_incomplete_type() {
    let source = r#"
        struct S;
        struct S foo();
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: function has incomplete return type
    Span: SourceSpan(source_id=SourceId(2), start=9, end=47)
    ");
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
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: Invalid application of 'sizeof' to an incomplete type
    Span: SourceSpan(source_id=SourceId(2), start=68, end=79)
    ");
}
