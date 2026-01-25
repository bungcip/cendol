// Tests for C11 typedef redefinition rules.

use crate::tests::semantic_common::{setup_diagnostics_output, setup_mir};

#[test]
fn rejects_conflicting_typedef_redefinition() {
    let source = r#"
typedef int T;
typedef float T;
        "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 2

    Level: Error
    Message: redefinition of 'T' with a different type
    Span: SourceSpan(source_id=SourceId(2), start=16, end=32)

    Level: Note
    Message: previous definition is here
    Span: SourceSpan(source_id=SourceId(2), start=1, end=15)
    ");
}

#[test]
fn allows_compatible_typedef_redefinition() {
    let source = r#"
typedef int T;
typedef int T;
        "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @"");
}
