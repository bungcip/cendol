use crate::tests::test_utils::setup_diagnostics_output;

/// Test that empty declarations (e.g., `int;`) emit warnings instead of panicking
#[test]
fn test_empty_type_declaration_single() {
    let source = r#"
        int main() {
            int;
            return 0;
        }
    "#;

    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

/// Test multiple empty declarations
#[test]
fn test_empty_declarations_multiple() {
    let source = r#"
        char;
        char;
        int;
        int;
        int;
        
        int main() {
            return 0;
        }
    "#;

    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 5

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=9, end=14)

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=23, end=28)

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=37, end=41)

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=50, end=54)

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=63, end=67)
    ");
}

/// Test empty declaration in function scope
#[test]
fn test_empty_declaration_in_function() {
    let source = r#"
        int main() {
            int;
            char;
            float;
            return 0;
        }
    "#;

    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 3

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=34, end=38)

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=51, end=56)

    Level: Warning
    Message: declaration does not declare anything
    Span: SourceSpan(source_id=SourceId(2), start=69, end=75)
    ");
}
