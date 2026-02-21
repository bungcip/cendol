use crate::tests::test_utils::setup_diagnostics_output;

#[test]
fn test_return_struct_in_int_function() {
    let code = r#"
    typedef struct {
    } S;

    int main() {
        S s;
        return s;
    }
    "#;
    let output = setup_diagnostics_output(code);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found struct (anonymous)
    Span: SourceSpan(source_id=SourceId(2), start=77, end=78)
    ");
}
