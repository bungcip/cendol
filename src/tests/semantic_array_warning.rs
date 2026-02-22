use crate::tests::test_utils::setup_diagnostics_output;

#[test]
fn test_array_in_condition_warning() {
    let source = r#"
        int main() {
            int a[5];
            if (a) {
                return 0;
            }
            return 1;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Warning
    Message: address of array 'a' will always evaluate to 'true'
    Span: SourceSpan(source_id=SourceId(2), start=60, end=61)
    ");
}

#[test]
fn test_function_in_condition_no_warning() {
    let source = r#"
        void f() {}
        int main() {
            if (f) {
                return 0;
            }
            return 1;
        }
    "#;
    // Functions should decay to pointers but no warning is required by the user request
    // (though clang might warn for them too, the request was specifically for the array example).
    let output = setup_diagnostics_output(source);
    assert!(!output.contains("Warning"), "Should not have warning for function");
}
