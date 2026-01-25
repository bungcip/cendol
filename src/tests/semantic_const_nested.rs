#[cfg(test)]
mod tests {
    use super::super::semantic_common::setup_diagnostics_output;

    #[test]
    fn test_nested_const_pointer() {
        let code = "
            const int x = 10;
            const int *p = &x;
            void test() {
                *p = 20;
            }
        ";
        let output = setup_diagnostics_output(code);
        insta::assert_snapshot!(output, @r"
        Diagnostics count: 1

        Level: Error
        Message: cannot assign to read-only location
        Span: SourceSpan(source_id=SourceId(2), start=104, end=111)
        ");
    }

    #[test]
    fn test_const_pointer_to_int() {
        let code = "
            int x = 10;
            int * const p = &x;
            void test() {
                *p = 20; // This should be OK
                p = 0;   // This should fail
            }
        ";
        let output = setup_diagnostics_output(code);
        insta::assert_snapshot!(output, @r"
        Diagnostics count: 1

        Level: Error
        Message: cannot assign to read-only location
        Span: SourceSpan(source_id=SourceId(2), start=145, end=150)
        ");
    }

    #[test]
    fn test_nested_qualifier_preservation() {
        let code = "
            const int x = 10;
            const int * const p = &x;
            void test() {
                *p = 20; // Should fail (pointee is const)
                p = 0;   // Should fail (pointer is const)
            }
        ";
        let output = setup_diagnostics_output(code);
        insta::assert_snapshot!(output, @r"
        Diagnostics count: 2

        Level: Error
        Message: cannot assign to read-only location
        Span: SourceSpan(source_id=SourceId(2), start=111, end=118)

        Level: Error
        Message: cannot assign to read-only location
        Span: SourceSpan(source_id=SourceId(2), start=170, end=175)
        ");
    }
}
