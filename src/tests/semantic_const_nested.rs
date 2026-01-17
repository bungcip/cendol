#[cfg(test)]
mod tests {
    use crate::tests::semantic_common::setup_diagnostics_output;

    #[test]
    fn test_nested_const_pointer() {
        let code = "
            const int x = 10;
            const int *p = &x;
            void test() {
                *p = 20;
            }
        ";
        // This should fail because *p is const int.
        let output = setup_diagnostics_output(code);
        insta::assert_snapshot!(output);
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
        insta::assert_snapshot!(output);
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
        insta::assert_snapshot!(output);
    }
}
