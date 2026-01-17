#[cfg(test)]
mod tests {
    use super::super::semantic_common::run_fail_with_message;
    use crate::driver::artifact::CompilePhase;

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
        run_fail_with_message(code, CompilePhase::Mir, "cannot assign to read-only location");
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
        run_fail_with_message(code, CompilePhase::Mir, "cannot assign to read-only location");
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
        // Both will fail, let's just check one diagnostic.
        run_fail_with_message(code, CompilePhase::Mir, "cannot assign to read-only location");
    }
}
