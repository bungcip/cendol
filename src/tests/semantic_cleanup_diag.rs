#[cfg(test)]
mod cleanup_diagnostic {
    use crate::driver::artifact::CompilePhase;
    use crate::tests::test_utils::*;

    #[test]
    fn test_cleanup_on_global() {
        // GCC/Clang only allow cleanup on local variables.
        // Cendol should warn or error.
        // Current implementation in lowering.rs warns.
        run_pass_with_diagnostic_message(
            r#"
            void clean(int *p) {}
            int __attribute__((cleanup(clean))) global_var;
            int main() { return 0; }
        "#,
            CompilePhase::Mir,
            "'__cleanup__' attribute only applies to local variables",
        );
    }

    #[test]
    fn test_cleanup_on_typedef() {
        // cleanup attribute on a type is ignored.
        run_pass_with_diagnostic_message(
            r#"
            void clean(int *p) {}
            typedef int __attribute__((cleanup(clean))) clean_int;
            int main() { 
                clean_int x = 0;
                return 0; 
            }
        "#,
            CompilePhase::Mir,
            "ignored on type",
        );
    }
}
