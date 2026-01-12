#[cfg(test)]
mod tests {
    use crate::driver::artifact::CompilePhase;
    use crate::tests::semantic_common::run_pass;

    #[test]
    fn test_signed_int() {
        let code = "typedef signed int int32_t; int main() { int32_t x = 0; return 0; }";
        run_pass(code, CompilePhase::Mir);
    }

    #[test]
    fn test_signed_long() {
        let code = "typedef signed long int64_t; int main() { int64_t l = 0; return 0; }";
        run_pass(code, CompilePhase::Mir);
    }

    #[test]
    fn test_signed_char() {
        let code = "signed char c = 'a'; int main() { return 0; }";
        run_pass(code, CompilePhase::Mir);
    }

    #[test]
    fn test_unsigned_int() {
        let code = "unsigned int x = 0; int main() { return 0; }";
        run_pass(code, CompilePhase::Mir);
    }
}
