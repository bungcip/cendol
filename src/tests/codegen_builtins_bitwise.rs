use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_codegen_bitwise_builtins() {
    let source = r#"
        int test_popcount(unsigned int x) { return __builtin_popcount(x); }
        int test_popcountl(unsigned long x) { return __builtin_popcountl(x); }
        int test_popcountll(unsigned long long x) { return __builtin_popcountll(x); }
        int test_clz(unsigned int x) { return __builtin_clz(x); }
        int test_ctz(unsigned int x) { return __builtin_ctz(x); }
        int main() {
            return test_popcount(0xF0) + test_clz(0x1) + test_ctz(0x80);
        }
    "#;
    run_pass(source, CompilePhase::Cranelift);
}

#[test]
fn test_popcountll_regression() {
    let source = r#"
        int main() {
            unsigned long long x = 1ULL << 40;
            // If it was truncated to 32-bit int, popcount would be 0.
            if (__builtin_popcountll(x) != 1) return 1;
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::EmitObject);
}
