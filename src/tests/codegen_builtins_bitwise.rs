use super::codegen_common::run_c_code_exit_status;
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
        int test_ffs(unsigned int x) { return __builtin_ffs(x); }
        int test_ffsl(unsigned long x) { return __builtin_ffsl(x); }
        int test_ffsll(unsigned long long x) { return __builtin_ffsll(x); }
        int main() {
            return test_popcount(0xF0) + test_clz(0x1) + test_ctz(0x80) + test_ffs(0x80);
        }
    "#;
    run_pass(source, CompilePhase::Cranelift);
}

#[test]
fn test_ffs_codegen() {
    let source = r#"
        int main() {
            if (__builtin_ffs(0) != 0) return 1;
            if (__builtin_ffs(1) != 1) return 2;
            if (__builtin_ffs(2) != 2) return 3;
            if (__builtin_ffs(0x80) != 8) return 4;
            if (__builtin_ffsl(0L) != 0) return 5;
            if (__builtin_ffsl(1L << 40) != 41) return 6;
            if (__builtin_ffsll(0LL) != 0) return 7;
            if (__builtin_ffsll(1LL << 60) != 61) return 8;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
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
    assert_eq!(run_c_code_exit_status(source), 0);
}
