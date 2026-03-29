use super::codegen_common::run_c_code_exit_status;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_clz_const_eval() {
    // 1 in 32-bit: 00000000 00000000 00000000 00000001 -> 31 leading zeros
    // 1 in 64-bit: 00000000 ... 00000001 -> 63 leading zeros
    run_pass(
        "int main() {
            _Static_assert(__builtin_clz(1) == 31, \"clz\");
            _Static_assert(__builtin_clzll(1) == 63, \"clzll\");
            return 0;
        }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_ctz_const_eval() {
    run_pass(
        "int main() {
            _Static_assert(__builtin_ctz(8) == 3, \"ctz\");
            _Static_assert(__builtin_ctzll(1LL << 40) == 40, \"ctzll\");
            return 0;
        }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_popcount_const_eval() {
    run_pass(
        "int main() {
            _Static_assert(__builtin_popcount(0xF0) == 4, \"popcount\");
            _Static_assert(__builtin_popcountll(0xF0000000000ULL) == 4, \"popcountll\");
            return 0;
        }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_has_builtin_bitwise() {
    run_pass(
        "int main() {
            _Static_assert(__has_builtin(__builtin_popcount), \"popcount\");
            _Static_assert(__has_builtin(__builtin_popcountl), \"popcountl\");
            _Static_assert(__has_builtin(__builtin_popcountll), \"popcountll\");
            _Static_assert(__has_builtin(__builtin_clz), \"clz\");
            _Static_assert(__has_builtin(__builtin_clzl), \"clzl\");
            _Static_assert(__has_builtin(__builtin_clzll), \"clzll\");
            _Static_assert(__has_builtin(__builtin_ctz), \"ctz\");
            _Static_assert(__has_builtin(__builtin_ctzl), \"ctzl\");
            _Static_assert(__has_builtin(__builtin_ctzll), \"ctzll\");
            _Static_assert(__has_builtin(__builtin_ffs), \"ffs\");
            _Static_assert(__has_builtin(__builtin_ffsl), \"ffsl\");
            _Static_assert(__has_builtin(__builtin_ffsll), \"ffsll\");
            return 0;
        }",
        CompilePhase::Preprocess,
    );
}

#[test]
fn test_bitwise_runtime() {
    let source = r#"
        int main() {
            if (__builtin_clz(1) != 31) return 1;
            if (__builtin_clzll(1) != 63) return 2;
            if (__builtin_ctz(8) != 3) return 3;
            if (__builtin_ctzll(1LL << 40) != 40) return 4;
            if (__builtin_popcount(0xFF) != 8) return 5;
            if (__builtin_popcountll(0xFF00000000ULL) != 8) return 6;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
