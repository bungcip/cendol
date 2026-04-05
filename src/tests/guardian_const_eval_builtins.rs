use super::test_utils::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_const_eval_bswap() {
    let code = r#"
        _Static_assert(__builtin_bswap16(0x1234) == 0x3412, "bswap16");
        _Static_assert(__builtin_bswap32(0x12345678) == 0x78563412, "bswap32");
        _Static_assert(__builtin_bswap64(0x123456789ABCDEF0ULL) == 0xF0DEBC9A78563412ULL, "bswap64");

        enum E {
            A = __builtin_bswap16(0x00FF),
            B = __builtin_bswap32(0x0000FFFF),
        };
        _Static_assert(A == 0xFF00, "enum A");
        _Static_assert(B == 0xFFFF0000, "enum B");

        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_const_eval_builtin_choose_expr_float() {
    let code = r#"
        _Static_assert(__builtin_choose_expr(0, 0.0, 1.5) > 1.4, "choose float 0");
        _Static_assert(__builtin_choose_expr(1, 2.5, 0.0) > 2.4, "choose float 1");
        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_const_eval_expect() {
    let code = r#"
        _Static_assert(__builtin_expect(1, 0) == 1, "expect int");
        _Static_assert(__builtin_expect(0, 1) == 0, "expect int 0");

        #define EPSILON 0.000001
        _Static_assert(__builtin_expect(1.5, 0.0) > 1.4, "expect float");

        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_const_eval_constant_p() {
    let code = r#"
        _Static_assert(__builtin_constant_p(1), "constant_p int");
        _Static_assert(__builtin_constant_p(1.5), "constant_p float");
        _Static_assert(__builtin_constant_p(1 + 2), "constant_p expr");

        int x = 0;
        _Static_assert(!__builtin_constant_p(x), "constant_p var");

        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_const_eval_builtin_inf_nan() {
    let code = r#"
        _Static_assert(__builtin_inf() > 1e308, "inf");
        _Static_assert(__builtin_inff() > 1e37f, "inff");

        // NaN != NaN is true
        _Static_assert(__builtin_nan("") != __builtin_nan(""), "nan");

        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_const_eval_builtin_choose_expr_inf() {
    let code = r#"
        // Verify choose_expr works with float constants including inf
        _Static_assert(__builtin_choose_expr(1, __builtin_inf(), 0.0) > 0.0, "choose inf");
        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}
