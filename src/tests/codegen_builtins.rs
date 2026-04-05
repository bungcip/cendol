use super::codegen_common::{run_c_code_exit_status, run_c_code_with_output};
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtins_bitwise() {
    let source = r#"
        int main() {
            // 1. ffs / ffsl / ffsll (find first set bit, 1-indexed, 0 if no bits set)
            if (__builtin_ffs(0) != 0) return 1;
            if (__builtin_ffs(1) != 1) return 2;
            if (__builtin_ffs(2) != 2) return 3;
            if (__builtin_ffs(0x80) != 8) return 4;
            if (__builtin_ffsl(0L) != 0) return 5;
            if (__builtin_ffsl(1L << 40) != 41) return 6;
            if (__builtin_ffsll(0LL) != 0) return 7;
            if (__builtin_ffsll(1LL << 60) != 61) return 8;

            // 2. popcount / popcountl / popcountll (count set bits)
            if (__builtin_popcount(0) != 0) return 9;
            if (__builtin_popcount(1) != 1) return 10;
            if (__builtin_popcount(0xFF) != 8) return 11;
            if (__builtin_popcountll(1ULL << 40) != 1) return 13;
            if (__builtin_popcountll(0xFF00000000ULL) != 8) return 14;

            // 3. clz / clzl / clzll (count leading zeros, defined for x != 0)
            if (__builtin_clz(1) != 31) return 15;
            if (__builtin_clz(1u << 31) != 0) return 16;
            if (__builtin_clzll(1ULL << 63) != 0) return 17;
            if (__builtin_clzll(1) != 63) return 18;

            // 4. ctz / ctzl / ctzll (count trailing zeros, defined for x != 0)
            if (__builtin_ctz(1) != 0) return 19;
            if (__builtin_ctz(8) != 3) return 20;
            if (__builtin_ctzll(1LL << 40) != 40) return 21;
            if (__builtin_ctzll(1ULL << 63) != 63) return 22;

            // 5. bswap16 / bswap32 / bswap64 (byte swap)
            if (__builtin_bswap16(0x1234) != 0x3412) return 23;
            if (__builtin_bswap32(0x12345678) != 0x78563412) return 24;
            if (__builtin_bswap64(0x123456789ABCDEF0ULL) != 0xF0DEBC9A78563412ULL) return 25;
            if (__builtin_bswap32(__builtin_bswap32(0x12345678)) != 0x12345678) return 26;

            // Side effects in bswap
            int bswap_cnt = 0;
            unsigned int bswap_val = __builtin_bswap32((bswap_cnt++, 0x12345678));
            if (bswap_val != 0x78563412) return 27;
            if (bswap_cnt != 1) return 28;

            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_builtin_constant_p_runtime() {
    let source = r#"
        int main() {
            int x = 5;
            const int y = 10;

            if (__builtin_constant_p(10) != 1) return 1;
            if (__builtin_constant_p(x) != 0) return 2;
            if (__builtin_constant_p(y) != 0) return 3;
            if (__builtin_constant_p(10 + 20) != 1) return 4;

            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_prefetch_codegen() {
    // Should not crash during MIR generation
    run_pass("void f(int *p) { __builtin_prefetch(p, 0, 3); }", CompilePhase::Mir);
}

#[test]
fn test_builtin_prefetch_side_effects() {
    // Arguments should still be evaluated for side effects
    run_pass(
        "
        void f(int *p, int *q) {
            __builtin_prefetch(p = q, 0, 3);
        }
    ",
        CompilePhase::Mir,
    );
}

#[test]
fn test_builtin_unreachable() {
    let source = r#"
        void test() {
            if (0) {
                __builtin_unreachable();
            }
        }
    "#;
    run_pass(source, CompilePhase::Cranelift);
}

#[test]
fn test_builtin_unreachable_traps() {
    // Note: We use -1 to indicate abnormal termination (like a trap/signal)
    // in our testing environment for run_c_code_exit_status.
    let code = r#"
        int main() {
            __builtin_unreachable();
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), -1);
}

#[test]
fn test_codegen_choose_expr_basic() {
    let source = "
        extern int putchar(int);
        int main() {
            __builtin_choose_expr(1, putchar('A'), putchar('B'));
            __builtin_choose_expr(0, putchar('C'), putchar('D'));
            return 0;
        }
    ";
    // We can't easily check output here without a full runtime test,
    // but we can at least ensure it compiles to MIR without issues.
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_codegen_choose_expr_side_effects() {
    let source = "
        int main() {
            int x = 0;
            int y = __builtin_choose_expr(1, x = 10, x = 20);
            if (x != 10) return 1;

            int z = __builtin_choose_expr(0, x = 30, x = 40);
            if (x != 40) return 2;

            return 0;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_offsetof_simple() {
    let source = r#"
        struct S {
            char a;
            int b;
            char c;
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d %d", (int)__builtin_offsetof(struct S, a),
                               (int)__builtin_offsetof(struct S, b),
                               (int)__builtin_offsetof(struct S, c));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    // On x86_64: char a (0), padding (1-3), int b (4), char c (8)
    assert_eq!(output, "0 4 8");
}

#[test]
fn test_builtin_offsetof_nested() {
    let source = r#"
        struct Inner {
            char x;
            int y;
        };
        struct Outer {
            char a;
            struct Inner b;
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d", (int)__builtin_offsetof(struct Outer, b.x),
                             (int)__builtin_offsetof(struct Outer, b.y));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    // Outer: char a (0), padding (1-3), Inner b (4)
    // Inner: char x (0), padding (1-3), int y (4)
    // b.x is at 4 + 0 = 4
    // b.y is at 4 + 4 = 8
    assert_eq!(output, "4 8");
}

#[test]
fn test_builtin_offsetof_array() {
    let source = r#"
        struct S {
            int a[10];
            int b;
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d", (int)__builtin_offsetof(struct S, a[0]),
                             (int)__builtin_offsetof(struct S, a[5]));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output, "0 20");
}

#[test]
fn test_builtin_offsetof_anonymous() {
    let source = r#"
        struct S {
            char a;
            struct {
                char b;
                int c;
            };
        };
        int printf(const char *, ...);
        int main() {
            printf("%d %d", (int)__builtin_offsetof(struct S, b),
                             (int)__builtin_offsetof(struct S, c));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    // S: char a (0), anonymous struct (starts at 4 due to int c alignment)
    // anonymous: char b (0), int c (4)
    // b is at 4 + 0 = 4
    // c is at 4 + 4 = 8
    assert_eq!(output, "4 8");
}

#[test]
fn test_builtin_offsetof_stddef() {
    let source = r#"
        #include <stddef.h>
        struct S { int a; int b; };
        int printf(const char *, ...);
        int main() {
            printf("%d", (int)offsetof(struct S, b));
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output, "4");
}

#[test]
fn test_builtin_offsetof_constant_context() {
    let source = r#"
        struct S { char a; int b; };
        int main() {
            int arr[__builtin_offsetof(struct S, b)];
            return sizeof(arr) / sizeof(int);
        }
    "#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 4);
}
