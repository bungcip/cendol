use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

// A. __builtin_choose_expr
#[test]
fn test_semantic_choose_expr_basic() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(1, 10, 20);
            int b = __builtin_choose_expr(0, 10, 20);
            return a + b;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_type_mismatch() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(0, 10, \"hello\");
            return a;
        }
    ";
    run_fail_with_message(source, "type mismatch: expected int, found char[6]");
}

#[test]
fn test_semantic_choose_expr_const_context() {
    let source = "
        _Static_assert(__builtin_choose_expr(1, 42, 0) == 42, \"x should be 42\");
        int main() { return 0; }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_types() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(1, 10, \"hello\");
            char* b = __builtin_choose_expr(0, 10, \"hello\");
            return a;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_not_constant() {
    let source = "
        int main() {
            int x = 1;
            int a = __builtin_choose_expr(x, 10, 20);
            return a;
        }
    ";
    run_fail_with_message(
        source,
        "condition in '__builtin_choose_expr' is not a constant expression",
    );
}

#[test]
fn test_semantic_choose_expr_lazy_semantic() {
    let source = "
        int main() {
            // Member 'invalid' doesn't exist on int, but it shouldn't matter since branch is not selected
            int a = __builtin_choose_expr(1, 10, ((struct {int x;})0).invalid);
            return a;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_semantic_choose_expr_nested() {
    let source = "
        int main() {
            int a = __builtin_choose_expr(1, __builtin_choose_expr(0, 1, 2), 3);
            return a;
        }
    ";
    run_pass(source, CompilePhase::Mir);
}

// B. __builtin_fabs*
#[test]
fn test_builtin_fabs_semantic() {
    let source = r#"
        double test_fabs(double x) {
            return __builtin_fabs(x);
        }
        float test_fabsf(float x) {
            return __builtin_fabsf(x);
        }
        long double test_fabsl(long double x) {
            return __builtin_fabsl(x);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_fabs_has_builtin() {
    let source = r#"
        #if !__has_builtin(__builtin_fabs)
        #error "__builtin_fabs not supported"
        #endif
        #if !__has_builtin(__builtin_fabsf)
        #error "__builtin_fabsf not supported"
        #endif
        #if !__has_builtin(__builtin_fabsl)
        #error "__builtin_fabsl not supported"
        #endif
        int x;
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_fabs_const() {
    let source = r#"
        _Static_assert(__builtin_fabs(-1.0) == 1.0, "fabs");
        _Static_assert(__builtin_fabsf(-1.0f) == 1.0f, "fabsf");
        _Static_assert(__builtin_fabsl(-1.0L) == 1.0L, "fabsl");
    "#;
    run_pass(source, CompilePhase::Mir);
}

// C. __builtin_memcpy/memset/memmove
#[test]
fn test_builtin_memcpy_semantic() {
    let source = r#"
        void test_memcpy(int *dest, const int *src, unsigned long n) {
            void *ret = __builtin_memcpy(dest, src, n);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_memset_semantic() {
    let source = r#"
        void test_memset(int *s, int c, unsigned long n) {
            void *ret = __builtin_memset(s, c, n);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_memmove_semantic() {
    let source = r#"
        void test_memmove(int *dest, const int *src, unsigned long n) {
            void *ret = __builtin_memmove(dest, src, n);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_mem_has_builtin() {
    let source = r#"
        #if !__has_builtin(__builtin_memcpy)
        #error "__builtin_memcpy not supported"
        #endif
        #if !__has_builtin(__builtin_memset)
        #error "__builtin_memset not supported"
        #endif
        #if !__has_builtin(__builtin_memmove)
        #error "__builtin_memmove not supported"
        #endif
        int main() { return 0; }
    "#;
    run_pass(source, CompilePhase::Preprocess);
}

#[test]
fn test_builtin_memcpy_invalid_args() {
    let source = r#"
        void test(int dest, int src, int n) {
            __builtin_memcpy(dest, src, n);
        }
    "#;
    run_fail_with_message(source, "type mismatch");
}

#[test]
fn test_builtin_memset_invalid_args() {
    let source = r#"
        void test(int s, int c, int n) {
            __builtin_memset(s, c, n);
        }
    "#;
    run_fail_with_message(source, "type mismatch");
}

#[test]
fn test_builtin_memcpy_runtime() {
    let source = r#"
        int main() {
            int a[10];
            int b[10];
            for (int i = 0; i < 10; i++) a[i] = i;
            __builtin_memcpy(b, a, 10 * sizeof(int));
            for (int i = 0; i < 10; i++) {
                if (b[i] != i) return i + 1;
            }
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_builtin_memset_runtime() {
    let source = r#"
        int main() {
            unsigned char a[10];
            __builtin_memset(a, 0xAA, 10);
            for (int i = 0; i < 10; i++) {
                if (a[i] != 0xAA) return i + 1;
            }
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

// D. __builtin_memcmp
#[test]
fn test_builtin_memcmp_semantic() {
    let source = r#"
        void test_memcmp(const void *s1, const void *s2, unsigned long n) {
            int ret = __builtin_memcmp(s1, s2, n);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_memcmp_has_builtin() {
    let source = r#"
        #if !__has_builtin(__builtin_memcmp)
        #error "__builtin_memcmp not supported"
        #endif
        int main() { return 0; }
    "#;
    run_pass(source, CompilePhase::Preprocess);
}

#[test]
fn test_builtin_memcmp_invalid_args() {
    let source = r#"
        void test(int s1, int s2, int n) {
            __builtin_memcmp(s1, s2, n);
        }
    "#;
    run_fail_with_message(source, "type mismatch");
}

#[test]
fn test_builtin_memcmp_runtime() {
    let source = r#"
        int main() {
            char a[] = "abcde";
            char b[] = "abcfg";
            char c[] = "abcde";

            if (__builtin_memcmp(a, c, 5) != 0) return 1;
            if (__builtin_memcmp(a, b, 3) != 0) return 2;
            if (__builtin_memcmp(a, b, 4) >= 0) return 3;
            if (__builtin_memcmp(b, a, 4) <= 0) return 4;

            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

// E. __builtin_prefetch
#[test]
fn test_builtin_prefetch_semantic() {
    // Valid cases
    run_pass(
        "void f(int *p) { __builtin_prefetch(p); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 0); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 1); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 0, 0); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(int *p) { __builtin_prefetch(p, 1, 3); }",
        CompilePhase::SemanticLowering,
    );
    run_pass(
        "void f(void *p) { __builtin_prefetch(p); }",
        CompilePhase::SemanticLowering,
    );

    // Invalid cases
    run_fail_with_message(
        "void f(int p) { __builtin_prefetch(p); }",
        "type mismatch: expected void*, found int",
    );
    run_fail_with_message(
        "void f(int *p) { __builtin_prefetch(p, 2); }",
        "argument 'rw' to '__builtin_prefetch' is out of range",
    );
    run_fail_with_message(
        "void f(int *p) { __builtin_prefetch(p, 0, 4); }",
        "argument 'locality' to '__builtin_prefetch' is out of range",
    );
    run_fail_with_message(
        "void f(int *p, int rw) { __builtin_prefetch(p, rw); }",
        "argument 'rw' to '__builtin_prefetch' must be a constant",
    );
}

#[test]
fn test_builtin_prefetch_pp_feature() {
    run_pass(
        "#if !__has_builtin(__builtin_prefetch)\n#error prefetch not supported\n#endif\nint main(){}",
        CompilePhase::Preprocess,
    );
}

// F. __builtin_types_compatible_p
#[test]
fn test_builtin_types_compatible_p_basic() {
    run_pass(
        r#"
        _Static_assert(__builtin_types_compatible_p(int, int), "int should be compatible with int");
        _Static_assert(__builtin_types_compatible_p(int, signed int), "int should be compatible with signed int");
        _Static_assert(!__builtin_types_compatible_p(int, long), "int should not be compatible with long");
        _Static_assert(__builtin_types_compatible_p(const int, const int), "const int should be compatible with const int");
        _Static_assert(__builtin_types_compatible_p(int, const int), "int should be compatible with const int (qualifiers ignored)");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_pointers() {
    run_pass(
        r#"
        _Static_assert(__builtin_types_compatible_p(int*, int*), "int* should be compatible with int*");
        _Static_assert(!__builtin_types_compatible_p(int*, char*), "int* should not be compatible with char*");
        _Static_assert(__builtin_types_compatible_p(void*, void*), "void* should be compatible with void*");

        _Static_assert(__builtin_types_compatible_p(int * const, int *), "int * const should be compatible with int * (top-level qualifier ignored)");
        _Static_assert(!__builtin_types_compatible_p(const int *, int *), "const int * should not be compatible with int * (not a top-level qualifier)");

        _Static_assert(__builtin_types_compatible_p(volatile int, int), "volatile int should be compatible with int");
        _Static_assert(__builtin_types_compatible_p(const volatile int, int), "const volatile int should be compatible with int");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_typedef() {
    run_pass(
        r#"
        typedef int my_int;
        _Static_assert(__builtin_types_compatible_p(int, my_int), "int should be compatible with my_int");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_enum() {
    run_pass(
        r#"
        enum E { A };
        // enum E with only A=0 now has underlying type `int` (fits in int)
        _Static_assert(__builtin_types_compatible_p(enum E, int), "enum E should be compatible with its underlying type (int)");

        enum E2 { B = -1 };
        _Static_assert(__builtin_types_compatible_p(enum E2, int), "enum E2 should be compatible with its underlying type (int)");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_struct() {
    run_pass(
        r#"
        struct S { int x; };
        _Static_assert(__builtin_types_compatible_p(struct S, struct S), "struct S should be compatible with struct S");

        struct S2 { int x; };
        _Static_assert(!__builtin_types_compatible_p(struct S, struct S2), "struct S should not be compatible with struct S2");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_array() {
    run_pass(
        r#"
        _Static_assert(__builtin_types_compatible_p(int[10], int[10]), "int[10] should be compatible with int[10]");
        _Static_assert(!__builtin_types_compatible_p(int[10], int[11]), "int[10] should not be compatible with int[11]");
        _Static_assert(__builtin_types_compatible_p(int[], int[10]), "int[] should be compatible with int[10]");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

// G. __builtin_unreachable
#[test]
fn test_builtin_unreachable_type() {
    let source = r#"
        void test() {
            __builtin_unreachable();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_unreachable_in_noreturn() {
    // This should pass because __builtin_unreachable() means it does not fall off.
    let source = r#"
        _Noreturn void die(void) {
            __builtin_unreachable();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_unreachable_after_statement() {
    let source = r#"
        _Noreturn void die(void) {
            int x = 1;
            x++;
            __builtin_unreachable();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_unreachable_in_switch() {
    let source = r#"
        int test(int x) {
            switch (x) {
                case 1: return 10;
                default: __builtin_unreachable();
            }
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

// H. Bitwise Builtins
#[test]
fn test_semantic_popcount() {
    run_pass("int main() { return __builtin_popcount(42); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_popcountl(42L); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_popcountll(42LL); }", CompilePhase::Mir);
}

#[test]
fn test_semantic_ffs_const_eval() {
    run_pass(
        "int main() { _Static_assert(__builtin_ffs(0) == 0, \"\"); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { _Static_assert(__builtin_ffs(1) == 1, \"\"); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { _Static_assert(__builtin_ffs(2) == 2, \"\"); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { _Static_assert(__builtin_ffs(0x80) == 8, \"\"); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { _Static_assert(__builtin_ffsl(0L) == 0, \"\"); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { _Static_assert(__builtin_ffsl(1L << 40) == 41, \"\"); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { _Static_assert(__builtin_ffsll(0LL) == 0, \"\"); return 0; }",
        CompilePhase::Mir,
    );
    run_pass(
        "int main() { _Static_assert(__builtin_ffsll(1LL << 60) == 61, \"\"); return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_semantic_ffs() {
    run_pass("int main() { return __builtin_ffs(42); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_ffsl(42L); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_ffsll(42LL); }", CompilePhase::Mir);
}

#[test]
fn test_semantic_clz() {
    run_pass("int main() { return __builtin_clz(42); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_clzl(42L); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_clzll(42LL); }", CompilePhase::Mir);
}

#[test]
fn test_semantic_ctz() {
    run_pass("int main() { return __builtin_ctz(42); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_ctzl(42L); }", CompilePhase::Mir);
    run_pass("int main() { return __builtin_ctzll(42LL); }", CompilePhase::Mir);
}

#[test]
fn test_semantic_bitwise_invalid_type() {
    run_fail_with_message(
        "int main() { return __builtin_popcount(42.0); }",
        "type mismatch: expected integer type, found double",
    );
    run_fail_with_message(
        "int main() { return __builtin_clz(\"hello\"); }",
        "type mismatch: expected integer type, found char*",
    );
}
