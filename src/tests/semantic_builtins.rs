use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_atomic_builtins_compilation() {
    let source = r#"
        void test_atomic(int *ptr, int val, int *expected) {
            int ret;
            ret = __atomic_load_n(ptr, 0);
            __atomic_store_n(ptr, val, 0);
            ret = __atomic_exchange_n(ptr, val, 0);
            _Bool success = __atomic_compare_exchange_n(ptr, expected, val, 0, 0, 0);
            ret = __atomic_fetch_add(ptr, val, 0);
            ret = __atomic_fetch_sub(ptr, val, 0);
            ret = __atomic_fetch_and(ptr, val, 0);
            ret = __atomic_fetch_or(ptr, val, 0);
            ret = __atomic_fetch_xor(ptr, val, 0);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_atomic_semantic_errors() {
    use crate::tests::test_utils::run_fail_with_diagnostic;

    // Invalid memory order type
    let source_memorder = r#"
        void test(int *ptr) {
            __atomic_load_n(ptr, "invalid");
        }
    "#;
    run_fail_with_diagnostic(
        source_memorder,
        CompilePhase::Mir,
        "invalid argument type for atomic builtin: char[8]",
        3,
        34,
    );

    // Invalid pointer type
    let source_ptr = r#"
        void test(int val) {
            __atomic_load_n(val, 0);
        }
    "#;
    run_fail_with_diagnostic(
        source_ptr,
        CompilePhase::Mir,
        "invalid argument type for atomic builtin: int",
        3,
        29,
    );

    // Invalid bitwise operation on float
    let source_bitwise = r#"
        void test(float *ptr, float val) {
            __atomic_fetch_and(ptr, val, 0);
        }
    "#;
    run_fail_with_diagnostic(
        source_bitwise,
        CompilePhase::Mir,
        "invalid argument type for atomic builtin: float",
        3,
        32,
    );
}

#[test]
fn test_atomic_compare_exchange_loop() {
    let source = r#"
        #include <stdbool.h>

        bool atomic_cas(int *ptr, int old, int new_val) {
            return __atomic_compare_exchange_n(ptr, &old, new_val, false, 5, 5);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_expect() {
    let source = r#"
extern int printf (const char *, ...);
typedef unsigned long size_t;

size_t _brk_start, _brk_end;
void * extend_brk(size_t size, size_t align)
{
    size_t mask = align - 1;
    void *ret = 0;

     do {
	 if (__builtin_expect(!!(_brk_start == 0), 0))
	   do {
	       printf("wrong1\n");
	   } while (0);
     } while (0);
     _brk_end = (_brk_end + mask) & ~mask;
     ret = (void *)_brk_end;
     _brk_end += size;

     return ret;
}

static void get_args (int a, int b)
{
  if (a != 1)
    printf("wrong2\n");
  else
    printf("okay\n");
}

void bla(void)
{
  int __ret = 42;
  ({
    if (__builtin_expect(!!(0), 0)) {
      if (__builtin_expect(!!__ret, 0))
        printf("wrong3\n");
      int x = !!(__ret);
    }
    __ret;
  });
  get_args(!!__ret, sizeof(__ret));
}

_Bool chk(unsigned long addr, unsigned long limit, unsigned long size)
{
  _Bool ret;
  /* This just needs to compile, no runtime test.  (And it doesn't compile
     only with certain internal checking added that's not committed).  */
  if (0)
    ret = 0 != (!!(addr > limit - size));
  return ret;
}

int main()
{
  void *r;
  _brk_start = 1024;
  _brk_end = 1024;
  r = extend_brk (4096, 16);
  if (!r)
    printf("wrong4\n");
  else
    printf("okay\n");
  bla();
  return 0;
}
"#;
    run_pass(source, CompilePhase::Mir);
}

// GCC Type Aliases
#[test]
fn test_gnuc_va_list_typedef() {
    let source = r#"
        // Test that __gnuc_va_list is recognized as a type name
        typedef __gnuc_va_list my_va_list;
        
        // Test using it in a function declaration
        int vprintf(const char *fmt, __gnuc_va_list ap);
        
        // Test using it in a struct
        struct format_ctx {
            __gnuc_va_list args;
        };
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_valist_assignment() {
    let src = r#"
    typedef __builtin_va_list va_list;
    void foo(va_list ap) {
        va_list ap2;
        ap2 = ap;
    }
    "#;
    run_pass(src, CompilePhase::Mir);
}

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
fn test_implicit_builtins() {
    let source = r#"
        void test() {
            float f = __builtin_nanf("");
            double d = __builtin_nan("");
            float inf_f = __builtin_inff();
            double inf = __builtin_inf();
            double huge = __builtin_huge_val();
            float huge_f = __builtin_huge_valf();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_trap_semantic() {
    let source = r#"
        void test() {
            __builtin_trap();
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_trap_noreturn() {
    let source = r#"
        void test() {
            __builtin_trap();
            int x = 1; // unreachable but semantically valid
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_trap_expression() {
    let source = r#"
        void test() {
            int x = (__builtin_trap(), 1);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_alloca_success() {
    let source = r#"
        void* test(int n) {
            return __builtin_alloca(n);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_alloca_constant() {
    let source = r#"
        void* test() {
            return __builtin_alloca(100);
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_builtin_alloca_invalid_arg() {
    let source = r#"
        void* test() {
            return __builtin_alloca("invalid");
        }
    "#;
    run_fail_with_message(source, "expected integer type");
}

#[test]
fn test_builtin_constant_p() {
    run_pass(
        r#"
            int main() {
                int x = 5;
                const int y = 10;

                _Static_assert(__builtin_constant_p(10) == 1, "10 is constant");
                _Static_assert(__builtin_constant_p(x) == 0, "x is not constant");
                _Static_assert(__builtin_constant_p(y) == 0, "y is not constant in C");
                _Static_assert(__builtin_constant_p(10 + 20) == 1, "10+20 is constant");

                int arr[__builtin_constant_p(10) ? 10 : -1]; // Valid array size if true
                return 0;
            }
        "#,
        CompilePhase::Mir,
    );
}
