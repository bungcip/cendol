use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

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
