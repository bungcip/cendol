use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::{run_fail_with_message, run_pass};

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
    use crate::tests::semantic_common::run_fail_with_diagnostic;

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
// tests_generic.rs - Test cases for C11 _Generic expressions
//
// This module contains tests for the semantic analysis of _Generic expressions.
// It verifies that the type resolver correctly determines the type of a
// _Generic expression based on the type of its controlling expression.

#[test]
fn test_generic_selection_correct_type_is_chosen() {
    run_pass(
        r#"
    struct A { int a_field; };
    struct B { int b_field; };
    int main() {
        long x = 0;
        struct A my_a_instance;
        struct B my_b_instance;
        // With a 'long' controlling expression, this should select the second
        // association, resulting in an expression of type 'struct A'.
        // Accessing '.a_field' on the result should succeed.
        int val = (_Generic(x, int: my_b_instance, long: my_a_instance, default: my_b_instance)).a_field;
        return 0;
    }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_rejects_multiple_defaults() {
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, default: 0, default: 1);
        }
        "#,
        CompilePhase::Mir,
        "duplicate default association",
    );
}

#[test]
fn test_generic_selection_rejects_duplicate_types() {
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, int: 0, int: 1);
        }
        "#,
        CompilePhase::Mir,
        "compatible with previously specified type 'int'",
    );
}

#[test]
fn test_generic_selection_rejects_compatible_types_due_to_qualifiers() {
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, int: 0, const int: 1);
        }
        "#,
        CompilePhase::Mir,
        "compatible with previously specified type 'int'",
    );
}

#[test]
fn test_generic_selection_rejects_multiple_matches_even_if_controlling_is_different() {
    // This should fail because int and int are compatible, regardless of the controlling expression being float.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(1.0f, int: 0, int: 1, default: 2);
        }
        "#,
        CompilePhase::Mir,
        "compatible with previously specified type 'int'",
    );
}

#[test]
fn test_generic_function_decay() {
    run_pass(
        r#"
        void my_func() {}
        int main() {
            return _Generic(my_func, void (*)(void): 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_with_user_defined_type() {
    run_pass(
        r#"
    struct MyStruct { int x; };
    int main() {
        struct MyStruct s;
        _Generic(s, struct MyStruct: 1, default: 0);
        return 0;
    }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_invalid_type_name() {
    run_fail_with_message(
        r#"
    int main() {
        int x = 0;
        // 'NotARealType' is not a valid type.
        _Generic(x, int: 1, NotARealType: 2, default: 3);
        return 0;
    }
    "#,
        CompilePhase::Mir,
        "Unexpected token: expected declaration specifiers",
    );
}

#[test]
fn test_generic_selection_no_match() {
    run_fail_with_message(
        r#"
    int main() {
        float f = 0.0;
        _Generic(f, int: 1, long: 2);
        return 0;
    }
    "#,
        CompilePhase::Mir,
        "controlling expression type 'float' not compatible with any generic association",
    );
}

#[test]
fn test_generic_selection_strips_qualifiers_and_handles_default_correctly() {
    run_pass(
        r#"
    struct A { int a; };
    struct B { int b; };
    int main() {
        const int x = 0;
        struct A my_a;
        struct B my_b;
        int val = (_Generic(x, default: my_b, int: my_a)).a;
        return 0;
    }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_string_literal_decay() {
    run_pass(
        r#"
        int main() {
            // String literal decays to 'char *' (not 'const char *' in C)
            return _Generic("hello", char *: 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_pointer_qualifiers() {
    run_pass(
        r#"
        int main() {
            const char *ti;
            // Should match const char *
            return _Generic(ti, const char *: 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_pointer_to_const_vs_const_pointer() {
    run_pass(
        r#"
        int main() {
            char * const ptr;
            // Should match char * (because top-level const is stripped)
            return _Generic(ptr, char *: 0, default: 1);
        }
    "#,
        CompilePhase::Mir,
    );
}
