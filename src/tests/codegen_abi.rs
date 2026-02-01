//! Tests for ABI compatibility and specific types
use crate::tests::codegen_common::setup_cranelift;

#[test]
fn test_long_double_size_x86_64() {
    // This test ensures long double is 16 bytes on x86_64
    if target_lexicon::Triple::host().architecture != target_lexicon::Architecture::X86_64 {
        return;
    }

    let source = r#"
        struct S { long double d; };
        _Static_assert(sizeof(long double) == 16, "long double size mismatch");
        _Static_assert(sizeof(struct S) == 16, "struct size mismatch");
    "#;
    setup_cranelift(source);
}

#[test]
fn test_long_double_variadic_usage() {
    // This ensures we can compile code using long double in variadic args without crashing
    let source = r#"
        #include <stdarg.h>
        void foo(int n, ...) {
            va_list ap;
            va_start(ap, n);
            long double d = va_arg(ap, long double);
        }
    "#;
    setup_cranelift(source);
}
