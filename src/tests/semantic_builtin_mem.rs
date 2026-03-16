use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};
use crate::tests::codegen_common::run_c_code_exit_status;

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
    // Expected to fail because dest and src should be pointers
    run_fail_with_message(source, "type mismatch");
}

#[test]
fn test_builtin_memset_invalid_args() {
    let source = r#"
        void test(int s, int c, int n) {
            __builtin_memset(s, c, n);
        }
    "#;
    // Expected to fail because s should be a pointer
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
