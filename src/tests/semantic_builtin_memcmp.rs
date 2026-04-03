use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

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
