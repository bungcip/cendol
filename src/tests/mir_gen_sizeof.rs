use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_sizeof_return_type() {
    run_pass(
        r#"
        void *calloc(unsigned long nmemb, unsigned long size);
        int main() {
            int *p = calloc(10, sizeof(int));
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_alignof_return_type() {
    run_pass(
        r#"
        unsigned long f(unsigned long x) { return x; }
        int main() {
            f(_Alignof(int));
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_offsetof_return_type() {
    run_pass(
        r#"
        struct S { int x; int y; };
        unsigned long f(unsigned long x) { return x; }
        int main() {
            f(__builtin_offsetof(struct S, y));
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}
