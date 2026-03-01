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

/// Regression test: sizeof(a)/sizeof(a)[0] pattern used by ARRAY_SIZE macro.
/// sizeof(a)[0] must parse as sizeof((a)[0]), not (sizeof(a))[0].
#[test]
fn test_sizeof_array_size_macro() {
    run_pass(
        r#"
        #define ARRAY_SIZE(a) ((unsigned int)((sizeof (a))/(sizeof (a)[0])))
        int arr[5];
        int x = ARRAY_SIZE(arr);
        int main() {
            return x == 5 ? 0 : 1;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

/// Regression test: float constant folding in global struct initializers.
/// Expressions like 1/2.2 must be constant-folded at compile time.
#[test]
fn test_float_constant_folding_in_global_init() {
    run_pass(
        r#"
        struct S { double a; double b; };
        static const struct S vals[] = {
            { 1/2.2, 0.5 },
            { 1/1.6, 0.25 },
            { 1/(2+51./256), 0.125 },
        };
        int main() {
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}
