use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

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
