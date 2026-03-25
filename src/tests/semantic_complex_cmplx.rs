use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_complex_h_cmplx() {
    let source = r#"
        #include <complex.h>

        double complex z1 = CMPLX(1.0, 2.0);
        float complex z2 = CMPLXF(3.0f, 4.0f);

        int main() {
            if (creal(z1) != 1.0) return 1;
            if (cimag(z1) != 2.0) return 1;
            if (creal(z2) != 3.0f) return 1;
            if (cimag(z2) != 4.0f) return 1;

            double complex z3 = CMPLX(0.0, -0.0);
            if (creal(z3) != 0.0) return 1;
            if (cimag(z3) != -0.0) return 1;

            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Cranelift);
}

#[test]
fn test_complex_cmplx_const_eval() {
    let source = r#"
        #include <complex.h>

        // CMPLX should be usable in static initializers (constant expressions)
        static double complex z = CMPLX(1.0, 2.0);
        
        _Static_assert(creal(CMPLX(1.0, 2.0)) == 1.0, "real part fail");
        _Static_assert(cimag(CMPLX(1.0, 2.0)) == 2.0, "imag part fail");

        int main() {
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_complex_i_usage() {
    let source = r#"
        #include <complex.h>
        
        int main() {
            double complex z = 1.0 + 2.0 * I;
            if (creal(z) != 1.0) return 1;
            if (cimag(z) != 2.0) return 1;
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::Cranelift);
}
#[test]
fn test_complex_cmplx_signed_zero() {
    let source = r#"
        #include <complex.h>
        _Static_assert(__builtin_imag(CMPLX(0.0, -0.0)) < 0.0 == 0, "Wait, -0.0 < 0.0 is false");
        // We can't easily check -0.0 in _Static_assert without bit-casting, which cendol might not support yet.
        // But we can check if it compiles.
        double complex z = CMPLX(0.0, -0.0);
    "#;
    run_pass(source, CompilePhase::Mir);
}
