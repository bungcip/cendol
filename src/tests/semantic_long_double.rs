use crate::tests::test_utils::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_long_double_mant_dig() {
    run_pass(
        r#"
        #include <float.h>
        _Static_assert(LDBL_MANT_DIG == 64, "LDBL_MANT_DIG should be 64");
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_long_double_size_align() {
    run_pass(
        r#"
        _Static_assert(sizeof(long double) == 16, "sizeof(long double) should be 16");
        _Static_assert(_Alignof(long double) == 16, "_Alignof(long double) should be 16");
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_long_double_characteristic_macros() {
    run_pass(
        r#"
        #include <float.h>
        _Static_assert(FLT_RADIX == 2, "FLT_RADIX");
        _Static_assert(DBL_MANT_DIG == 53, "DBL_MANT_DIG");
        _Static_assert(LDBL_MANT_DIG == 64, "LDBL_MANT_DIG");
        _Static_assert(LDBL_DIG == 18, "LDBL_DIG");
        _Static_assert(LDBL_MIN_EXP == -16381, "LDBL_MIN_EXP");
        _Static_assert(LDBL_MAX_EXP == 16384, "LDBL_MAX_EXP");
        _Static_assert(LDBL_MIN_10_EXP == -4931, "LDBL_MIN_10_EXP");
        _Static_assert(LDBL_MAX_10_EXP == 4932, "LDBL_MAX_10_EXP");
        int main() {
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_long_double_assignment_lowering() {
    // Basic test to ensure long double assignment doesn't crash the compiler
    run_pass(
        r#"
        int main() {
            long double a = 1.0L;
            long double b = a;
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}
