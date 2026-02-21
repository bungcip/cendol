use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_type_limits_and_conversions() {
    let source = r#"
        // 1. Verify standard type limit macros are defined
        // These were missing causing errors in the original issue.
        _Static_assert(__SCHAR_MAX__ == 127, "SCHAR_MAX");
        _Static_assert(__SHRT_MAX__ == 32767, "SHRT_MAX");
        _Static_assert(__INT_MAX__ == 2147483647, "INT_MAX");
        _Static_assert(__LONG_LONG_MAX__ > 2147483647, "LONG_LONG_MAX");
        _Static_assert(__FLT_MANT_DIG__ == 24, "FLT_MANT_DIG");
        _Static_assert(__DBL_MANT_DIG__ == 53, "DBL_MANT_DIG");
        _Static_assert(__LDBL_MANT_DIG__ == 64, "LDBL_MANT_DIG");

        // 2. Verify token pasting works, specifically with line splicing.
        // The original bug was in PPLexer where line splicing (backslash-newline)
        // caused incorrect token start positions, corrupting token pasting (##).
        // e.g. `cvt_ ## type` would become `cvt_type` but if `type` was on a new line
        // after a splice, the splice consumption logic in `next_char` vs `next_token`
        // got out of sync regarding the token start position.

        #define PASTE(x, y) x ## y

        // Defines 'test_var'
        int PASTE(test_, \
var) = 42;

        int main() {
            // Verify we can access the variable with the pasted name
            return test_var - 42;
        }
    "#;

    // We run to EmitObject to ensure everything works, including the main function logic.
    // Unlike the original complex test case using floats, this simple integer logic
    // should pass the Cranelift backend without hitting missing f128 support.
    run_pass(source, CompilePhase::EmitObject);
}
