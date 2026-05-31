use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_mixed_sign_comparison_long_long() {
    // This tests the case where 'unsigned long' (u64) is compared with 'long long' (i64).
    // The C11 rule for mixed signedness with rank(st) > rank(ut) is:
    // If st can represent all values of ut, st wins.
    // Otherwise, both to unsigned version of st.
    // On x86-64, rank(LL) = 6, rank(UL) = 5. Sizes are both 64 bits.
    // So 'unsigned long long' should win.
    let source = r#"
        #include <stdint.h>
        int main() {
            uint64_t u = 0xFFFFFFFFFFFFFFFBULL; // -5 if signed
            int64_t s = 1LL;
            if (u < s) return 1; // Fails if signed comparison
            return 0; // Passes if unsigned comparison
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_mixed_sign_comparison_int_long() {
    // On x86-64, rank(Long) = 5, rank(UInt) = 4.
    // sizeof(Long) = 8, sizeof(UInt) = 4.
    // Signed long (st) can represent all values of unsigned int (ut).
    // So common type should be 'long' (signed!).
    let source = r#"
        #include <stdint.h>
        int main() {
            uint32_t u = 0xFFFFFFFFU; 
            int64_t s = 1LL;
            if (u < s) return 1; 
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
