use super::codegen_common::run_c_code_with_output;
use crate::tests::test_utils::run_pipeline_to_mir;

#[test]
fn test_nameless_bitfield_init_repro_output() {
    let code = r#"
        int printf(const char *format, ...);
        struct S {
            int f0;
            unsigned : 1;
            int f1;
            int f2;
        } g = {1, 2, 3};

        int main() {
            printf("%d %d %d", g.f0, g.f1, g.f2);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1 2 3");
}

#[test]
fn test_complex_bitfield_init_shift() {
    // This mirrors the reported issue where a nameless bit-field caused a shift
    let code = r#"
        int printf(const char *format, ...);
        struct {
          int f0;
          int f1;
          int f2;
          int f3;
          unsigned : 0;
          int f4;
          unsigned f5;
          unsigned short f6;
          long long f7;
        } g = {0, 1, 2, 3, 4, 5, 6, 7};

        int main() {
            // If the nameless bit-field :0 is correctly skipped:
            // 0 -> f0
            // 1 -> f1
            // 2 -> f2
            // 3 -> f3
            // (skip :0)
            // 4 -> f4
            // 5 -> f5
            // 6 -> f6
            // 7 -> f7
            printf("%d %d %d %d %d %u %hu %lld", g.f0, g.f1, g.f2, g.f3, g.f4, g.f5, g.f6, g.f7);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "0 1 2 3 4 5 6 7");
}

#[test]
fn test_bitfield_promotion() {
    let src = r#"
        #define IS_INT(x) _Generic((x), int: 1, default: 0)

        int main() {
            struct { unsigned b : 3; } s = {0};
            
            // Unsigned bit-field of width 3 should be promoted to 'int' since it can
            // represent all values of the bit-field (0-7).
            _Static_assert(IS_INT(~s.b), "~s.b should be promoted to int");
            _Static_assert(IS_INT(~({s.b;})), "~({s.b;}) should be promoted to int");
            _Static_assert(IS_INT(~(s.b)), "~(s.b) should be promoted to int");
            _Static_assert(IS_INT(~({(s.b);})), "~({(s.b);}) should be promoted to int");

            return 0;
        }
    "#;
    run_pipeline_to_mir(src);
}

#[test]
fn test_bitfield_promotion_unsigned() {
    let src = r#"
        #define IS_UINT(x) _Generic((x), unsigned int: 1, default: 0)

        int main() {
            // 32-bit unsigned bit-field cannot fit in (32-bit) signed int.
            struct { unsigned b : 32; } s = {0};
            
            _Static_assert(IS_UINT(~s.b), "~s.b (32-bit) should be promoted to unsigned int");
            
            return 0;
        }
    "#;
    run_pipeline_to_mir(src);
}
