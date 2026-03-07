use crate::tests::test_utils::run_pipeline_to_mir;

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
