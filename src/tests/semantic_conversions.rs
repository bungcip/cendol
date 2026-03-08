use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pipeline;

#[test]
fn test_complex_type_conversions() {
    let source = r#"
        int main() {
            _Complex double cd;
            double d = 1.0;
            cd + d;
            return 0;
        }
    "#;
    let (_, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());
}

#[test]
fn test_integer_promotion_bitfield() {
    let source = r#"
        #define IS_INT(x) _Generic((x), int: 1, default: 0)
        #define IS_UINT(x) _Generic((x), unsigned int: 1, default: 0)
        struct S {
            int sf : 31;
            unsigned int uf : 31;
            unsigned int uf_large : 32;
        };
        int main() {
            struct S s;
            // sf fits in int
            _Static_assert(IS_INT(s.sf + 0), "");
            // uf fits in int
            _Static_assert(IS_INT(s.uf + 0), "");
            // uf_large does not fit in int
            _Static_assert(IS_UINT(s.uf_large + 0), "");
            return 0;
        }
    "#;
    let (_, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());
}
