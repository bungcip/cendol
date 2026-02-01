use crate::tests::test_utils::run_pipeline_to_mir;

#[test]
fn test_unary_promotion_small_types() {
    let src = r#"
        #define IS_INT(x) _Generic((x), int: 1, default: 0)

        void test() {
            unsigned short us = 1;
            short s = 1;
            unsigned char uc = 1;
            signed char sc = 1;
            char c = 1;

            // Unary + should promote to int
            _Static_assert(IS_INT(+us), "+unsigned short should be int");
            _Static_assert(IS_INT(+s), "+short should be int");
            _Static_assert(IS_INT(+uc), "+unsigned char should be int");
            _Static_assert(IS_INT(+sc), "+signed char should be int");
            _Static_assert(IS_INT(+c), "+char should be int");

            // Unary - should promote to int
            _Static_assert(IS_INT(-us), "-unsigned short should be int");
            _Static_assert(IS_INT(-s), "-short should be int");
            _Static_assert(IS_INT(-uc), "-unsigned char should be int");
            _Static_assert(IS_INT(-sc), "-signed char should be int");
            _Static_assert(IS_INT(-c), "-char should be int");
        }
    "#;
    run_pipeline_to_mir(src);
}

#[test]
fn test_unary_promotion_no_promote() {
    let src = r#"
        #define IS_LONG(x) _Generic((x), long: 1, default: 0)
        #define IS_ULONG(x) _Generic((x), unsigned long: 1, default: 0)
        #define IS_LLONG(x) _Generic((x), long long: 1, default: 0)

        void test() {
            long l = 1;
            unsigned long ul = 1;
            long long ll = 1;

            // Unary + should preserve larger types (but strip qualifiers if any)
            _Static_assert(IS_LONG(+l), "+long should be long");
            _Static_assert(IS_ULONG(+ul), "+unsigned long should be unsigned long");
            _Static_assert(IS_LLONG(+ll), "+long long should be long long");

            _Static_assert(IS_LONG(-l), "-long should be long");
            _Static_assert(IS_ULONG(-ul), "-unsigned long should be unsigned long");
        }
    "#;
    run_pipeline_to_mir(src);
}
