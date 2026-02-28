use crate::tests::test_utils;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_lua_ternary_comma_qualifier() {
    // We expect a type mismatch (assignment of pointer to int), but not on the condition itself!
    // Rather than just verifying it passes, we'll verify it doesn't fail on the ternary condition type mismatch.
    // So let's verify that the ternary resolves to `char*` by assigning it to a char* which shouldn't warn.
    let source_ok = r#"
        struct TString {
            int shrlen;
            char *contents;
        };

        void bar(const struct TString *ts1) {
            long rl1;
            char *a;
            // The result of the ternary should be `char *` because:
            // a is `char *`.
            // ts1->contents is `char * const` (because ts1 is const), but the comma operator
            // does lvalue-to-rvalue conversion, which strips the top-level const, making it `char *`.
            // So both sides of ternary are `char *`.
            char *s = ((ts1->shrlen >= 0) ? (((void)((rl1) = ts1->shrlen)), a) : (((void)((rl1) = ts1->shrlen)), ts1->contents));
        }
    "#;
    test_utils::run_pass(source_ok, CompilePhase::Mir);
}

#[test]
fn test_comma_lvalue_conversion() {
    let source = r#"
        void test() {
            const char * const b = 0;
            // comma operator strips top-level const, making it `const char *`
            _Static_assert(_Generic((1, b), const char *: 1, default: 0) == 1, "comma strips top-level const");
        }
    "#;
    test_utils::run_pass(source, CompilePhase::Mir);
}
