use crate::tests::test_utils::check_diagnostic_message_only;
use crate::tests::test_utils::run_pass;

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

#[test]
fn test_integer_promotion_bitfield_wider_than_int() {
    let source = r#"
        #define IS_LONG_LONG(x) _Generic((x), long long: 1, default: 0)
        #define IS_ULONG_LONG(x) _Generic((x), unsigned long long: 1, default: 0)
        struct S {
            long long llf : 40;
            unsigned long long ullf : 40;
        };
        int main() {
            struct S s;
            // llf is promoted to long long (since it is wider than int)
            _Static_assert(IS_LONG_LONG(s.llf + 0), "");
            // ullf is promoted to unsigned long long (since it is wider than int)
            _Static_assert(IS_ULONG_LONG(s.ullf + 0), "");
            return 0;
        }
    "#;
    let (_, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());
}

#[test]
fn test_usual_arithmetic_conversions_coverage() {
    let source = r#"
        void test() {
            int a = 1;
            unsigned long long b = 2;
            typeof(a + b) c;

            // Cover integer_promotion where qt is an enum (line 74)
            enum E { A, B } e = A;
            typeof(+e) f;

            // Cover integer_promotion where qt rank < int (line 77)
            short s = 1;
            typeof(+s) g;

            // Cover default argument promotions
            void f_decl();
            float my_float = 1.0f;
            f_decl(my_float);

            char c_arg = 'a';
            f_decl(c_arg);
        }
    "#;
    let (_, result) = run_pipeline(source, CompilePhase::SemanticLowering);
    assert!(result.is_ok());
}

#[test]
fn test_pointer_level_and_type_warnings() {
    // --- test_different_pointer_levels_warning ---
    let source = r#"
        void test(void) {
            int x;
            int *y = 0;
            int *a = &x;
            const int *b = &y;
        }
    "#;
    let driver = run_pass(source, CompilePhase::Mir);
    check_diagnostic_message_only(
        &driver,
        "incompatible pointer types passing 'int**' to parameter of type 'const int*'",
    );
    // --- test_incompatible_pointer_warning_function_call ---
    let source = r#"
        void f(int *i) {
        }
        void test(void) {
            double *d;
            f(d);
        }
    "#;
    let driver = run_pass(source, CompilePhase::Mir);
    check_diagnostic_message_only(
        &driver,
        "incompatible pointer types passing 'double*' to parameter of type 'int*'",
    );
}
