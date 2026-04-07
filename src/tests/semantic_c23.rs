use crate::driver::artifact::CompilePhase;
use crate::lang_options::CStandard;
use crate::tests::test_utils::*;

#[test]
fn test_c23_char8_t_and_utf8_literal() {
    run_pass_with_std(
        r#"
        typedef unsigned char char8_t;
        int main() {
            char8_t c = u8'a';
            return 0;
        }
        "#,
        CompilePhase::Mir,
        CStandard::C23,
    );
}

#[test]
fn test_c23_auto_basic() {
    run_pass_with_std(
        r#"
        int main() {
            auto x = 1;
            auto y = 1.0;
            const auto z = 'a';
            static auto s = 42;

            int* px = &x;
            double* py = &y;
            const int* pz = &z;
            int* ps = &s;
            return 0;
        }
        "#,
        CompilePhase::Mir,
        CStandard::C23,
    );
}

#[test]
fn test_c23_constexpr() {
    run_pass_with_std(
        r#"
        constexpr int a = 42;
        static constexpr int b = 100;

        int main() {
            constexpr int c = 5;
            static constexpr int d = 10;
            return a + b + c + d;
        }
        "#,
        CompilePhase::Mir,
        CStandard::C23,
    );

    run_fail_with_message_and_std(
        r#"
        constexpr int a;
        "#,
        "constexpr requires an initialized data declaration",
        CStandard::C23,
    );

    run_fail_with_message_and_std(
        r#"
        int main() {
            constexpr int a = 5;
            a = 10;
        }
        "#,
        "cannot assign to read-only location",
        CStandard::C23,
    );

    run_fail_with_message_and_std(
        r#"
        extern constexpr int a = 5;
        "#,
        "conflicting storage class",
        CStandard::C23,
    );
}

#[test]
fn test_c23_auto_fail_c11() {
    // In C11, auto is only a storage class and requires a type specifier
    run_fail_with_message_and_std(
        r#"
        void test() {
            auto x = 1;
        }
        "#,
        "missing type specifier",
        CStandard::C11,
    );
}

#[test]
fn test_c23_keywords() {
    run_pass_with_std(
        r#"
        int main() {
            bool b = true;
            b = false;

            _Alignas(8) int x;
            alignas(8) int y;

            int sz1 = _Alignof(int);
            int sz2 = alignof(int);

            static _Thread_local int t1;
            static thread_local int t2;

            constexpr int c = 42;

            typeof(int) a = 1;

            return 0;
        }
        "#,
        CompilePhase::Mir,
        CStandard::C23,
    );
}

#[test]
fn test_c23_auto_multi_declarator() {
    run_pass_with_std(
        r#"
        void test() {
            auto x = 1, y = 2;
            int *px = &x, *py = &y;
        }
        "#,
        CompilePhase::Mir,
        CStandard::C23,
    );

    run_fail_with_message_and_std(
        r#"
        void test() {
            auto x = 1, y = 1.0;
        }
        "#,
        "deduced as 'int' for one declarator, but 'double' for another",
        CStandard::C23,
    );
}

#[test]
fn test_c23_string_literals() {
    run_pass_with_std(
        r#"
        int main() {
            const unsigned char* s1 = u8"hello";
            const unsigned short* s2 = u"world";
            const unsigned int* s3 = U"foo";
            return 0;
        }
        "#,
        CompilePhase::Mir,
        CStandard::C23,
    );
}

#[test]
fn test_c23_auto_invalid_contexts() {
    run_fail_with_message_and_std(
        r#"
        typedef auto auto_int;
        "#,
        "conflicting storage class",
        CStandard::C23,
    );

    run_fail_with_message_and_std(
        r#"
        struct S {
            auto x;
        };
        "#,
        "not allowed in struct or union member",
        CStandard::C23,
    );
}
