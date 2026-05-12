use crate::driver::artifact::CompilePhase;
use crate::lang_options::CStandard;
use crate::tests::test_utils::*;

#[test]
fn test_c23_attribute_parsing_basic() {
    run_pass_with_std(
        r#"
        [[maybe_unused]] int x;
        [[deprecated]] void f(void);
        [[nodiscard]] int g(void) { return 42; }
        "#,
        CompilePhase::Parse,
        CStandard::C23,
    );
}

#[test]
fn test_c23_attribute_parsing_complex() {
    run_pass_with_std(
        r#"
        [[vendor::attr(1, 2, "three")]] int x;
        [[attr1, attr2]] [[attr3]] int y;
        "#,
        CompilePhase::Parse,
        CStandard::C23,
    );
}

#[test]
fn test_c23_attribute_parsing_on_statements() {
    run_pass_with_std(
        r#"
        void f(void) {
            [[maybe_unused]] int x = 0;
            [[fallthrough]];
            for (int i = 0; i < 10; ++i) [[unlikely]] {
                break;
            }
        }
        "#,
        CompilePhase::Parse,
        CStandard::C23,
    );
}

#[test]
fn test_c23_attribute_parsing_on_structs() {
    run_pass_with_std(
        r#"
        struct [[deprecated]] S {
            [[maybe_unused]] int x;
        };

        enum [[deprecated]] E {
            [[maybe_unused]] A
        };
        "#,
        CompilePhase::Parse,
        CStandard::C23,
    );
}

#[test]
fn test_c23_attribute_parsing_on_declarators() {
    run_pass_with_std(
        r#"
        int * [[attr]] ptr;
        int arr[10] [[attr]];
        void f(int x [[attr]]);
        "#,
        CompilePhase::Parse,
        CStandard::C23,
    );
}

#[test]
fn test_c23_attribute_fail_c11() {
    // Attributes are not supported in C11
    run_fail_with_message_and_std(
        "[[maybe_unused]] int x;",
        "expected declaration specifiers",
        CStandard::C11,
    );
}

#[test]
fn test_attribute_coverage() {
    run_pass_with_std(
        r#"
        int x [[attr]];
        int y __attribute__((aligned(4)));
        int z __asm__("my_z");
        
        int w __attribute__((aligned));
        
        [[attr(1+(2*3))]] int a;
        
        [[123, maybe_unused]] int b;
        int ([[maybe_unused]] x);
        
        int c __asm__(("my_c"));
        "#,
        CompilePhase::Parse,
        CStandard::C23,
    );
}
