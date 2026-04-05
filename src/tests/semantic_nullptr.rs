use crate::lang_options::CStandard;
use crate::tests::test_utils::{run_fail_with_message_and_std, run_pass_with_std};

#[test]
fn test_c23_nullptr() {
    let source = r#"
        void test() {
            typeof(nullptr) nt;
            void *p = nullptr;
            int *q = nullptr;
            _Bool b = nullptr; // nullptr converts to bool (false)
            if (nullptr) {}    // acts as boolean false
        }
    "#;
    run_pass_with_std(
        source,
        crate::driver::artifact::CompilePhase::SemanticLowering,
        CStandard::C23,
    );
}

#[test]
fn test_c23_nullptr_invalid_conversions() {
    let source = r#"
        void test() {
            int x = nullptr;
        }
    "#;
    run_fail_with_message_and_std(source, "type mismatch", CStandard::C23);
}

#[test]
fn test_c23_nullptr_comparison() {
    let source = r#"
        void test() {
            int *p = nullptr;
            if (p == nullptr) {}
            if (nullptr == p) {}
            if (nullptr == nullptr) {}

            // nullptr isn't directly compatible with an integer, but it's a null pointer constant
            if (0 == nullptr) {}
        }
    "#;
    run_pass_with_std(
        source,
        crate::driver::artifact::CompilePhase::SemanticLowering,
        CStandard::C23,
    );
}
