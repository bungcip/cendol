use crate::tests::test_utils::{run_fail_with_message, run_pipeline};

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
    let _ = run_pipeline(source, crate::driver::artifact::CompilePhase::SemanticLowering);
}

#[test]
fn test_c23_nullptr_invalid_conversions() {
    let source = r#"
        void test() {
            int x = nullptr;
        }
    "#;
    run_fail_with_message(source, "type mismatch");
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
    let _ = run_pipeline(source, crate::driver::artifact::CompilePhase::SemanticLowering);
}
