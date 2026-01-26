use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::*;

#[test]
fn test_func_identifier_basic() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            printf("%s", __func__);
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_in_main() {
    let source = r#"
        int printf(const char *, ...);
        int main() {
            printf("%s", __func__);
            return 0;
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_type() {
    let source = r#"
        void foo() {
            // __func__ is static const char[]
            // so it decays to const char*
            const char *p = __func__;
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_redefinition() {
    let source = r#"
        void foo() {
            int __func__;
        }
    "#;
    // Shadows implicitly declared __func__
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_func_identifier_nested_scope() {
    let source = r#"
        int printf(const char *, ...);
        void foo() {
            {
                 // Should access outer __func__
                 printf("%s", __func__);
            }
        }
    "#;
    run_pass(source, CompilePhase::SemanticLowering);
}
