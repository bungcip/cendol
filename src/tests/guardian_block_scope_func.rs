use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_block_scope_extern_func_call() {
    let code = r#"
        int main() {
            extern void f(void);
            f(); // Triggers lazy MIR declaration
            return 0;
        }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_block_scope_static_func_prohibited() {
    let code = r#"
        int main() {
            static void f(void);
            return 0;
        }
    "#;
    run_fail_with_message(code, "invalid storage class 'static' for function 'f'");
}

#[test]
fn test_block_scope_static_func_def_prohibited() {
    let code = r#"
        int main() {
            static void f(void) {}
            return 0;
        }
    "#;
    // The parser might catch this as "Unexpected token: expected ;, found {"
    // Or the semantic analyzer will catch it.
    // In our current implementation, the parser correctly flags it:
    run_fail_with_message(code, "expected ;, found {");
}

#[test]
fn test_block_scope_extern_func_usage() {
    let code = r#"
        int main() {
            extern int f(int);
            int (*p)(int) = f;
            return 0;
        }
    "#;
    run_pass(code, CompilePhase::Mir);
}
