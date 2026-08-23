use crate::tests::test_utils::{run_fail_with_message, run_pedantic_fail_with_message};

#[test]
fn test_return_constraints() {
    // 1. void function returning a void expression (should emit VoidReturnWithVoidExpr warning)
    run_pedantic_fail_with_message(r#"
        void foo(void) {}
        void bar(void) {
            return foo();
        }
    "#, "void function 'bar' should not return a value");

    // 2. void function returning a non-void expression (should emit VoidReturnWithValue error)
    run_fail_with_message(r#"
        void bar(void) {
            return 42;
        }
    "#, "void function 'bar' should not return a value");

    // 3. non-void function without a return value (should emit NonVoidReturnWithoutValue error)
    run_fail_with_message(r#"
        int bar(void) {
            return;
        }
    "#, "non-void function 'bar' should return a value");
}
