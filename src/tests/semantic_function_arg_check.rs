use crate::tests::test_utils::*;

#[test]
fn test_array_argument_to_int_parameter() {
    let source = r#"
        void takes_int(int x) { (void)x; }
        void test() {
            int arr[10];
            takes_int(arr);
        }
    "#;
    let driver = run_fail(source, crate::driver::artifact::CompilePhase::Mir);
    check_diagnostic_message_only(&driver, "expected int, found int*");
}

#[test]
fn test_struct_argument_to_int_parameter() {
    let source = r#"
        struct S { int x; };
        void takes_int(int x) { (void)x; }
        void test() {
            struct S s;
            takes_int(s);
        }
    "#;
    let driver = run_fail(source, crate::driver::artifact::CompilePhase::Mir);
    check_diagnostic_message_only(&driver, "expected int, found struct S");
}

#[test]
fn test_pointer_argument_to_int_parameter() {
    let source = r#"
        void takes_int(int x) { (void)x; }
        void test() {
            int *ptr;
            takes_int(ptr);
        }
    "#;
    let driver = run_fail(source, crate::driver::artifact::CompilePhase::Mir);
    check_diagnostic_message_only(&driver, "expected int, found int*");
}
