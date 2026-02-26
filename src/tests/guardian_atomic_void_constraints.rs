use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_atomic_specifier_on_void_prohibited() {
    // C11 6.7.2.4p3: The type-name in the _Atomic(type-name) specifier shall designate
    // an object type ... (void is NOT an object type)
    run_fail_with_message(
        "typedef _Atomic(void) av;",
        "_Atomic(type-name) specifier cannot be used with void type",
    );
}

#[test]
fn test_atomic_qualifier_on_void_prohibited() {
    // C11 6.7.3p5: The _Atomic qualifier shall be applied only to an object type ...
    run_fail_with_message("_Atomic void *p;", "_Atomic qualifier cannot be used with void type");
}
