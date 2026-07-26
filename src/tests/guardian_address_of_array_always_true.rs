use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass_with_diagnostic;

#[test]
fn test_address_of_array_always_true_warning_if() {
    run_pass_with_diagnostic(
        r#"
        void f() {
            int arr[10];
            if (arr) {}
        }
        "#,
        CompilePhase::Mir,
        "address of array 'arr' will always evaluate to 'true'",
        4,
        17,
    );
}

#[test]
fn test_address_of_array_always_true_warning_while() {
    run_pass_with_diagnostic(
        r#"
        void f() {
            int arr[10];
            while (arr) {}
        }
        "#,
        CompilePhase::Mir,
        "address of array 'arr' will always evaluate to 'true'",
        4,
        20,
    );
}

#[test]
fn test_address_of_array_always_true_warning_for() {
    run_pass_with_diagnostic(
        r#"
        void f() {
            int arr[10];
            for (; arr;) {}
        }
        "#,
        CompilePhase::Mir,
        "address of array 'arr' will always evaluate to 'true'",
        4,
        20,
    );
}

#[test]
fn test_address_of_array_always_true_warning_ternary() {
    run_pass_with_diagnostic(
        r#"
        void f() {
            int arr[10];
            int x = arr ? 1 : 0;
        }
        "#,
        CompilePhase::Mir,
        "address of array \'arr\' will always evaluate to \'true\'",
        4,
        21,
    );
}

#[test]
fn test_address_of_array_always_true_warning_logical_not() {
    run_pass_with_diagnostic(
        r#"
        void f() {
            int arr[10];
            int x = !arr;
        }
        "#,
        CompilePhase::Mir,
        "address of array 'arr' will always evaluate to 'true'",
        4,
        22,
    );
}
