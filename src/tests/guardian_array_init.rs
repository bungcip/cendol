use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass, run_pass_with_diagnostic_message};

#[test]
fn test_array_init_excess_elements() {
    run_pass_with_diagnostic_message(
        r#"
        int main(void) {
            int a[2] = {1, 2, 3};
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "excess elements in array initializer",
    );
}

#[test]
fn test_array_init_exact_elements() {
    run_pass(
        r#"
        int main(void) {
            int a[3] = {1, 2, 3};
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_array_init_fewer_elements() {
    run_pass(
        r#"
        int main(void) {
            int a[4] = {1, 2};
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_array_init_designator_reset() {
    run_pass(
        r#"
        int main(void) {
            int a[3] = {1, [0] = 5, 2, 3};
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_array_init_designator_excess() {
    run_pass_with_diagnostic_message(
        r#"
        int main(void) {
            int a[3] = {1, [2] = 5, 2};
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "excess elements in array initializer",
    );
}

#[test]
fn test_string_init_excess_chars() {
    // C11 §6.7.9p14: the number of characters in the string literal
    // (excluding the null) shall not exceed the number of elements in the array.
    run_pass_with_diagnostic_message(
        r#"
        int main(void) {
            char s[2] = "abc";
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "excess elements in array initializer",
    );
}

#[test]
fn test_string_init_exact_fit_no_null() {
    // C11 §6.7.9p14: char s[3] = "abc" is valid (null terminator dropped)
    run_pass(
        r#"
        int main(void) {
            char s[3] = "abc";
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_string_init_with_room() {
    // char s[10] = "abc" → valid, plenty of room
    run_pass(
        r#"
        int main(void) {
            char s[10] = "abc";
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_array_init_designator_exceeds_bounds() {
    run_fail_with_message(
        r#"
        int main(void) {
            int a[2] = {[3] = 1};
            return 0;
        }
        "#,
        "array index in initializer exceeds array bounds",
    );
}
