use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_pass};

#[test]
fn test_string_init_excess_chars() {
    // C11 §6.7.9p14: the number of characters in the string literal
    // (excluding the null) shall not exceed the number of elements in the array.
    // char s[2] = "abc" → error: 3 chars > 2 elements
    run_fail_with_diagnostic(
        r#"
        int main(void) {
            char s[2] = "abc";
            return 0;
        }
        "#,
        CompilePhase::Mir,
        "excess elements in array initializer",
        3,
        25,
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
