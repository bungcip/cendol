use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_array_init_excess_elements() {
    // int a[2] = {1, 2, 3} -> Error: 3 elements in array of 2
    run_fail_with_message(
        r#"
        int main(void) {
            int a[2] = {1, 2, 3};
            return 0;
        }
        "#,
        "excess elements in array initializer",
    );
}

#[test]
fn test_array_init_exact_elements() {
    // int a[3] = {1, 2, 3} -> OK
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
    // int a[4] = {1, 2} -> OK
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
    // int a[3] = {1, [0] = 5, 2, 3} -> Error, because after [0]=5, index is 0,
    // then 2 goes to index 1, 3 goes to index 2. Total items 4, but max index reached is 2
    // Wait, if it resets, the final item goes to index 2.
    // 1 -> index 0
    // [0] = 5 -> index 0
    // 2 -> index 1
    // 3 -> index 2
    // So current_index reaches 3 at the end. But does it exceed? No, max_index=3.
    // So this is valid!
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
    // int a[3] = {1, [2] = 5, 2} -> Error, 2 goes to index 3 which is out of bounds
    run_fail_with_message(
        r#"
        int main(void) {
            int a[3] = {1, [2] = 5, 2};
            return 0;
        }
        "#,
        "excess elements in array initializer",
    );
}
