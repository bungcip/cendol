use super::semantic_common::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_array_completion_composite() {
    run_pass(
        r#"
        extern int a[];
        int a[10];
        int main() {
            return sizeof(a) - 10 * sizeof(int);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_array_of_pointers_composite() {
    run_pass(
        r#"
        extern int *a[];
        extern int *a[10];
        int main() {
            return sizeof(a) - 10 * sizeof(int*);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_conflicting_array_composite() {
    use super::semantic_common::run_fail_with_message;
    run_fail_with_message(
        r#"
        extern int a[5];
        extern int a[10];
        "#,
        CompilePhase::SemanticLowering,
        "conflicting types",
    );
}

#[test]
fn test_array_completion_reverse() {
    run_pass(
        r#"
        int a[10];
        extern int a[];
        int main() {
            return sizeof(a) - 10 * sizeof(int);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_function_composite_type() {
    run_pass(
        r#"
        int f(int a[]);
        int f(int a[5]) {
            return 0;
        }
        int main() {
            return f(0);
        }
        "#,
        CompilePhase::Mir,
    );
}
