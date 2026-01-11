//! Semantic validation tests for lvalue constraints.
use super::semantic_common::{check_diagnostic, run_fail};
use crate::driver::artifact::CompilePhase;

fn run_lvalue_test(source: &str, expected_line: u32, expected_col: u32) {
    let driver = run_fail(source, CompilePhase::Mir);
    check_diagnostic(
        &driver,
        "Expression is not assignable (not an lvalue)",
        expected_line,
        expected_col,
    );
}

#[test]
fn rejects_invalid_lvalue_assignments() {
    // Assignment to a literal
    run_lvalue_test(
        r#"
        int main() {
            1 = 2;
        }
    "#,
        3,
        13,
    );

    // Assignment to an arithmetic expression
    run_lvalue_test(
        r#"
        int main() {
            int x;
            x + 1 = 5;
        }
    "#,
        4,
        13,
    );

    // Pre-increment on a literal
    run_lvalue_test(
        r#"
        int main() {
            ++1;
        }
    "#,
        3,
        13,
    );

    // Post-increment on a literal
    run_lvalue_test(
        r#"
        int main() {
            1++;
        }
    "#,
        3,
        13,
    );

    // Pre-decrement on an rvalue
    run_lvalue_test(
        r#"
        int main() {
            int x, y;
            --(x + y);
        }
    "#,
        4,
        13,
    );

    // Post-decrement on an rvalue
    run_lvalue_test(
        r#"
        int main() {
            int x, y;
            (x + y)--;
        }
    "#,
        4,
        14,
    );

    // Address-of operator on rvalue
    run_lvalue_test(
        r#"
        int main() {
            int x;
            &(x + 1);
        }
    "#,
        4,
        13,
    );

    // Assignment to a member of a struct returned by value (rvalue)
    run_lvalue_test(
        r#"
        struct S { int x; };
        struct S f() { struct S s; return s; }
        int main() {
            f().x = 1;
        }
    "#,
        5,
        13,
    );

    // Assignment to a function identifier (which is a non-modifiable lvalue)
    let driver = run_fail(
        r#"
        void my_func() {}
        int main() {
            my_func = 1;
        }
    "#,
        CompilePhase::Mir,
    );
    check_diagnostic(
        &driver,
        "Expression is not assignable (lvalue is a function)",
        4,
        13,
    );
}
