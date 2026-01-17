//! Semantic validation tests for lvalue constraints.
use crate::tests::semantic_common::setup_diagnostics_output;

#[test]
fn test_assign_to_literal() {
    let source = r#"
        int main() {
            1 = 2;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_assign_to_arithmetic_expr() {
    let source = r#"
        int main() {
            int x;
            x + 1 = 5;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_pre_increment_literal() {
    let source = r#"
        int main() {
            ++1;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_post_increment_literal() {
    let source = r#"
        int main() {
            1++;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_pre_decrement_rvalue() {
    let source = r#"
        int main() {
            int x, y;
            --(x + y);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_post_decrement_rvalue() {
    let source = r#"
        int main() {
            int x, y;
            (x + y)--;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_address_of_rvalue() {
    let source = r#"
        int main() {
            int x;
            &(x + 1);
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}

#[test]
fn test_assign_to_struct_rvalue_member() {
    let source = r#"
        struct S { int x; };
        struct S f() { struct S s; return s; }
        int main() {
            f().x = 1;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
