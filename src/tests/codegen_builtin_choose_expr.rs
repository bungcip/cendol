use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_codegen_choose_expr() {
    let status = run_c_code_exit_status(
        r#"
        int main() {
            int x = __builtin_choose_expr(1, 10, 20);
            int y = __builtin_choose_expr(0, 10, 20);
            if (x == 10 && y == 20) return 0;
            return 1;
        }
        "#,
    );
    assert_eq!(status, 0);
}

#[test]
fn test_codegen_choose_expr_side_effects() {
    let status = run_c_code_exit_status(
        r#"
        int count = 0;
        int inc() { count++; return 1; }
        int main() {
            int x = __builtin_choose_expr(1, 10, inc());
            if (x == 10 && count == 0) return 0;
            return 1;
        }
        "#,
    );
    assert_eq!(status, 0);
}

#[test]
fn test_codegen_choose_expr_lvalue() {
    let status = run_c_code_exit_status(
        r#"
        int main() {
            int a = 1, b = 2;
            __builtin_choose_expr(1, a, b) = 10;
            __builtin_choose_expr(0, a, b) = 20;
            if (a == 10 && b == 20) return 0;
            return 1;
        }
        "#,
    );
    assert_eq!(status, 0);
}
