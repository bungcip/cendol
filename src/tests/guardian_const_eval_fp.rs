use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_choose_expr_fp_const() {
    run_pass(
        r#"
        float x = __builtin_choose_expr(1, 1.5f, 2.5f);
        _Static_assert(__builtin_choose_expr(1, 1.5f, 2.5f) == 1.5f, "choose_expr float");
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_fp_const() {
    run_pass(
        r#"
        float x = _Generic(1, int: 1.5f, default: 2.5f);
        _Static_assert(_Generic(1.0, double: 1.5f, default: 2.5f) == 1.5f, "generic selection float");
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_ternary_fp_const() {
    run_pass(
        r#"
        float x = 1 ? 1.5f : 2.5f;
        _Static_assert((0 ? 1.5f : 2.5f) == 2.5f, "ternary float");
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_nested_selection_fp_const() {
    run_pass(
        r#"
        float x = __builtin_choose_expr(1, _Generic(1, int: (1 ? 1.5f : 0.0f), default: 2.5f), 3.5f);
        _Static_assert(__builtin_choose_expr(1, _Generic(1, int: (1 ? 1.5f : 0.0f), default: 2.5f), 3.5f) == 1.5f, "nested selection float");
        "#,
        CompilePhase::Mir,
    );
}
