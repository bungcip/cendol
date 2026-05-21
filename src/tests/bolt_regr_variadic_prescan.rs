use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_variadic_prescan_regression() {
    let source = "
#define EXPAND(x) x x
#define VAR(x, ...) x, __VA_ARGS__
VAR(EXPAND(a), EXPAND(b), EXPAND(c))
";
    // Expected: EXPAND(a) expands, EXPAND(b) expands, EXPAND(c) expands.
    // result: a a , b b , c c
    let tokens = setup_pp_snapshot(source);
    let result: Vec<String> = tokens.iter().map(|t| t.text.clone()).collect();
    let result_str = result.join(" ");
    assert_eq!(result_str, "a a , b b , c c");
}

#[test]
fn test_variadic_prescan_regression_2() {
    let source = "
#define EXPAND(x) x x
#define VAR(...) __VA_ARGS__
VAR(EXPAND(a), EXPAND(b))
";
    let tokens = setup_pp_snapshot(source);
    let result: Vec<String> = tokens.iter().map(|t| t.text.clone()).collect();
    let result_str = result.join(" ");
    assert_eq!(result_str, "a a , b b");
}
