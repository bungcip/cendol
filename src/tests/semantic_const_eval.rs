use crate::ast::NodeKind;
use crate::semantic::const_eval::{ConstEvalCtx, eval_const_expr};
use crate::tests::semantic_common::setup_analysis;

fn evaluate_program(source: &str) -> String {
    let (ast, mut registry, symbol_table) = setup_analysis(source);

    // Force layout computation for types likely to be used in sizeof tests.
    let _ = registry.ensure_layout(registry.type_int);
    let _ = registry.ensure_layout(registry.type_long);
    let _ = registry.ensure_layout(registry.type_long_long);
    let _ = registry.ensure_layout(registry.type_char);
    let _ = registry.ensure_layout(registry.type_float);
    let _ = registry.ensure_layout(registry.type_double);

    let root = ast.get_root();
    let init_expr = if let NodeKind::TranslationUnit(tu) = ast.get_kind(root) {
        tu.decl_start
            .range(tu.decl_len)
            .find_map(|decl_ref| {
                if let NodeKind::VarDecl(data) = ast.get_kind(decl_ref)
                    && data.name.to_string() == "test_var"
                {
                    return data.init;
                }
                None
            })
            .expect("Could not find test_var initializer")
    } else {
        panic!("Root is not a TranslationUnit");
    };

    let ctx = ConstEvalCtx {
        ast: &ast,
        symbol_table: &symbol_table,
        registry: &registry,
        semantic_info: ast.semantic_info.as_ref(),
    };

    let result = eval_const_expr(&ctx, init_expr);
    match result {
        Some(val) => format!("{}", val),
        None => "None".to_string(),
    }
}

fn format_const_eval_batch(exprs: &[&str]) -> String {
    let mut output = String::new();

    for expr in exprs {
        let source = format!("long long test_var = {};", expr);
        let val_str = evaluate_program(&source);
        output.push_str(&format!("Expression: {}\nResult: {}\n---\n", expr, val_str));
    }

    output
}

#[test]
fn test_arithmetic() {
    let output = format_const_eval_batch(&["1 + 2", "10 - 5", "2 * 3", "10 / 2", "10 % 3"]);
    insta::assert_snapshot!(output, @r"
    Expression: 1 + 2
    Result: 3
    ---
    Expression: 10 - 5
    Result: 5
    ---
    Expression: 2 * 3
    Result: 6
    ---
    Expression: 10 / 2
    Result: 5
    ---
    Expression: 10 % 3
    Result: None
    ---
    ");
}

#[test]
fn test_bitwise() {
    let output = format_const_eval_batch(&["1 << 2", "8 >> 1", "0x0F & 0xF0", "0x0F | 0xF0", "0x0F ^ 0xFF", "~0"]);
    insta::assert_snapshot!(output, @r"
    Expression: 1 << 2
    Result: 4
    ---
    Expression: 8 >> 1
    Result: 4
    ---
    Expression: 0x0F & 0xF0
    Result: 0
    ---
    Expression: 0x0F | 0xF0
    Result: 255
    ---
    Expression: 0x0F ^ 0xFF
    Result: 240
    ---
    Expression: ~0
    Result: -1
    ---
    ");
}

#[test]
fn test_logical() {
    let output = format_const_eval_batch(&["1 && 1", "1 && 0", "1 || 0", "0 || 0", "!0", "!5"]);
    insta::assert_snapshot!(output, @r"
    Expression: 1 && 1
    Result: 1
    ---
    Expression: 1 && 0
    Result: 0
    ---
    Expression: 1 || 0
    Result: 1
    ---
    Expression: 0 || 0
    Result: 0
    ---
    Expression: !0
    Result: 1
    ---
    Expression: !5
    Result: 0
    ---
    ");
}

#[test]
fn test_comparisons() {
    let output = format_const_eval_batch(&["1 < 2", "2 > 1", "1 <= 1", "2 >= 2", "1 == 1", "1 != 2"]);
    insta::assert_snapshot!(output, @r"
    Expression: 1 < 2
    Result: 1
    ---
    Expression: 2 > 1
    Result: 1
    ---
    Expression: 1 <= 1
    Result: 1
    ---
    Expression: 2 >= 2
    Result: 1
    ---
    Expression: 1 == 1
    Result: 1
    ---
    Expression: 1 != 2
    Result: 1
    ---
    ");
}

#[test]
fn test_ternary() {
    let output = format_const_eval_batch(&["1 ? 10 : 20", "0 ? 10 : 20"]);
    insta::assert_snapshot!(output, @r"
    Expression: 1 ? 10 : 20
    Result: 10
    ---
    Expression: 0 ? 10 : 20
    Result: 20
    ---
    ");
}

#[test]
fn test_sizeof() {
    let output = format_const_eval_batch(&[
        "sizeof(int)",
        "sizeof(long)",
        "sizeof(long long)",
        // "sizeof(1 + 1)", // Fails because operand type is not resolved in AST for unevaluated operands in this test setup
    ]);
    insta::assert_snapshot!(output, @r"
    Expression: sizeof(int)
    Result: 4
    ---
    Expression: sizeof(long)
    Result: 8
    ---
    Expression: sizeof(long long)
    Result: 8
    ---
    ");
}

#[test]
fn test_complex() {
    let output = format_const_eval_batch(&["1 + 2 * 3", "(1 + 2) * 3"]);
    insta::assert_snapshot!(output, @r"
    Expression: 1 + 2 * 3
    Result: 7
    ---
    Expression: (1 + 2) * 3
    Result: 9
    ---
    ");
}

#[test]
fn test_overflow_wrapping() {
    // 9223372036854775807 is LLONG_MAX (2^63 - 1)
    let output = format_const_eval_batch(&["9223372036854775807LL + 1"]);
    insta::assert_snapshot!(output, @r"
    Expression: 9223372036854775807LL + 1
    Result: -9223372036854775808
    ---
    ");
}

#[test]
fn test_generic_selection() {
    let output = format_const_eval_batch(&[
        "_Generic(1, int: 10, default: 20)",
        "_Generic(1.0, double: 30, default: 20)",
    ]);
    insta::assert_snapshot!(output, @r"
    Expression: _Generic(1, int: 10, default: 20)
    Result: 10
    ---
    Expression: _Generic(1.0, double: 30, default: 20)
    Result: 30
    ---
    ");
}

#[test]
fn test_enum_constants() {
    let source = "enum { A = 5, B = 10 }; int test_var = A + B;";
    let val_str = evaluate_program(source);

    insta::assert_snapshot!(format!("Source: {}\nResult: {}", source, val_str), @r"
    Source: enum { A = 5, B = 10 }; int test_var = A + B;
    Result: 15
    ");
}

#[test]
fn test_sizeof_expression() {
    let output = format_const_eval_batch(&["sizeof(1 + 1)"]);
    insta::assert_snapshot!(output, @r"
    Expression: sizeof(1 + 1)
    Result: 4
    ---
    ");
}

#[test]
fn test_alignof() {
    let output = format_const_eval_batch(&["_Alignof(int)"]);
    insta::assert_snapshot!(output, @r"
    Expression: _Alignof(int)
    Result: 4
    ---
    ");
}

#[test]
fn test_logical_short_circuit_or() {
    // Should result in 1 and not divide by zero error
    let output = format_const_eval_batch(&["1 || (1 / 0)"]);
    insta::assert_snapshot!(output, @r"
    Expression: 1 || (1 / 0)
    Result: 1
    ---
    ");
}

#[test]
fn test_logical_short_circuit_and() {
    // Should result in 0 and not divide by zero error
    let output = format_const_eval_batch(&["0 && (1 / 0)"]);
    insta::assert_snapshot!(output, @r"
    Expression: 0 && (1 / 0)
    Result: 0
    ---
    ");
}
