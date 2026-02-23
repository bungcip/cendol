use crate::ast::NodeKind;
use crate::semantic::const_eval::{ConstEvalCtx, eval_const_expr};
use crate::tests::semantic_common::setup_analysis;

fn evaluate_program(source: &str) -> String {
    let (ast, registry, symbol_table) = setup_analysis(source);

    let root = ast.get_root();
    // Ensure we have a translation unit
    if !matches!(ast.get_kind(root), NodeKind::TranslationUnit(_)) {
        panic!("Root is not a TranslationUnit");
    }

    let init_expr = crate::tests::semantic_common::find_var_decl(&ast, "test_var")
        .init
        .expect("Could not find test_var initializer");

    let ctx = ConstEvalCtx {
        ast: &ast,
        symbol_table: &symbol_table,
        registry: &registry,
        semantic_info: ast.semantic_info.as_ref(),
    };

    let result = eval_const_expr(&ctx, init_expr);
    match result {
        Some(val) => format!("{}", val as u64), // Display as unsigned for clarity in this test
        None => "None".to_string(),
    }
}

fn format_const_eval_batch(exprs: &[&str]) -> String {
    let mut output = String::new();

    for expr in exprs {
        // Use unsigned long long to force unsigned context if needed, but expression type dictates it.
        // We use size_t logic: (~(unsigned long)0)
        let source = format!("unsigned long test_var = {};", expr);
        let val_str = evaluate_program(&source);
        output.push_str(&format!("Expression: {}\nResult: {}\n---\n", expr, val_str));
    }

    output
}

#[test]
fn test_unsigned_division() {
    // MAX_SIZET is 18446744073709551615 (2^64 - 1).
    // As i64, it is -1.
    // -1 / 9 = 0.
    // 18446744073709551615 / 9 = 2049638230412172401.
    let exprs = &[
        "(unsigned long)(~(unsigned long)0) / 9",
        "(unsigned long)-1 / 9",
        "((unsigned long)1 << 63) / 2", // 2^63 / 2 = 2^62
    ];
    let output = format_const_eval_batch(exprs);
    insta::assert_snapshot!(output, @"
    Expression: (unsigned long)(~(unsigned long)0) / 9
    Result: 2049638230412172401
    ---
    Expression: (unsigned long)-1 / 9
    Result: 2049638230412172401
    ---
    Expression: ((unsigned long)1 << 63) / 2
    Result: 4611686018427387904
    ---
    ");
}

#[test]
fn test_unsigned_comparisons() {
    // -1 < 1 (signed) is true.
    // (unsigned)-1 < 1 is false (MAX < 1).
    let exprs = &[
        "(unsigned long)-1 < 1",
        "(unsigned long)-1 > 1",
    ];
    let output = format_const_eval_batch(exprs);
    // Result 0 means false, 1 means true.
    insta::assert_snapshot!(output, @"
    Expression: (unsigned long)-1 < 1
    Result: 0
    ---
    Expression: (unsigned long)-1 > 1
    Result: 1
    ---
    ");
}
