use crate::ast::NodeKind;
use crate::semantic::const_eval::{ConstEvalCtx, eval_const_expr};
use crate::tests::semantic_common::setup_analysis;

fn snapshot_const_eval(name: &str, expr: &str) {
    let source = format!("long long test_var = {};", expr);
    let (ast, mut registry, symbol_table) = setup_analysis(&source);

    // Ensure layouts
    let _ = registry.ensure_layout(registry.type_int);
    let _ = registry.ensure_layout(registry.type_long_long);

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
    let val_str = match result {
        Some(val) => format!("{}", val),
        None => "None".to_string(),
    };

    insta::assert_snapshot!(name, format!("Expression: {}\nResult: {}", expr, val_str));
}

#[test]
fn test_sizeof_expression() {
    snapshot_const_eval("sizeof_expr_arithmetic", "sizeof(1 + 1)");
}

#[test]
fn test_alignof() {
    snapshot_const_eval("alignof_int", "_Alignof(int)");
}

#[test]
fn test_logical_short_circuit_or() {
    snapshot_const_eval("short_circuit_or", "1 || (1 / 0)");
}

#[test]
fn test_logical_short_circuit_and() {
    snapshot_const_eval("short_circuit_and", "0 && (1 / 0)");
}
