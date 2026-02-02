use crate::ast::NodeKind;
use crate::semantic::const_eval::{ConstEvalCtx, eval_const_expr};
use crate::tests::semantic_common::setup_lowering;

fn snapshot_const_eval_batch(name: &str, exprs: &[&str]) {
    let mut output = String::new();

    for expr in exprs {
        let source = format!("long long test_var = {};", expr);
        let (ast, mut registry, symbol_table) = setup_lowering(&source);

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
                    if let NodeKind::VarDecl(data) = ast.get_kind(decl_ref) {
                        if data.name.to_string() == "test_var" {
                            return data.init;
                        }
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

        output.push_str(&format!("Expression: {}\nResult: {}\n---\n", expr, val_str));
    }

    insta::assert_snapshot!(name, output);
}

#[test]
fn test_arithmetic() {
    snapshot_const_eval_batch("arithmetic", &["1 + 2", "10 - 5", "2 * 3", "10 / 2", "10 % 3"]);
}

#[test]
fn test_bitwise() {
    snapshot_const_eval_batch(
        "bitwise",
        &["1 << 2", "8 >> 1", "0x0F & 0xF0", "0x0F | 0xF0", "0x0F ^ 0xFF", "~0"],
    );
}

#[test]
fn test_logical() {
    snapshot_const_eval_batch("logical", &["1 && 1", "1 && 0", "1 || 0", "0 || 0", "!0", "!5"]);
}

#[test]
fn test_comparisons() {
    snapshot_const_eval_batch(
        "comparisons",
        &["1 < 2", "2 > 1", "1 <= 1", "2 >= 2", "1 == 1", "1 != 2"],
    );
}

#[test]
fn test_ternary() {
    snapshot_const_eval_batch("ternary", &["1 ? 10 : 20", "0 ? 10 : 20"]);
}

#[test]
fn test_sizeof() {
    snapshot_const_eval_batch(
        "sizeof",
        &[
            "sizeof(int)",
            "sizeof(long)",
            "sizeof(long long)",
            // "sizeof(1 + 1)", // Fails because operand type is not resolved in AST for unevaluated operands in this test setup
        ],
    );
}

#[test]
fn test_complex() {
    snapshot_const_eval_batch("complex", &["1 + 2 * 3", "(1 + 2) * 3"]);
}

#[test]
fn test_overflow_wrapping() {
    // 9223372036854775807 is LLONG_MAX (2^63 - 1)
    snapshot_const_eval_batch("overflow_wrapping", &["9223372036854775807LL + 1"]);
}

#[test]
fn test_generic_selection() {
    snapshot_const_eval_batch(
        "generic_selection",
        &[
            "_Generic(1, int: 10, default: 20)",
            "_Generic(1.0, double: 30, default: 20)",
        ],
    );
}

#[test]
fn test_enum_constants() {
    let source = "enum { A = 5, B = 10 }; int test_var = A + B;";
    let (ast, registry, symbol_table) = setup_lowering(source);

    let root = ast.get_root();
    let init_expr = if let NodeKind::TranslationUnit(tu) = ast.get_kind(root) {
        tu.decl_start
            .range(tu.decl_len)
            .find_map(|decl_ref| {
                if let NodeKind::VarDecl(data) = ast.get_kind(decl_ref) {
                    if data.name.to_string() == "test_var" {
                        return data.init;
                    }
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

    insta::assert_snapshot!("enum_constants", format!("Source: {}\nResult: {}", source, val_str));
}
