use crate::tests::parser_utils::setup_expr;

#[test]
fn test_builtin_convertvector() {
    let resolved = setup_expr("__builtin_convertvector(expr, int)");
    insta::assert_yaml_snapshot!(&resolved, @"
    FunctionCall:
      - Ident: __builtin_convertvector
      - - Ident: expr
        - Ident: type_1
    ");
}
