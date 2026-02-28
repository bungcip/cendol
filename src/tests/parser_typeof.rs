use super::parser_utils::setup_declaration;

#[test]
fn test_typeof_expr() {
    let decl = setup_declaration("typeof(5 + 3) x;");
    insta::assert_yaml_snapshot!("typeof_expr", decl);
}

#[test]
fn test_typeof_type() {
    let decl = setup_declaration("typeof(int) x;");
    insta::assert_yaml_snapshot!("typeof_type", decl);
}

#[test]
fn test_typeof_comma_expr() {
    let decl = setup_declaration("typeof((void)0, 5) x;");
    insta::assert_yaml_snapshot!("typeof_comma_expr", decl);
}
