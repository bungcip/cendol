use super::parser_utils::setup_declaration;

#[test]
fn test_typeof_expr() {
    let decl = setup_declaration("typeof(5 + 3) x;");
    insta::assert_yaml_snapshot!(decl, @r"
    Declaration:
      specifiers:
        - TypeofExpr(4)
      init_declarators:
        - name: x
    ");
}

#[test]
fn test_typeof_type() {
    let decl = setup_declaration("typeof(int) x;");
    insta::assert_yaml_snapshot!(decl, @r#"
    Declaration:
      specifiers:
        - "Typeof(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) })"
      init_declarators:
        - name: x
    "#);
}

#[test]
fn test_typeof_comma_expr() {
    let decl = setup_declaration("typeof((void)0, 5) x;");
    insta::assert_yaml_snapshot!(decl, @r"
    Declaration:
      specifiers:
        - TypeofExpr(5)
      init_declarators:
        - name: x
    ");
}
