use super::parser_utils::setup_declaration;

#[test]
fn test_typeof_unqual_expr() {
    let decl = setup_declaration("typeof_unqual(5 + 3) x;");
    insta::assert_yaml_snapshot!(decl, @"
    Declaration:
      specifiers:
        - TypeofUnqualExpr(4)
      init_declarators:
        - name: x
    ");
}

#[test]
fn test_typeof_unqual_type() {
    let decl = setup_declaration("typeof_unqual(int) x;");
    insta::assert_yaml_snapshot!(decl, @r#"
    Declaration:
      specifiers:
        - "TypeofUnqual(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) })"
      init_declarators:
        - name: x
    "#);
}

#[test]
fn test_typeof_unqual_comma_expr() {
    let decl = setup_declaration("typeof_unqual((void)0, 5) x;");
    insta::assert_yaml_snapshot!(decl, @"
    Declaration:
      specifiers:
        - TypeofUnqualExpr(5)
      init_declarators:
        - name: x
    ");
}
