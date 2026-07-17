use super::parser_utils::setup_declaration_with_std;
use crate::lang_options::CStandard;

#[test]
fn test_typeof_unqual_c11_fails() {
    crate::tests::test_utils::run_fail_with_message(
        "typeof_unqual(int) x;",
        "expected declaration specifiers, found typeof_unqual",
    );
}

#[test]
fn test_typeof_unqual_expr() {
    let decl = setup_declaration_with_std("typeof_unqual(5 + 3) x;", CStandard::C23);
    insta::assert_yaml_snapshot!(decl, @"
    Declaration:
      specifiers:
        - TypeofUnqualExpr(5)
      init_declarators:
        - name: x
    ");
}

#[test]
fn test_typeof_unqual_type() {
    let decl = setup_declaration_with_std("typeof_unqual(int) x;", CStandard::C23);
    insta::assert_yaml_snapshot!(decl, @r#"
    Declaration:
      specifiers:
        - "TypeofUnqual(PType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) })"
      init_declarators:
        - name: x
    "#);
}

#[test]
fn test_typeof_unqual_comma_expr() {
    let decl = setup_declaration_with_std("typeof_unqual((void)0, 5) x;", CStandard::C23);
    insta::assert_yaml_snapshot!(decl, @"
    Declaration:
      specifiers:
        - TypeofUnqualExpr(6)
      init_declarators:
        - name: x
    ");
}
