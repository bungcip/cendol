use crate::tests::parser_utils::setup_declaration;

#[test]
fn test_attribute_before_declarator_failure() {
    // This tests the uncovered code path in parse_declarator where parse_attribute fails.
    // parse_declarator catches the error and continues.
    // We use "int (__attribute__ x);" because at the top level, parse_declaration_specifiers
    // consumes __attribute__. But inside parentheses, parse_declarator is called recursively
    // and sees __attribute__ first.
    // "__attribute__" is consumed, but "x" is not "((", so parse_attribute fails.
    // The parser then continues to parse "x" as the declarator.
    let resolved = setup_declaration("int (__attribute__ x);");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
    ");
}
