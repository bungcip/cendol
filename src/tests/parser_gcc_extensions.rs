use crate::tests::parser_utils::{setup_declaration, setup_expr, setup_translation_unit};

#[test]
fn test_restrict_keyword() {
    let resolved = setup_declaration("int * __restrict p;");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer
    ");
}

#[test]
fn test_restrict_keyword_underscores() {
    let resolved = setup_declaration("int * __restrict__ p;");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer
    ");
}

#[test]
fn test_const_keyword_underscores() {
    let resolved = setup_declaration("int * __const__ p;");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer
    ");
}

#[test]
fn test_multiple_attributes_function_decl() {
    let code = "void foo() __attribute__((noreturn)) __attribute__((nothrow));";
    let resolved = setup_translation_unit(code);
    insta::assert_yaml_snapshot!(&resolved, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: foo
              kind: function(void) -> int
    ");
}

#[test]
fn test_gcc_keywords_in_parameters() {
    let code = "int foo(const char * __restrict format, ...);";
    let resolved = setup_declaration(code);
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: foo
          kind: "function(char pointer, ...) -> int"
    "#);
}

#[test]
fn test_asm_label() {
    let code = "int foo() __asm__(\"foo_impl\");";
    let resolved = setup_translation_unit(code);
    insta::assert_yaml_snapshot!(&resolved, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - int
          init_declarators:
            - name: foo
              kind: function(void) -> int
    ");
}

#[test]
fn test_asm_and_attributes() {
    let code = "int foo() __asm__(\"foo_impl\") __attribute__((nothrow));";
    let resolved = setup_translation_unit(code);
    insta::assert_yaml_snapshot!(&resolved, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - int
          init_declarators:
            - name: foo
              kind: function(void) -> int
    ");
}

#[test]
fn test_attribute_in_cast() {
    let resolved = setup_expr("(__attribute__((__noinline__)) int) 1");
    insta::assert_yaml_snapshot!(&resolved, @"
    Cast:
      - parsed_type_1_1
      - LiteralInt: 1
    ");
}

#[test]
fn test_gnu_statement_expression() {
    let resolved = setup_expr("({ int x = 1; x + 2; })");
    insta::assert_yaml_snapshot!(&resolved, @"
    GnuStatementExpression:
      - CompoundStatement:
          - Declaration:
              specifiers:
                - int
              init_declarators:
                - name: x
                  initializer:
                    LiteralInt: 1
          - ExpressionStatement:
              BinaryOp:
                - Add
                - Ident: x
                - LiteralInt: 2
      - BinaryOp:
          - Add
          - Ident: x
          - LiteralInt: 2
    ");
}
