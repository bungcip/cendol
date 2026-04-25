use crate::tests::parser_utils::{setup_declaration, setup_translation_unit, setup_translation_unit_with_std};

#[test]
fn test_peek_past_attribute_exhaustive() {
    // Hits loop and line 79: multiple attributes
    let resolved = setup_declaration("void f(int __attribute__((noreturn)) __attribute__((unused)) *);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - void
      init_declarators:
        - name: f
          kind: function(int pointer) -> int
    ");
}

#[test]
fn test_array_size_variations_coverage() {
    // Hits parse_array_size branches for static, qualifiers, and star
    let resolved = setup_declaration("int f(int a[static 10]);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int array) -> int
    ");

    let resolved = setup_declaration("int f(int a[const 10]);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int array) -> int
    ");

    let resolved = setup_declaration("int f(int a[*]);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int array) -> int
    ");
}

#[test]
fn test_abstract_declarator_complex_coverage() {
    // Hits parse_abstract_declarator branches

    // Pointer to function returning int
    let resolved = setup_declaration("int f(int (*)(void));");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int function(void) -> pointer) -> int
    ");

    // Array of pointers
    let resolved = setup_declaration("int f(int *[]);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(pointer to array to int) -> int
    ");

    // Abstract function type ()
    let resolved = setup_declaration("int f(int ());");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int function(void) -> int) -> int
    ");
}

#[test]
fn test_abstract_declarator_with_attributes() {
    // Hits the attribute branch in parse_abstract_declarator
    let resolved = setup_declaration("int f(int __attribute__((noreturn)) (*)(void));");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int function(void) -> pointer) -> int
    ");
}

#[test]
fn test_get_declarator_name_bitfield() {
    // Hits ParsedDeclarator::BitField in get_declarator_name
    let resolved = setup_declaration("struct S { int x : 5; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct S { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_abstract_declarator_exhaustive() {
    // Hits line 381: Identifier as type name in abstract declarator
    // We use setup_translation_unit to handle the typedef
    let resolved = setup_translation_unit("typedef int T; void f(T);");
    insta::assert_yaml_snapshot!(&resolved, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - Typedef
            - int
          init_declarators:
            - name: T
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(T) -> int
    ");

    // Hits line 386: Identifier as type name followed by identifier (param name)
    let resolved = setup_translation_unit("typedef int T; void f(T x);");
    insta::assert_yaml_snapshot!(&resolved, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - Typedef
            - int
          init_declarators:
            - name: T
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(T) -> int
    ");

    // Hits line 394: 'int' (or other keyword) in abstract declarator context
    let resolved = setup_declaration("void f(int);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - void
      init_declarators:
        - name: f
          kind: function(int) -> int
    ");

    // Hits line 410: '(' followed by Attribute
    let resolved = setup_declaration("void f(int (__attribute__((unused)) *));");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - void
      init_declarators:
        - name: f
          kind: function(int pointer) -> int
    ");
}

#[test]
fn test_nested_function_params_coverage() {
    // Hits get_declarator_params recursion (line 361)
    // int (*f(void))(int)
    let resolved = setup_declaration("int (*f(void))(int);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int) -> pointer to function(void) -> int
    ");
}

#[test]
fn test_bitfield_exhaustive() {
    // Unnamed bitfield hits line 352 get_declarator_name with Identifier(None)
    let resolved = setup_declaration("struct S { int : 5; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct S { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_pointer_qualifiers_coverage() {
    // Hits line 178 in parse_leading_pointers
    let resolved = setup_declaration("int * const * volatile p;");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer to pointer
    ");
}

#[test]
fn test_mega_coverage_declarations() {
    // Hits line 111-112 (attributes after declarator), 581 (depth), 591 (unexpected C23 tokens)
    let source = "int x [[maybe_unused]] [[attr((1))]] [[123]], y __asm__(\"y\") [[maybe_unused]] = 1;";
    let _ = setup_translation_unit_with_std(source, crate::lang_options::CStandard::C23);

    // Hits parse_attribute: aligned(int), __aligned__(long), unknown, noreturn, packed, and _ => advance
    let source2 = "int z __attribute__((aligned(int), __aligned__(long), unknown(((1))), noreturn, packed, 123, ++));";
    let _ = setup_declaration(source2);
}
