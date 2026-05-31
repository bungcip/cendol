use crate::driver::artifact::CompilePhase;
use crate::lang_options::CStandard;
use crate::tests::parser_utils::{setup_declaration, setup_translation_unit, setup_translation_unit_with_std};
use crate::tests::test_utils::{run_pass, run_pass_with_std};

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
    let resolved = setup_declaration("struct S { int x : 5; } s;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct S { ... }"
      init_declarators:
        - name: s
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
    let resolved = setup_declaration("struct S { int : 5; } s;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct S { ... }"
      init_declarators:
        - name: s
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

#[test]
fn test_get_declarator_params_coverage() {
    // Hits line 348 in get_declarator_params (Function returning function pointer)
    let _ = setup_translation_unit("void (*f())(int) { return 0; }");

    // Hits line 354 in get_declarator_params (Array of function pointers / function returning pointer to array)
    let _ = setup_translation_unit("int (*g())[5] { return 0; }");
}

#[test]
fn test_type_qualifiers_atomic_restrict() {
    let decl = setup_declaration("int * restrict _Atomic p;");
    insta::assert_yaml_snapshot!(&decl, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer
    ");
}

#[test]
fn test_vla_star_size() {
    let decl = setup_translation_unit("void foo(int a[*]);");
    insta::assert_yaml_snapshot!(&decl, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: foo
              kind: function(int array) -> int
    ");
}

#[test]
fn test_abstract_declarator_in_declarator() {
    let decl = setup_translation_unit("void foo(int (*));");
    insta::assert_yaml_snapshot!(&decl, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: foo
              kind: function(int pointer) -> int
    ");
}

#[test]
fn test_array_size_qualifiers() {
    let decl = setup_translation_unit("void foo(int a[static restrict 5]);");
    insta::assert_yaml_snapshot!(&decl, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: foo
              kind: function(int array) -> int
    ");
}

#[test]
fn test_complex_abstract_declarators_trailing() {
    let decl1 = setup_translation_unit("void f(int [10]);");
    insta::assert_yaml_snapshot!(&decl1, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(int array) -> int
    ");

    let decl2 = setup_translation_unit("void f(int (int));");
    insta::assert_yaml_snapshot!(&decl2, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(int function(int) -> int) -> int
    ");

    let _ = setup_translation_unit("void f(int (*)(int)[10]);");
}

#[test]
fn test_abstract_declarator_left_paren_gaps() {
    let decl1 = setup_translation_unit("void f(int ());");
    insta::assert_yaml_snapshot!(&decl1, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(int function(void) -> int) -> int
    ");

    let decl2 = setup_translation_unit("void f(int (*)(...));");
    insta::assert_yaml_snapshot!(&decl2, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(int function(...) -> pointer) -> int
    ");
}

#[test]
fn test_pointer_qualifier_abstract() {
    let decl = setup_translation_unit("void f(int * restrict);");
    insta::assert_yaml_snapshot!(&decl, @"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(int pointer) -> int
    ");
}

#[test]
fn test_abstract_declarator_dead_arms_attempt() {
    let _ = setup_translation_unit("void f(int (* int));");
    let _ = setup_translation_unit("typedef int my_int; void f(int (* my_int));");
    let _ = setup_translation_unit("typedef int my_int; void f(int (* my_int p));");
}

#[test]
fn test_abstract_declarator_builder_coverage() {
    run_pass(
        r#"
        int main() {
            int sz1 = sizeof(int *);           // Abstract pointer
            int sz2 = sizeof(int [5]);         // Abstract array
            int sz3 = sizeof(int (*)(void));   // Abstract function pointer
            int x = (int)3.14;                 // Cast
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_is_type_name_start_c23_attr() {
    run_pass_with_std(
        r#"
        void foo() {
            int x = ([[maybe_unused]] int)1;
        }
        "#,
        CompilePhase::Parse,
        CStandard::C23,
    );
}
