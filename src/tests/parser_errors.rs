use crate::driver::artifact::CompilePhase;
use crate::lang_options::CStandard;
use crate::tests::parser_utils::{setup_declaration, setup_translation_unit};
use crate::tests::test_utils::{run_fail_with_message, run_pass, run_pass_with_std};

#[test]
fn test_invalid_attributes_recovery() {
    // Tests for peek_past_attribute EOF and format fallbacks (lines 36-74)
    run_pass("int foo __attribute__;", CompilePhase::Parse);
    run_pass("int foo __attribute__(;", CompilePhase::Parse);
    run_pass("int foo __attribute__(();", CompilePhase::Parse);
    run_pass("int foo __attribute__((foo", CompilePhase::Parse);

    // This checks `depth += 1` inside attribute paren matching
    let decl5 = setup_declaration("int foo __attribute__(((foo)));");
    insta::assert_yaml_snapshot!(&decl5, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: foo
    ");

    // 74: EOF after one Attribute block
    run_pass("int x __attribute__((foo))", CompilePhase::Parse);

    // Targeted tests for peek_past_attribute (disambiguation context)
    run_pass("void f(int (__attribute__ * x));", CompilePhase::Parse);
    run_pass("void f(int (__attribute__ (unused) * x));", CompilePhase::Parse);
    run_pass("void f(int (__attribute__((unused(1))) * x));", CompilePhase::Parse);
    run_pass(
        "void f(int (__attribute__((unused)) __attribute__((unused)) * x));",
        CompilePhase::Parse,
    );
    run_pass("void f(int (__attribute__((unused)) x));", CompilePhase::Parse);

    // Disambiguation: attribute followed by *
    let decl6 = setup_declaration("void f(int (__attribute__((unused)) *));");
    insta::assert_yaml_snapshot!(&decl6, @"
    Declaration:
      specifiers:
        - void
      init_declarators:
        - name: f
          kind: function(int pointer) -> int
    ");

    let resolved = setup_declaration("int (__attribute__ x);");
    insta::assert_yaml_snapshot!(&resolved, @"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
    ");
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

/// all declarator/declaration/statement parser error is in here
#[test]
fn test_parser_errors() {
    let cases = [
        // A. Declarator errors
        ("int foo()();", "Declaration not allowed in this context"),
        ("int foo()[5];", "Declaration not allowed in this context"),
        ("int foo[5]();", "Declaration not allowed in this context"),
        ("int (***+x);", "expected ), found +"),
        ("void foo(int +);", "expected ), found +"),
        ("void foo(int (int +));", "expected ), found int"),
        ("void foo(int (int x +));", "expected ), found int"),
        ("void foo(int (+));", "expected ), found +"),
        ("void foo(+);", "expected ), found +"),
        ("void foo(+x);", "expected ), found +"),
        ("void foo(int x, +);", "expected ), found +"),
        ("void foo(){foo(1}", "expected )"),
        ("void foo() { int x[] = {1, 2; }", "expected }"),
        ("void foo() { struct S { int x; ", "expected }"),
        ("void foo(int x, int y", "expected )"),
        ("void foo(int ( + ));", "expected ), found +"),
        ("void foo(int ..., int);", "expected ), found ..."),
        // B. Context-specific "expected identifier" errors
        ("void foo() { struct S s; s . 1; }", "expected identifier, found 1"),
        ("void foo() { struct S *s; s->1; }", "expected identifier, found 1"),
        (
            "void foo() { __builtin_offsetof(struct S, 1); }",
            "expected identifier, found 1",
        ),
        ("enum E { 1 };", "expected identifier, found 1"),
        (
            "struct S { int x; }; void foo() { struct S s = { . + = 1 }; }",
            "expected identifier, found +",
        ),
        ("void foo() { goto 1; }", "expected identifier, found 1"),
        // C. Declaration/Statement errors
        (
            "int foo() { int 1; }",
            "expected Expected declarator or identifier after type specifier",
        ),
        // D. Type specifier errors
        ("long", "Unexpected token"),
        ("_Atomic(", "Unexpected token"),
        ("void foo() { (int struct S { int x; }) 0; }", "single type specifier"),
        // E. Hex float validation (lexical error in constant parsing)
        ("void foo() { double x = 0x1.0p; }", "invalid token"),
        // F. Coverage for specific "expected" messages in parse_decl
        (
            "void foo() { struct S { int x; } 123; }",
            "Expected ';' after struct/union definition",
        ),
        ("void foo() { enum E { A } 123; }", "Expected ';' after enum definition"),
        ("void foo() { extern 123; }", "Expected type specifiers"),
        ("void foo(int __attribute__ noreturn);", "expected ), found int"),
        ("int __attribute__((noreturn))", "Expected type specifiers"),
        ("int ", "Expected declarator or identifier after type specifier"),
        ("int x[10 ;", "expected ], found ;"),
        ("void foo(int ( * );", "expected ), found ;"),
        ("void foo(int ( * [ ] );", "expected ), found ;"),
        ("void foo(int x : 5);", "expected ), found :"),
        ("void foo(int : 5);", "expected ), found :"),
        ("int x : 5;", "expected ';' after declaration, found :"),
        // G. Coverage for synchronization and lexer errors
        (r#"#error "custom error""#, "custom error"),
        ("#endif", "Unmatched #endif"),
        (r#"#error "fail""#, "fail"),
        ("int x = +; }", "found ;"),
        ("int x =", "found end of file"),
        ("_Alignas(", "found end of file"),
        ("void foo() { (", "found end of file"),
        ("void foo() { { int x = +; } }", "found ;"),
        ("[[maybe_unused]]", "found ["),
    ];

    for (source, message) in cases {
        run_fail_with_message(source, message);
    }
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
    // This test ensures that the ParsedDeclarator::Abstract variant is correctly
    // handled by build_parsed_declarator.
    // Abstract declarators appear in type names (casts, sizeof, alignof).
    run_pass(
        r#"
        int main() {
            // sizeof(type-name) uses abstract declarators
            int sz1 = sizeof(int *);           // Abstract pointer
            int sz2 = sizeof(int [5]);         // Abstract array
            int sz3 = sizeof(int (*)(void));   // Abstract function pointer

            // Casts also use abstract declarators
            int x = (int)3.14;

            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_is_type_name_start_c23_attr() {
    // Triggers return true on C23 attribute start in is_type_name_start
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
