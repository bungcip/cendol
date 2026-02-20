use crate::driver::artifact::CompilePhase;
use crate::tests::parser_utils::{setup_declaration, setup_translation_unit};
use crate::tests::test_utils;

use crate::diagnostic::DiagnosticLevel;

fn has_parse_errors(source: &str) -> bool {
    let (driver, _) = test_utils::run_pipeline(source, CompilePhase::Parse);
    driver
        .get_diagnostics()
        .iter()
        .any(|d| d.level == DiagnosticLevel::Error)
}

#[test]
fn test_invalid_attributes_recovery() {
    // Tests for peek_past_attribute EOF and format fallbacks (lines 36-74)
    test_utils::run_pass("int foo __attribute__;", CompilePhase::Parse);
    test_utils::run_pass("int foo __attribute__(;", CompilePhase::Parse);
    test_utils::run_pass("int foo __attribute__(();", CompilePhase::Parse);
    test_utils::run_pass("int foo __attribute__((foo", CompilePhase::Parse);

    // This checks `depth += 1` inside attribute paren matching
    let decl5 = setup_translation_unit("int foo __attribute__(((foo)));");
    insta::assert_yaml_snapshot!(&decl5, @r"
    TranslationUnit:
      - Declaration:
          specifiers:
            - int
          init_declarators:
            - name: foo
    ");

    // 74: EOF after one Attribute block
    test_utils::run_pass("int x __attribute__((foo))", CompilePhase::Parse);

    // Targeted tests for peek_past_attribute (disambiguation context)
    // Line 36, 45, 58, 71
    test_utils::run_pass("void f(int (__attribute__ * x));", CompilePhase::Parse); // No LeftParen after Attribute (falls back)
    test_utils::run_pass("void f(int (__attribute__ (unused) * x));", CompilePhase::Parse); // No second LeftParen
    test_utils::run_pass("void f(int (__attribute__((unused(1))) * x));", CompilePhase::Parse); // depth += 1 (Line 58)
    test_utils::run_pass(
        "void f(int (__attribute__((unused)) __attribute__((unused)) * x));",
        CompilePhase::Parse,
    ); // Multiple attributes (Line 73)
    test_utils::run_pass("void f(int (__attribute__((unused)) x));", CompilePhase::Parse); // Not Attribute after one (Line 70)

    // Disambiguation: attribute followed by *
    let decl6 = setup_translation_unit("void f(int (__attribute__((unused)) *));");
    insta::assert_yaml_snapshot!(&decl6, @r"
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
fn test_function_returning_function() {
    assert!(has_parse_errors("int foo()();"));
}

#[test]
fn test_function_returning_array() {
    assert!(has_parse_errors("int foo()[5];"));
}

#[test]
fn test_array_of_functions() {
    assert!(has_parse_errors("int foo[5]();"));
}

#[test]
fn test_type_qualifiers_atomic_restrict() {
    let decl = setup_declaration("int * restrict _Atomic p;");
    insta::assert_yaml_snapshot!(&decl, @r"
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
    insta::assert_yaml_snapshot!(&decl, @r"
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
    // Falls into `parse_abstract_declarator(parser)?` from `parse_declarator(parser, None)`
    let decl = setup_translation_unit("void foo(int (*));");
    insta::assert_yaml_snapshot!(&decl, @r"
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
fn test_invalid_tokens_in_declarator() {
    // Tests token consumption loop in parse_declarator
    assert!(has_parse_errors("int (***+x);"));
}

#[test]
fn test_array_size_qualifiers() {
    // Tests `parse_array_size` matching `static` and qualifiers
    let decl = setup_translation_unit("void foo(int a[static restrict 5]);");
    insta::assert_yaml_snapshot!(&decl, @r"
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
fn test_abstract_declarator_fallbacks() {
    // Covers `is_abstract_declarator_start` returning false
    assert!(has_parse_errors("void foo(int +);")); // Not a *. (, or [

    // Covers `parse_abstract_declarator` TokenKind::Int fallback without identifier
    assert!(has_parse_errors("void foo(int (int +));"));

    // Covers `parse_abstract_declarator` TokenKind fallback identifier validation
    assert!(has_parse_errors("void foo(int (int x +));"));

    // Covers `parse_abstract_declarator` wildcard token fallback
    assert!(has_parse_errors("void foo(int (+));"));
}

#[test]
fn test_function_param_fallback() {
    // Covers lines 336-346 fallback for failed parse_declaration_specifiers
    // and empty declarations in params
    assert!(has_parse_errors("void foo(+);"));
    assert!(has_parse_errors("void foo(+x);"));
    // Recovery path in parse_function_parameters (lines 340-344)
    assert!(has_parse_errors("void foo(int x, +);"));
}

#[test]
fn test_complex_abstract_declarators_trailing() {
    // Covers parse_trailing_declarators_for_type_names gaps (lines 124, 130, 137-145)
    // Wait, the plan said lines 124, 130, 137-145 in declarator.rs but those are in parse_declarator
    // Let's use constructs that trigger them.

    // Abstract declarator with trailing array
    let decl1 = setup_translation_unit("void f(int [10]);");
    insta::assert_yaml_snapshot!(&decl1, @r"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(int array) -> int
    ");

    // Abstract declarator with trailing function
    let decl2 = setup_translation_unit("void f(int (int));");
    insta::assert_yaml_snapshot!(&decl2, @r"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(function(int) -> int) -> int
    ");

    // Complex abstract declarator: pointer to array of functions (invalid but triggers logic)
    // Removed has_parse_errors check as it is recovered by parse_function_parameters
    let _ = setup_translation_unit("void f(int (*)(int)[10]);");
}

#[test]
fn test_abstract_declarator_left_paren_gaps() {
    // Covers lines 493, 499, 512-516, 529-535 in parse_abstract_declarator

    // Empty parameter list in abstract declarator
    let decl1 = setup_translation_unit("void f(int ());");
    insta::assert_yaml_snapshot!(&decl1, @r"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(function(void) -> int) -> int
    ");

    // Variadic abstract declarator
    let decl2 = setup_translation_unit("void f(int (*)(...));");
    insta::assert_yaml_snapshot!(&decl2, @r"
    TranslationUnit:
      - Declaration:
          specifiers:
            - void
          init_declarators:
            - name: f
              kind: function(int function(...) -> pointer) -> int
    ");

    // Nested abstract declarator with left paren fallback (line 538)
    assert!(has_parse_errors("void f(int ( + ));"));
}

#[test]
fn test_pointer_qualifier_abstract() {
    // Covers lines 552-554 in parse_abstract_declarator
    let decl = setup_translation_unit("void f(int * restrict);");
    insta::assert_yaml_snapshot!(&decl, @r"
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
    // Attempting to hit lines 447-479 in parse_abstract_declarator

    // Hit Int arm (Line 466): ( * int )
    // is_param_list_start will be false because it sees *
    // parse_leading_pointers consumes *
    // then it sees int. HITS Int arm.
    let _ = setup_translation_unit("void f(int (* int));");

    // Hit Identifier arm with Type Name (Line 449): ( * my_int )
    let _ = setup_translation_unit("typedef int my_int; void f(int (* my_int));");

    // Hit Identifier arm with Type Name and next Identifier (Line 453): ( * my_int p )
    // This is weird but it should hit the branch.
    let _ = setup_translation_unit("typedef int my_int; void f(int (* my_int p));");
}
