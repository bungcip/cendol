use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_digraph_tokenization() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    // Note: PPTokenKind::get_fixed_text() returns the standard punctuation character(s)
    // for these tokens, even if they were lexed as digraphs.
    test_tokens!(
        lexer,
        ("[", PPTokenKind::LeftBracket),
        ("]", PPTokenKind::RightBracket),
        ("{", PPTokenKind::LeftBrace),
        ("}", PPTokenKind::RightBrace),
        ("#", PPTokenKind::Hash),
        ("##", PPTokenKind::HashHash),
    );
}

#[test]
fn test_digraph_directive_initiation() {
    let source = "%:define FOO 1\nFOO";
    let tokens = setup_pp_snapshot(source);

    // Should expand FOO to 1
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Number
      text: \"1\"
    ");
}

#[test]
fn test_digraph_stringification() {
    let source = r#"
%:define STR(x) %:x
STR(hello)
"#;
    let tokens = setup_pp_snapshot(source);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: StringLiteral
      text: \"\\\"hello\\\"\"
    ");
}

#[test]
fn test_digraph_concatenation() {
    let source = r#"
%:define CONCAT(a, b) a %:%: b
CONCAT(foo, bar)
"#;
    let tokens = setup_pp_snapshot(source);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: foobar
    ");
}

#[test]
fn test_digraph_in_disabled_block() {
    let source = r#"
#if 0
  %:define SHOULD_BE_SKIPPED 1
#endif
SHOULD_BE_SKIPPED
"#;
    let tokens = setup_pp_snapshot(source);
    // SHOULD_BE_SKIPPED should NOT be expanded
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: SHOULD_BE_SKIPPED
    ");
}

#[test]
fn test_digraph_mixed_with_standard() {
    let source = "<% int a<:1:>; %>";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("{", PPTokenKind::LeftBrace),
        ("int", PPTokenKind::Identifier(_)),
        ("a", PPTokenKind::Identifier(_)),
        ("[", PPTokenKind::LeftBracket),
        ("1", PPTokenKind::Number),
        ("]", PPTokenKind::RightBracket),
        (";", PPTokenKind::Semicolon),
        ("}", PPTokenKind::RightBrace),
    );
}

#[test]
fn test_digraph_percent_colon_at_start_of_line() {
    let source = "  %: define BAR 2\nBAR";
    let tokens = setup_pp_snapshot(source);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Number
      text: \"2\"
    ");
}

#[test]
fn test_digraph_hash_hash_complex() {
    // Test %:%: as ## in various positions
    let source = r#"
%:define GLUE(a, b) a%:%:b
GLUE(1, 2)
"#;
    let tokens = setup_pp_snapshot(source);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Number
      text: \"12\"
    ");
}
