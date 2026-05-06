use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_all_digraph_tokens() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("<:", PPTokenKind::LeftBracket),
        (":>", PPTokenKind::RightBracket),
        ("<%", PPTokenKind::LeftBrace),
        ("%>", PPTokenKind::RightBrace),
        ("%:", PPTokenKind::Hash),
        ("%:%:", PPTokenKind::HashHash),
    );
}

#[test]
fn test_digraph_directive() {
    let src = r#"
%:define FOO 1
%:if FOO
OK
%:endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_pasting() {
    let src = r#"
#define PASTE(a, b) a %:%: b
int PASTE(x, y) = 42;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_stringification() {
    let src = r#"
#define STR(x) %:x
char *s = STR(<: :>);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_mixed_with_standard() {
    let source = "<: ] { %> # %:%:";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("<:", PPTokenKind::LeftBracket),
        ("]", PPTokenKind::RightBracket),
        ("{", PPTokenKind::LeftBrace),
        ("%>", PPTokenKind::RightBrace),
        ("#", PPTokenKind::Hash),
        ("%:%:", PPTokenKind::HashHash),
    );
}

#[test]
fn test_digraph_fast_skip() {
    let src = r#"
#if 0
  %:define SHOULD_NOT_HAPPEN
#else
  OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_not_pasting() {
    // %:%: is ##, but %: followed by something else is just # followed by that thing
    let source = "%:%";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("%:", PPTokenKind::Hash), ("%", PPTokenKind::Percent),);
}
