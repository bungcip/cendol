use crate::pp::PPTokenKind;
use crate::pp::pp_lexer::PPLexer;
use crate::source_manager::SourceId;
use crate::tests::pp_common::setup_pp_snapshot;

/// Helper to create a lexer (copied/adapted from pp_lexer.rs for isolation)
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

#[test]
fn test_lexer_line_splicing_with_whitespace() {
    // This was the issue: splicing failed if there was whitespace between \ and \n
    // "VAL\ \nUE" -> "VALUE"
    let source = "VAL\\ \nUE";
    let mut lexer = create_test_pp_lexer(source);

    // Should lex as "VALUE"
    let token = lexer.next_token().unwrap();
    assert_eq!(
        token.kind,
        PPTokenKind::Identifier(crate::intern::StringId::new("VALUE"))
    );
}

#[test]
fn test_lexer_line_splicing_with_tab() {
    let source = "VAL\\ \t \nUE";
    let mut lexer = create_test_pp_lexer(source);

    let token = lexer.next_token().unwrap();
    assert_eq!(
        token.kind,
        PPTokenKind::Identifier(crate::intern::StringId::new("VALUE"))
    );
}

#[test]
fn test_preprocessor_multiline_directive_with_splice() {
    // This was the issue: preprocessor checked line numbers and stopped early
    let src = r#"
#define FOO 1
#if FOO \
    && 1
int x = 1;
#else
int x = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_preprocessor_multiline_directive_with_whitespace_splice() {
    // Combined test: whitespace splice + multi-line directive
    // Note the space after backslash
    let src = r#"
#define FOO 1
#if FOO \ 
    && 1
int y = 1;
#else
int y = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: y
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}
