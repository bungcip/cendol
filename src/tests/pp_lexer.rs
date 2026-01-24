use crate::pp::pp_lexer::{PPLexer, PPToken};
use crate::pp::PPTokenKind;
use crate::source_manager::SourceId;
use serde::Serialize;
use std::collections::BTreeMap;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

#[derive(Serialize)]
struct SnapshotPPToken {
    kind: String,
    text: String,
    flags: String,
}

impl From<PPToken> for SnapshotPPToken {
    fn from(token: PPToken) -> Self {
        let kind = match &token.kind {
            PPTokenKind::Identifier(_) => "Identifier".to_string(),
            PPTokenKind::StringLiteral(_) => "StringLiteral".to_string(),
            PPTokenKind::CharLiteral(_, _) => "CharLiteral".to_string(),
            PPTokenKind::Number(_) => "Number".to_string(),
            k => format!("{:?}", k),
        };

        let text = token.get_text().to_string();

        let flags = format!("{:?}", token.flags);

        SnapshotPPToken { kind, text, flags }
    }
}

fn snapshot_pp_lexer(source: &str) -> Vec<SnapshotPPToken> {
    let mut lexer = create_test_pp_lexer(source);
    let mut tokens = Vec::new();
    while let Some(token) = lexer.next_token() {
        tokens.push(token.into());
    }
    tokens
}

fn get_pp_lexer_cases(cases: Vec<&str>) -> BTreeMap<&str, Vec<SnapshotPPToken>> {
    let mut all = BTreeMap::new();
    for case in cases {
        all.insert(case, snapshot_pp_lexer(case));
    }
    all
}

#[test]
fn test_line_splicing_comprehensive() {
    let cases = vec![
        "hel\\\nlo",
        "hel\\\nlo\\\nworld",
        "123\\\n456",
        "\"hello\\\nworld\"",
        "hel  \\\n    lo",
        "hello\nworld",
        "test\\",
        "hel\\\r\nlo",
        "hel\\\rlo",
        "test\\\r",
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_all_punctuation_tokens() {
    let source = "+ - * / % & | ^ ! ~ < > <= >= == != << >> = += -= *= /= %= &= |= ^= <<= >>= ++ -- -> . ? : , ; ( ) [ ] { } ... && || # ##";
    let tokens = snapshot_pp_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_all_keyword_tokens() {
    let source = "if ifdef ifndef elif else endif define undef include line pragma error warning";
    let tokens = snapshot_pp_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_all_literal_tokens() {
    let source = "variable \"string\" 'c' 123";
    let tokens = snapshot_pp_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_adjacent_string_literals_not_combined() {
    let source = "\"hello\" \"world\"";
    let tokens = snapshot_pp_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_line_splicing_in_skip_whitespace() {
    let source = "   \\\n   identifier";
    let tokens = snapshot_pp_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_hash_flags() {
    let cases = vec![
        "#",
        "  #",
        "##",
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_wide_literals() {
    let cases = vec![
        "L'a' u'b' U'c' '\\0'",
        "L\"hello\" u\"world\" U\"test\"",
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_eod_token_production() {
    let cases = vec![
        "#define x 1\n",
        "#ifdef TEST\n",
        "#ifndef TEST\n",
        "#elif 1\n",
        "#else\n",
        "#endif\n",
        "#include \"test.h\"\n",
        "#undef TEST\n",
        "#line 100\n",
        "#pragma once\n",
        "#error message\n",
        "#warning message\n",
        "#define x 1", // EOF case
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_bmp_unicode_string_literals() {
    let source = r#"L"hello$$你好¢¢世界€€world""#;
    let tokens = snapshot_pp_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_various_bmp_characters() {
    let cases = vec![
        r#"L"你好世界""#,
        r#"L"€$¢£¥""#,
        r#"L"hello¢world€test""#,
        r#"L"café naïve résumé""#,
        r#"L"αβγδε""#,
        r#"L"привет мир""#,
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_special_characters_in_strings() {
    let cases = vec![
        r#"L"hello \"world\" \\test""#,
        r#"L"café's \"test\" \\value""#,
        r#"L"hello\
world""#,
        r#"""#,
        r#"L"""#,
        r#"u"""#,
        r#"U"""#,
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_utf8_sequence_lengths() {
    let cases = vec![
        r#"L"abc""#,
        r#"L"café""#,
        r#"L"你好""#,
        r#"L"café你好""#,
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_consecutive_splices() {
    let cases = vec![
        "A\\\n\\\nB",
        "A\\\r\n\\\r\nB",
    ];
    let tokens = get_pp_lexer_cases(cases);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_hex_float_literal() {
    let source = "0x1p+1 0x1.fp-2 0x1P+1";
    let tokens = snapshot_pp_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_peek_next_char_splicing() {
    let source = "a\\\nb";
    let mut lexer = create_test_pp_lexer(source);
    // next_char
    assert_eq!(lexer.next_char(), Some(b'a'));
    assert_eq!(lexer.next_char(), Some(b'b'));
    assert_eq!(lexer.next_char(), None);

    let mut lexer = create_test_pp_lexer(source);
    // peek_char
    assert_eq!(lexer.peek_char(), Some(b'a'));
    assert_eq!(lexer.position, 0);
    assert_eq!(lexer.next_char(), Some(b'a'));
    assert_eq!(lexer.position, 1);
    assert_eq!(lexer.peek_char(), Some(b'b'));
    assert_eq!(lexer.position, 1);
}
