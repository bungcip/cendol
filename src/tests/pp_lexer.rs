use crate::pp::pp_lexer::{PPLexer, PPToken, PPTokenFlags};
use crate::source_manager::SourceId;
use serde::Serialize;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

#[derive(Serialize)]
struct SnapshotToken {
    kind: String,
    text: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    flags: Vec<String>,
}

impl From<PPToken> for SnapshotToken {
    fn from(token: PPToken) -> Self {
        let kind_str = format!("{:?}", token.kind);
        // Clean up kind string to remove unstable IDs
        let kind_clean = if kind_str.starts_with("Identifier") {
            "Identifier".to_string()
        } else if kind_str.starts_with("StringLiteral") {
            "StringLiteral".to_string()
        } else if kind_str.starts_with("Number") {
            "Number".to_string()
        } else if kind_str.starts_with("CharLiteral") {
            // CharLiteral(97, StringId(..)) -> CharLiteral(97)
            let end = kind_str.find(',').unwrap_or(kind_str.len());
             format!("{})", &kind_str[0..end])
        } else {
            kind_str
        };

        let mut flags = Vec::new();
        if token.flags.contains(PPTokenFlags::LEADING_SPACE) { flags.push("LEADING_SPACE".to_string()); }
        if token.flags.contains(PPTokenFlags::STARTS_PP_LINE) { flags.push("STARTS_PP_LINE".to_string()); }
        if token.flags.contains(PPTokenFlags::NEEDS_CLEANUP) { flags.push("NEEDS_CLEANUP".to_string()); }
        if token.flags.contains(PPTokenFlags::MACRO_EXPANDED) { flags.push("MACRO_EXPANDED".to_string()); }
        flags.sort();

        SnapshotToken {
            kind: kind_clean,
            text: token.get_text().to_string(),
            flags,
        }
    }
}

fn tokenize(source: &str) -> Vec<SnapshotToken> {
    let mut lexer = create_test_pp_lexer(source);
    let mut tokens = Vec::new();
    while let Some(token) = lexer.next_token() {
        tokens.push(token.into());
    }
    tokens
}

/// Test comprehensive line splicing scenarios
#[test]
fn test_line_splicing_comprehensive() {
    let sources = vec![
        // Basic line splicing
        "hel\\\nlo\nhel\\\nlo\\\nworld\n123\\\n456\n\"hello\\\nworld\"\n",
        // Line splicing with whitespace
        "hel  \\\n    lo",
        // No line splicing (regular newline)
        "hello\nworld",
        // Line splicing at end of buffer
        "test\\",
        // Line splicing with CRLF
        "hel\\\r\nlo",
        // Line splicing with CR
        "hel\\\rlo",
        // Line splicing with CR at end
        "test\\\r",
    ];

    let results: Vec<_> = sources.iter().map(|&src| (src, tokenize(src))).collect();
    insta::assert_yaml_snapshot!(results);

    // Test next_char with line splicing manually as it tests internal state
    let source = "a\\\nb";
    let mut lexer = create_test_pp_lexer(source);
    assert_eq!(lexer.next_char(), Some(b'a'));
    assert_eq!(lexer.next_char(), Some(b'b'));
    assert_eq!(lexer.next_char(), None);

    // Test peek_char with line splicing
    let source = "a\\\nb";
    let mut lexer = create_test_pp_lexer(source);
    assert_eq!(lexer.peek_char(), Some(b'a'));
    assert_eq!(lexer.position, 0);
    assert_eq!(lexer.next_char(), Some(b'a'));
    assert_eq!(lexer.position, 1);
    assert_eq!(lexer.peek_char(), Some(b'b'));
    assert_eq!(lexer.position, 1);
}

/// Test that PPLexer can produce all punctuation tokens
#[test]
fn test_all_punctuation_tokens() {
    let source = "+ - * / % & | ^ ! ~ < > <= >= == != << >> = += -= *= /= %= &= |= ^= <<= >>= ++ -- -> . ? : , ; ( ) [ ] { } ... && || # ##";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that PPLexer can produce all keyword tokens
#[test]
fn test_all_keyword_tokens() {
    let source = "if ifdef ifndef elif else endif define undef include line pragma error warning";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that PPLexer can produce all literal tokens
#[test]
fn test_all_literal_tokens() {
    let source = "variable \"string\" 'c' 123";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that adjacent string literals are not combined in preprocessor stage
#[test]
fn test_adjacent_string_literals_not_combined() {
    let source = "\"hello\" \"world\"";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that line splicing is handled correctly in skip_whitespace_and_comments
#[test]
fn test_line_splicing_in_skip_whitespace() {
    let source = "   \\\n   identifier";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that single # tokens always have STARTS_PP_LINE flag set
#[test]
fn test_hash_starts_pp_line() {
    let source = "#";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that indented # tokens have STARTS_PP_LINE flag set
#[test]
fn test_indented_hash_starts_pp_line() {
    let source = "  #";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that ## tokens do not have STARTS_PP_LINE flag set
#[test]
fn test_hashhash_no_starts_pp_line() {
    let source = "##";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test wide character literals with L, u, U prefixes
#[test]
fn test_wide_character_literals() {
    let source = "L'a' u'b' U'c' '\\0'";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test wide string literals with L, u, U prefixes
#[test]
fn test_wide_string_literals() {
    let source = "L\"hello\" u\"world\" U\"test\"";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that Eod (End of Directive) tokens are produced at the end of directive lines
#[test]
fn test_eod_token_production() {
    let source = "#define x 1\n";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that Eod tokens are produced for various directive types
#[test]
fn test_eod_for_various_directives() {
    let test_cases = vec![
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
    ];

    let results: Vec<_> = test_cases.iter().map(|&src| (src, tokenize(src))).collect();
    insta::assert_yaml_snapshot!(results);
}

/// Test that Eod is produced at EOF when in directive line (clang compatibility)
#[test]
fn test_eod_at_eof_in_directive() {
    let source = "#define x 1";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test string literals with BMP (Basic Multilingual Plane) Unicode characters
#[test]
fn test_bmp_unicode_string_literals() {
    let source = r#"L"hello$$你好¢¢世界€€world""#;
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test various BMP character types in string literals
#[test]
fn test_various_bmp_characters() {
    let test_cases = vec![
        r#"L"你好世界""#,
        r#"L"€$¢£¥""#,
        r#"L"hello¢world€test""#,
        r#"L"café naïve résumé""#,
        r#"L"αβγδε""#,
        r#"L"привет мир""#,
    ];

    let results: Vec<_> = test_cases.iter().map(|&src| (src, tokenize(src))).collect();
    insta::assert_yaml_snapshot!(results);
}

/// Test edge cases and special characters in string literals
#[test]
fn test_special_characters_in_strings() {
    let test_cases = vec![
        r#"L"hello \"world\" \\test""#,
        r#"L"café's \"test\" \\value""#,
        r#"L"hello\
world""#,
        r#"""#,
        r#"L"""#,
        r#"u"""#,
        r#"U"""#,
    ];

    let results: Vec<_> = test_cases.iter().map(|&src| (src, tokenize(src))).collect();
    insta::assert_yaml_snapshot!(results);
}

/// Test UTF-8 sequences of different lengths
#[test]
fn test_utf8_sequence_lengths() {
    let test_cases = vec![
        r#"L"abc""#,
        r#"L"café""#,
        r#"L"你好""#,
        r#"L"café你好""#,
    ];

    let results: Vec<_> = test_cases.iter().map(|&src| (src, tokenize(src))).collect();
    insta::assert_yaml_snapshot!(results);
}

/// Test C11 digraphs support
#[test]
fn test_digraphs() {
    let source = "<: :> <% %> %: %:%:";
    let tokens = tokenize(source);
    insta::assert_yaml_snapshot!(tokens);
}
