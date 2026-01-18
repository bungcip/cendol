use crate::pp::pp_lexer::PPLexer;
use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::source_manager::SourceId;
use serde::Serialize;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

#[derive(Serialize)]
struct SnapshotPPToken {
    kind: PPTokenKind,
    flags: PPTokenFlags,
    text: String,
}

fn setup_pp_lexer_snapshot(source: &str) -> Vec<SnapshotPPToken> {
    let mut lexer = create_test_pp_lexer(source);
    let mut tokens = Vec::new();
    while let Some(token) = lexer.next_token() {
        tokens.push(SnapshotPPToken {
            kind: token.kind,
            flags: token.flags,
            text: token.get_text().to_string(),
        });
    }
    tokens
}

/// Test comprehensive line splicing scenarios
#[test]
fn test_line_splicing_comprehensive() {
    // Basic line splicing
    let source1 = "hel\\
lo
hel\\
lo\\
world
123\\
456
\"hello\\
world\"
";

    // Line splicing with whitespace
    let source2 = "hel  \\
    lo";

    // No line splicing (regular newline)
    let source3 = "hello\nworld";

    // Line splicing at end of buffer
    let source4 = "test\\";

    // Line splicing with CRLF
    let source5 = "hel\\\r\nlo";

    // Line splicing with CR
    let source6 = "hel\\\rlo";

    // Line splicing with CR at end
    let source7 = "test\\\r";

    // Consecutive splices
    let source8 = "A\\\n\\\nB";

    // Consecutive splices with CR
    let source9 = "A\\\r\n\\\r\nB";

    insta::assert_yaml_snapshot!(vec![
        ("basic", setup_pp_lexer_snapshot(source1)),
        ("whitespace", setup_pp_lexer_snapshot(source2)),
        ("regular_newline", setup_pp_lexer_snapshot(source3)),
        ("end_buffer", setup_pp_lexer_snapshot(source4)),
        ("crlf", setup_pp_lexer_snapshot(source5)),
        ("cr", setup_pp_lexer_snapshot(source6)),
        ("cr_end", setup_pp_lexer_snapshot(source7)),
        ("consecutive", setup_pp_lexer_snapshot(source8)),
        ("consecutive_cr", setup_pp_lexer_snapshot(source9)),
    ]);
}

#[test]
fn test_line_splicing_iterators() {
    // Test next_char with line splicing
    let source = "a\\
b";
    let mut lexer = create_test_pp_lexer(source);
    let mut chars = Vec::new();
    while let Some(c) = lexer.next_char() {
        chars.push(c as char);
    }
    assert_eq!(chars, vec!['a', 'b']);

    // Test peek_char with line splicing
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
    let tokens = setup_pp_lexer_snapshot(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that PPLexer can produce all keyword tokens
#[test]
fn test_all_keyword_tokens() {
    let source = "if ifdef ifndef elif else endif define undef include line pragma error warning";
    let tokens = setup_pp_lexer_snapshot(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that PPLexer can produce all literal tokens
#[test]
fn test_all_literal_tokens() {
    let source = "variable \"string\" 'c' 123";
    let tokens = setup_pp_lexer_snapshot(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that adjacent string literals are not combined in preprocessor stage
#[test]
fn test_adjacent_string_literals_not_combined() {
    let source = "\"hello\" \"world\"";
    let tokens = setup_pp_lexer_snapshot(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that line splicing is handled correctly in skip_whitespace_and_comments
#[test]
fn test_line_splicing_in_skip_whitespace() {
    let source = "   \\\n   identifier";
    let tokens = setup_pp_lexer_snapshot(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test flag setting behavior
#[test]
fn test_flags() {
    let single_hash = "#";
    let indented_hash = "  #";
    let hash_hash = "##";

    insta::assert_yaml_snapshot!(vec![
        ("hash", setup_pp_lexer_snapshot(single_hash)),
        ("indented_hash", setup_pp_lexer_snapshot(indented_hash)),
        ("hash_hash", setup_pp_lexer_snapshot(hash_hash)),
    ]);
}

/// Test wide character literals with L, u, U prefixes
#[test]
fn test_wide_character_literals() {
    let source = "L'a' u'b' U'c' '\\0'";
    let tokens = setup_pp_lexer_snapshot(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test wide string literals with L, u, U prefixes
#[test]
fn test_wide_string_literals() {
    let source = "L\"hello\" u\"world\" U\"test\"";
    let tokens = setup_pp_lexer_snapshot(source);
    insta::assert_yaml_snapshot!(tokens);
}

/// Test that Eod (End of Directive) tokens are produced
#[test]
fn test_eod_token_production() {
    let simple = "#define x 1\n";
    let eof_directive = "#define x 1"; // No newline at end

    let various = vec![
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

    let mut results = vec![
        ("simple", setup_pp_lexer_snapshot(simple)),
        ("eof_directive", setup_pp_lexer_snapshot(eof_directive)),
    ];

    for v in various {
        results.push((v, setup_pp_lexer_snapshot(v)));
    }

    insta::assert_yaml_snapshot!(results);
}

/// Test string literals with BMP (Basic Multilingual Plane) Unicode characters
#[test]
fn test_unicode_strings() {
    let mixed = r#"L"hello$$你好¢¢世界€€world""#;

    let cases = vec![
        r#"L"你好世界""#,
        r#"L"€$¢£¥""#,
        r#"L"hello¢world€test""#,
        r#"L"café naïve résumé""#,
        r#"L"αβγδε""#,
        r#"L"привет мир""#,
    ];

    let mut results = vec![("mixed", setup_pp_lexer_snapshot(mixed))];
    for c in cases {
        results.push((c, setup_pp_lexer_snapshot(c)));
    }

    insta::assert_yaml_snapshot!(results);
}

/// Test edge cases and special characters in string literals
#[test]
fn test_special_characters_in_strings() {
    let cases = vec![
        r#"L"hello \"world\" \\test""#,
        r#"L"café's \"test\" \\value""#,
        // String with newlines (line splicing)
        r#"L"hello\
world""#,
        r#"""#,
        r#"L"""#,
        r#"u"""#,
        r#"U"""#,
    ];

    let mut results = Vec::new();
    for c in cases {
        results.push((c, setup_pp_lexer_snapshot(c)));
    }

    insta::assert_yaml_snapshot!(results);
}

/// Test UTF-8 sequences of different lengths
#[test]
fn test_utf8_sequence_lengths() {
    let cases = vec![
        r#"L"abc""#,
        r#"L"café""#,
        r#"L"你好""#,
        r#"L"café你好""#,
    ];

    let mut results = Vec::new();
    for c in cases {
        results.push((c, setup_pp_lexer_snapshot(c)));
    }

    insta::assert_yaml_snapshot!(results);
}
