use crate::pp::pp_lexer::PPLexer;
use crate::pp::PPTokenFlags;
use crate::source_manager::SourceId;

/// Helper function to create a PPLexer for testing
fn create_test_pp_lexer(source: &str) -> PPLexer {
    let source_id = SourceId::new(1);
    let buffer = source.as_bytes().to_vec();
    PPLexer::new(source_id, buffer)
}

#[derive(serde::Serialize)]
struct SnapshotPPToken {
    kind: String,
    text: String,
    flags: Vec<String>,
}

fn snapshot_pp_lexer(source: &str) -> Vec<SnapshotPPToken> {
    let mut lexer = create_test_pp_lexer(source);
    let mut tokens = Vec::new();
    while let Some(token) = lexer.next_token() {
        let mut flags = Vec::new();
        if token.flags.contains(PPTokenFlags::LEADING_SPACE) {
            flags.push("LEADING_SPACE".to_string());
        }
        if token.flags.contains(PPTokenFlags::STARTS_PP_LINE) {
            flags.push("STARTS_PP_LINE".to_string());
        }
        if token.flags.contains(PPTokenFlags::NEEDS_CLEANUP) {
            flags.push("NEEDS_CLEANUP".to_string());
        }
        if token.flags.contains(PPTokenFlags::MACRO_EXPANDED) {
            flags.push("MACRO_EXPANDED".to_string());
        }

        tokens.push(SnapshotPPToken {
            kind: format!("{:?}", token.kind),
            text: token.get_text().to_string(),
            flags,
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

    insta::assert_yaml_snapshot!(vec![
        snapshot_pp_lexer(source1),
        snapshot_pp_lexer(source2),
        snapshot_pp_lexer(source3),
        snapshot_pp_lexer(source4),
        snapshot_pp_lexer(source5),
        snapshot_pp_lexer(source6),
        snapshot_pp_lexer(source7),
    ]);

    // Test next_char with line splicing
    let source = "a\\
b";
    let mut lexer = create_test_pp_lexer(source);
    assert_eq!(lexer.next_char(), Some(b'a'));
    assert_eq!(lexer.next_char(), Some(b'b'));
    assert_eq!(lexer.next_char(), None);

    // Test peek_char with line splicing
    let source = "a\\
b";
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
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that PPLexer can produce all keyword tokens
#[test]
fn test_all_keyword_tokens() {
    let source = "if ifdef ifndef elif else endif define undef include line pragma error warning";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that PPLexer can produce all literal tokens
#[test]
fn test_all_literal_tokens() {
    let source = "variable \"string\" 'c' 123";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that adjacent string literals are not combined in preprocessor stage
#[test]
fn test_adjacent_string_literals_not_combined() {
    let source = "\"hello\" \"world\"";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that line splicing is handled correctly in skip_whitespace_and_comments
/// This prevents regression of the bug where backslash-newline in macro definitions
/// caused Unknown tokens due to improper splicing in whitespace skipping.
#[test]
fn test_line_splicing_in_skip_whitespace() {
    // This simulates the scenario in macro definitions where backslash-newline
    // appears after skipping initial whitespace, and ensures no Unknown tokens
    let source = "   \\\n   identifier";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that single # tokens always have STARTS_PP_LINE flag set
#[test]
fn test_hash_starts_pp_line() {
    let source = "#";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that indented # tokens have STARTS_PP_LINE flag set
#[test]
fn test_indented_hash_starts_pp_line() {
    let source = "  #";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that ## tokens do not have STARTS_PP_LINE flag set
#[test]
fn test_hashhash_no_starts_pp_line() {
    let source = "##";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test wide character literals with L, u, U prefixes
#[test]
fn test_wide_character_literals() {
    let source = "L'a' u'b' U'c' '\\0'";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test wide string literals with L, u, U prefixes
#[test]
fn test_wide_string_literals() {
    let source = "L\"hello\" u\"world\" U\"test\"";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that Eod (End of Directive) tokens are produced at the end of directive lines
#[test]
fn test_eod_token_production() {
    // Test simple directive
    let source = "#define x 1\n";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test that Eod tokens are produced for various directive types
#[test]
fn test_eod_for_various_directives() {
    // Test various directive types that should all end with Eod
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

    let results: Vec<_> = test_cases
        .iter()
        .map(|s| snapshot_pp_lexer(s))
        .collect();

    insta::assert_yaml_snapshot!(results);
}

/// Test that Eod is produced at EOF when in directive line (clang compatibility)
#[test]
fn test_eod_at_eof_in_directive() {
    // Directive at end of file without newline
    let source = "#define x 1";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test string literals with BMP (Basic Multilingual Plane) Unicode characters
#[test]
fn test_bmp_unicode_string_literals() {
    // Test the specific target string with mixed ASCII and BMP characters
    let source = r#"L"hello$$你好¢¢世界€€world""#;
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

/// Test various BMP character types in string literals
#[test]
fn test_various_bmp_characters() {
    let test_cases = vec![
        // Chinese characters (3-byte UTF-8 sequences)
        (r#"L"你好世界""#, "L\"你好世界\""),
        // Currency symbols (2-byte and 3-byte UTF-8 sequences)
        (r#"L"€$¢£¥""#, "L\"€$¢£¥\""),
        // Mixed ASCII and BMP
        (r#"L"hello¢world€test""#, "L\"hello¢world€test\""),
        // Extended Latin characters (2-byte UTF-8 sequences)
        (r#"L"café naïve résumé""#, "L\"café naïve résumé\""),
        // Greek characters (2-byte UTF-8 sequences)
        (r#"L"αβγδε""#, "L\"αβγδε\""),
        // Cyrillic characters (2-byte UTF-8 sequences)
        (r#"L"привет мир""#, "L\"привет мир\""),
    ];

    let results: Vec<_> = test_cases
        .iter()
        .map(|(src, _)| snapshot_pp_lexer(src))
        .collect();
    insta::assert_yaml_snapshot!(results);
}

/// Test edge cases and special characters in string literals
#[test]
fn test_special_characters_in_strings() {
    // Test with various special characters that might cause issues
    let test_cases = vec![
        // Regular ASCII with quotes and backslashes
        r#"L"hello \"world\" \\test""#,
        // Mixed quotes and special chars
        r#"L"café's \"test\" \\value""#,
        // String with newlines (line splicing) - should splice the newline
        "L\"hello\\\nworld\"",
        // String with all types of quotes
        r#"""#,
        r#"L"""#,
        r#"u"""#,
        r#"U"""#,
    ];

    let results: Vec<_> = test_cases
        .iter()
        .map(|src| snapshot_pp_lexer(src))
        .collect();

    insta::assert_yaml_snapshot!(results);
}

/// Test UTF-8 sequences of different lengths
#[test]
fn test_utf8_sequence_lengths() {
    // 1-byte sequence (ASCII)
    let source1 = r#"L"abc""#;
    // 2-byte sequence (extended ASCII)
    let source2 = r#"L"café""#;
    // 3-byte sequence (BMP Chinese)
    let source3 = r#"L"你好""#;
    // Mixed sequences
    let source4 = r#"L"café你好""#;

    insta::assert_yaml_snapshot!(vec![
        snapshot_pp_lexer(source1),
        snapshot_pp_lexer(source2),
        snapshot_pp_lexer(source3),
        snapshot_pp_lexer(source4)
    ]);
}

#[test]
fn test_consecutive_splices() {
    // Two backslash-newlines immediately following each other
    let source = "A\\\n\\\nB";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}

#[test]
fn test_consecutive_splices_with_cr() {
    let source = "A\\\r\n\\\r\nB";
    insta::assert_yaml_snapshot!(snapshot_pp_lexer(source));
}
