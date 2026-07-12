use crate::ast::StringId;
use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::test_tokens;
use crate::tests::pp_common::{assert_pp, create_test_pp_lexer, setup_pp_with_sm_and_diagnostics};

// Lexer basic tests
#[test]
fn test_all_punctuation_tokens() {
    let source = "+ - * / % & | ^ ! ~ < > <= >= == != << >> = += -= *= /= %= &= |= ^= <<= >>= ++ -- -> . ? : , ; ( ) [ ] { } ... && || # ##";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("+", PPTokenKind::Plus),
        ("-", PPTokenKind::Minus),
        ("*", PPTokenKind::Star),
        ("/", PPTokenKind::Slash),
        ("%", PPTokenKind::Percent),
        ("&", PPTokenKind::And),
        ("|", PPTokenKind::Or),
        ("^", PPTokenKind::Xor),
        ("!", PPTokenKind::Not),
        ("~", PPTokenKind::Tilde),
        ("<", PPTokenKind::Less),
        (">", PPTokenKind::Greater),
        ("<=", PPTokenKind::LessEqual),
        (">=", PPTokenKind::GreaterEqual),
        ("==", PPTokenKind::Equal),
        ("!=", PPTokenKind::NotEqual),
        ("<<", PPTokenKind::LeftShift),
        (">>", PPTokenKind::RightShift),
        ("=", PPTokenKind::Assign),
        ("+=", PPTokenKind::PlusAssign),
        ("-=", PPTokenKind::MinusAssign),
        ("*=", PPTokenKind::StarAssign),
        ("/=", PPTokenKind::DivAssign),
        ("%=", PPTokenKind::ModAssign),
        ("&=", PPTokenKind::AndAssign),
        ("|=", PPTokenKind::OrAssign),
        ("^=", PPTokenKind::XorAssign),
        ("<<=", PPTokenKind::LeftShiftAssign),
        (">>=", PPTokenKind::RightShiftAssign),
        ("++", PPTokenKind::Increment),
        ("--", PPTokenKind::Decrement),
        ("->", PPTokenKind::Arrow),
        (".", PPTokenKind::Dot),
        ("?", PPTokenKind::Question),
        (":", PPTokenKind::Colon),
        (",", PPTokenKind::Comma),
        (";", PPTokenKind::Semicolon),
        ("(", PPTokenKind::LeftParen),
        (")", PPTokenKind::RightParen),
        ("[", PPTokenKind::LeftBracket),
        ("]", PPTokenKind::RightBracket),
        ("{", PPTokenKind::LeftBrace),
        ("}", PPTokenKind::RightBrace),
        ("...", PPTokenKind::Ellipsis),
        ("&&", PPTokenKind::LogicAnd),
        ("||", PPTokenKind::LogicOr),
        ("#", PPTokenKind::Hash),
        ("##", PPTokenKind::HashHash),
    );
}

#[test]
fn test_all_keyword_tokens() {
    let source = "if ifdef ifndef elif else endif define undef include line pragma error warning";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("if", PPTokenKind::Identifier(_)),
        ("ifdef", PPTokenKind::Identifier(_)),
        ("ifndef", PPTokenKind::Identifier(_)),
        ("elif", PPTokenKind::Identifier(_)),
        ("else", PPTokenKind::Identifier(_)),
        ("endif", PPTokenKind::Identifier(_)),
        ("define", PPTokenKind::Identifier(_)),
        ("undef", PPTokenKind::Identifier(_)),
        ("include", PPTokenKind::Identifier(_)),
        ("line", PPTokenKind::Identifier(_)),
        ("pragma", PPTokenKind::Identifier(_)),
        ("error", PPTokenKind::Identifier(_)),
        ("warning", PPTokenKind::Identifier(_)),
    );
}

#[test]
fn test_all_literal_tokens() {
    let source = "variable \"string\" 'c' 123";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("variable", PPTokenKind::Identifier(_)),
        ("\"string\"", PPTokenKind::StringLiteral),
        ("'c'", PPTokenKind::CharLiteral(_)),
        ("123", PPTokenKind::Number),
    );
}

#[test]
fn test_adjacent_string_literals_not_combined() {
    let source = "\"hello\" \"world\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("\"hello\"", PPTokenKind::StringLiteral),
        ("\"world\"", PPTokenKind::StringLiteral),
    );
}

#[test]
fn test_hash_starts_pp_line() {
    let source = "#";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

#[test]
fn test_indented_hash_starts_pp_line() {
    let source = "  #";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

#[test]
fn test_hashhash_no_starts_pp_line() {
    let source = "##";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::HashHash);
    assert!(!token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

#[test]
fn test_wide_character_literals() {
    let source = "L'a' u'b' U'c' '\\0'";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("L'a'", PPTokenKind::CharLiteral(97)),
        ("u'b'", PPTokenKind::CharLiteral(98)),
        ("U'c'", PPTokenKind::CharLiteral(99)),
        ("'\\0'", PPTokenKind::CharLiteral(0)),
    );
}

#[test]
fn test_wide_string_literals() {
    let source = "L\"hello\" u\"world\" U\"test\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("L\"hello\"", PPTokenKind::StringLiteral),
        ("u\"world\"", PPTokenKind::StringLiteral),
        ("U\"test\"", PPTokenKind::StringLiteral),
    );
}

#[test]
fn test_eod_token_production() {
    let source = "#define x 1\n";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        ("define", PPTokenKind::Identifier(_)),
        ("x", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number),
        ("", PPTokenKind::Eod),
    );
}

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

    for directive in test_cases {
        let mut lexer = create_test_pp_lexer(directive);
        let tokens: Vec<_> = std::iter::from_fn(|| lexer.next_token()).collect();
        assert!(tokens.len() >= 2);
        assert_eq!(tokens[0].kind, PPTokenKind::Hash);
        assert_eq!(tokens.last().unwrap().kind, PPTokenKind::Eod);
    }
}

#[test]
fn test_eod_at_eof_in_directive() {
    let source = "#define x 1";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        ("define", PPTokenKind::Identifier(_)),
        ("x", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number),
        ("", PPTokenKind::Eod),
    );
}

#[test]
fn test_various_bmp_characters() {
    let test_cases = vec![
        (r#"L"你好世界""#, "L\"你好世界\""),
        (r#"L"€$¢£¥""#, "L\"€$¢£¥\""),
        (r#"L"hello¢world€test""#, "L\"hello¢world€test\""),
        (r#"L"café naïve résumé""#, "L\"café naïve résumé\""),
        (r#"L"αβγδε""#, "L\"αβγδε\""),
        (r#"L"привет мир""#, "L\"привет мир\""),
    ];

    for (source, expected) in test_cases {
        let mut lexer = create_test_pp_lexer(source);
        test_tokens!(lexer, (expected, PPTokenKind::StringLiteral));
    }
}

#[test]
fn test_hex_float_literal() {
    let source = "0x1p+1 0x1.fp-2 0x1P+1";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("0x1p+1", PPTokenKind::Number),
        ("0x1.fp-2", PPTokenKind::Number),
        ("0x1P+1", PPTokenKind::Number),
    );
}

#[test]
fn test_hex_literal_minus_sign_regression() {
    let source = "0xf-1";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("0xf", PPTokenKind::Number),
        ("-", PPTokenKind::Minus),
        ("1", PPTokenKind::Number),
    );
}

#[test]
fn test_char_literal_escapes() {
    let source = r"'\1' '\10' '\100' '\x01' '\x0e' '\x10' '\x40'";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(
        lexer,
        (r"'\1'", PPTokenKind::CharLiteral(1)),
        (r"'\10'", PPTokenKind::CharLiteral(8)),
        (r"'\100'", PPTokenKind::CharLiteral(64)),
        (r"'\x01'", PPTokenKind::CharLiteral(1)),
        (r"'\x0e'", PPTokenKind::CharLiteral(14)),
        (r"'\x10'", PPTokenKind::CharLiteral(16)),
        (r"'\x40'", PPTokenKind::CharLiteral(64)),
    );
}

// UCNs
#[test]
fn test_ucn_identifier() {
    assert_pp(
        r#"
#define \u00E4 10
int x = \u00E4;
        "#,
        "int x = 10;",
    );
}

#[test]
fn test_raw_utf8_identifier() {
    assert_pp(
        r#"
#define ä 20
int x = ä;
        "#,
        "int x = 20;",
    );
}

#[test]
fn test_ucn_string_literal() {
    assert_pp(
        r#"
char *s = "\u00E4";
        "#,
        r#"char *s = "\u00E4";"#,
    );
}

#[test]
fn test_invalid_ucn() {
    let src = r#"const char* s = "\uZZZZ";"#; // malformed UCN in string literal
    let (_, _, diags) = setup_pp_with_sm_and_diagnostics(src, None).unwrap();
    assert!(!diags.is_empty(), "Expected diagnostics for invalid UCN");
}

#[test]
fn test_utf_macros() {
    let src = r#"
#if __STDC_UTF_16__ == 1
OK
#endif
#if __STDC_UTF_32__ == 1
OK
#endif
"#;
    assert_pp(src, "OK\nOK");
}

// Line Splicing
#[test]
fn test_lexer_line_splicing_with_whitespace() {
    let source = "VAL\\ \nUE";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Identifier(StringId::new("VALUE")));
}

#[test]
fn test_consecutive_splices() {
    let source = "A\\\n\\\nB";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(lexer.get_token_text(&token), "AB");
}

#[test]
fn test_line_splicing_comprehensive() {
    let source = "hel\\\nlo\nhel\\\nlo\\\nworld\n123\\\n456\n\"hello\\\nworld\"";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(
        lexer,
        ("hello", PPTokenKind::Identifier(_)),
        ("helloworld", PPTokenKind::Identifier(_)),
        ("123456", PPTokenKind::Number),
        ("\"helloworld\"", PPTokenKind::StringLiteral),
    );
}

#[test]
fn test_preprocessor_multiline_directive_with_splice() {
    let src = r#"
#define FOO 1
#if FOO \
    && 1
OK
#else
FAIL
#endif
"#;
    assert_pp(src, "OK");
}

#[test]
fn test_pp_wide_char_arithmetic() {
    let src = r#"
#if L'\u0400' == 0x0400
OK_WIDE
#else
FAIL_WIDE
#endif

#if '\u00FF' == 255
OK_UCN
#else
FAIL_UCN
#endif
"#;
    assert_pp(src, "OK_WIDE\nOK_UCN");
}

#[test]
fn test_line_splicing_in_skip_whitespace() {
    let source = "   \\\n   identifier";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("identifier", PPTokenKind::Identifier(_)));
}

#[test]
fn test_u8_string_literal() {
    let source = "u8\"hello\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("u8\"hello\"", PPTokenKind::StringLiteral),);
}

#[test]
fn test_u8_string_literal_with_escapes() {
    let source = "u8\"hello\\nworld\\u00E4\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("u8\"hello\\nworld\\u00E4\"", PPTokenKind::StringLiteral),);
}

#[test]
fn test_not_u8_literal() {
    let source = "u8+1";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("u8", PPTokenKind::Identifier(_)),
        ("+", PPTokenKind::Plus),
        ("1", PPTokenKind::Number),
    );
}

#[test]
fn test_u8_char_literal() {
    // C23 u8'a' should be lexed as a single char literal token
    let source = "u8'a'";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("u8'a'", PPTokenKind::CharLiteral(97)),);
}
