use crate::ast::StringId;
use crate::lang_options::LangOptions;
use crate::pp::PPConfig;
use crate::pp::{PPTokenFlags, PPTokenKind};
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot, setup_preprocessor_test_with_diagnostics};

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
        ("\"string\"", PPTokenKind::StringLiteral(_)),
        ("'c'", PPTokenKind::CharLiteral(_, _)),
        ("123", PPTokenKind::Number(_)),
    );
}

#[test]
fn test_adjacent_string_literals_not_combined() {
    let source = "\"hello\" \"world\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("\"hello\"", PPTokenKind::StringLiteral(_)),
        ("\"world\"", PPTokenKind::StringLiteral(_)),
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
        ("L'a'", PPTokenKind::CharLiteral(97, _)),
        ("u'b'", PPTokenKind::CharLiteral(98, _)),
        ("U'c'", PPTokenKind::CharLiteral(99, _)),
        ("'\\0'", PPTokenKind::CharLiteral(0, _)),
    );
}

#[test]
fn test_wide_string_literals() {
    let source = "L\"hello\" u\"world\" U\"test\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("L\"hello\"", PPTokenKind::StringLiteral(_)),
        ("u\"world\"", PPTokenKind::StringLiteral(_)),
        ("U\"test\"", PPTokenKind::StringLiteral(_)),
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
        ("1", PPTokenKind::Number(_)),
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
        ("1", PPTokenKind::Number(_)),
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
        test_tokens!(lexer, (expected, PPTokenKind::StringLiteral(_)));
    }
}

#[test]
fn test_hex_float_literal() {
    let source = "0x1p+1 0x1.fp-2 0x1P+1";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("0x1p+1", PPTokenKind::Number(_)),
        ("0x1.fp-2", PPTokenKind::Number(_)),
        ("0x1P+1", PPTokenKind::Number(_)),
    );
}

#[test]
fn test_char_literal_escapes() {
    let source = r"'\1' '\10' '\100' '\x01' '\x0e' '\x10' '\x40'";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(
        lexer,
        (r"'\1'", PPTokenKind::CharLiteral(1, _)),
        (r"'\10'", PPTokenKind::CharLiteral(8, _)),
        (r"'\100'", PPTokenKind::CharLiteral(64, _)),
        (r"'\x01'", PPTokenKind::CharLiteral(1, _)),
        (r"'\x0e'", PPTokenKind::CharLiteral(14, _)),
        (r"'\x10'", PPTokenKind::CharLiteral(16, _)),
        (r"'\x40'", PPTokenKind::CharLiteral(64, _)),
    );
}

// Digraphs
#[test]
fn test_digraphs_basic() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

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
fn test_digraph_hash_starts_line() {
    let source = "%: define";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::Hash);
    assert!(token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

#[test]
fn test_digraph_hashhash_no_starts_line() {
    let source = "%:%:";
    let mut lexer = create_test_pp_lexer(source);
    let token = lexer.next_token().unwrap();
    assert_eq!(token.kind, PPTokenKind::HashHash);
    assert!(!token.flags.contains(PPTokenFlags::STARTS_PP_LINE));
}

// Trigraphs
#[test]
fn test_all_trigraphs() {
    let source = "??= ??( ??/ ??/ ??) ??' ??< ??! ??> ??-";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        ("[", PPTokenKind::LeftBracket),
        ("?", PPTokenKind::Unknown),
        ("?", PPTokenKind::Unknown),
        ("]", PPTokenKind::RightBracket),
        ("^", PPTokenKind::Xor),
        ("{", PPTokenKind::LeftBrace),
        ("|", PPTokenKind::Or),
        ("}", PPTokenKind::RightBrace),
        ("~", PPTokenKind::Tilde),
    );
}

#[test]
fn test_trigraph_line_splice() {
    let source = "abc??/\ndef";
    let mut lexer = create_test_pp_lexer(source);
    let t = lexer.next_token().unwrap();
    assert_eq!(t.kind, PPTokenKind::Identifier(StringId::new("abcdef")));
}

#[test]
fn test_trigraph_in_string() {
    let source = "\"??=\"";
    let mut lexer = create_test_pp_lexer(source);
    let t = lexer.next_token().unwrap();
    assert_eq!(t.kind, PPTokenKind::StringLiteral(StringId::new("\"#\"")));
}

// UCNs
#[test]
fn test_ucn_identifier() {
    let src = r#"
#define \u00E4 10
int x = \u00E4;
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "10"));
}

#[test]
fn test_raw_utf8_identifier() {
    let src = r#"
#define ä 20
int x = ä;
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "20"));
}

#[test]
fn test_ucn_string_literal() {
    let src = r#"
char *s = "\u00E4";
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    let s_token = tokens.iter().find(|t| t.get_text().contains(r#"\u00E4"#));
    assert!(s_token.is_some());
}

#[test]
fn test_utf_macros() {
    let src = r#"
#if __STDC_UTF_16__ == 1
int u16 = 1;
#endif
#if __STDC_UTF_32__ == 1
int u32 = 1;
#endif
"#;
    let config = PPConfig {
        lang_options: LangOptions::c11(),
        ..Default::default()
    };
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, Some(config)).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "u16"));
    assert!(tokens.iter().any(|t| t.get_text() == "u32"));
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
    assert_eq!(token.get_text(), "AB");
}

#[test]
fn test_line_splicing_comprehensive() {
    let source = "hel\\\nlo\nhel\\\nlo\\\nworld\n123\\\n456\n\"hello\\\nworld\"";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(
        lexer,
        ("hello", PPTokenKind::Identifier(_)),
        ("helloworld", PPTokenKind::Identifier(_)),
        ("123456", PPTokenKind::Number(_)),
        ("\"helloworld\"", PPTokenKind::StringLiteral(_)),
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
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
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
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK_WIDE
    - kind: Identifier
      text: OK_UCN
    ");
}

#[test]
fn test_line_splicing_in_skip_whitespace() {
    let source = "   \\\n   identifier";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(lexer, ("identifier", PPTokenKind::Identifier(_)));
}
