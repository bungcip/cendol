use crate::ast::NameId;
use crate::ast::literal::{CharPrefix, FloatSuffix, IntSuffix, LitRef, LitVal, StrPrefix};
use crate::lang_options::CStandard;
use crate::parser::Lexer;
use crate::parser::lexer::TokenKind;
use crate::pp::Preprocessor;
use crate::pp::types::PPConfig;
use crate::source_manager::FileKind;
use crate::tests::test_utils::setup_sm_and_de;

fn setup_lexer(input: &str) -> Vec<TokenKind> {
    let (mut sm, mut de) = setup_sm_and_de();
    let file_id = sm.add_buffer(input.as_bytes().to_vec(), "test.c", None, FileKind::Synthetic);
    let config = PPConfig::default();
    let mut pp = Preprocessor::new(&mut sm, &mut de, &config);
    pp.start_processing(file_id);
    let mut lexer = Lexer::new(&mut pp, CStandard::C23);
    let mut tokens = Vec::new();
    while let Ok(Some(token)) = lexer.next_token() {
        tokens.push(token.kind);
        if token.kind == TokenKind::EndOfFile {
            break;
        }
    }
    tokens
}

fn assert_literal(input: &str, expected: LitVal) {
    let tokens = setup_lexer(input);
    assert!(!tokens.is_empty(), "No tokens returned for input: {}", input);
    if let TokenKind::Literal(lit) = &tokens[0] {
        assert_eq!(lit.get_val(), expected, "Literal mismatch for {}", input);
    } else {
        panic!("Expected Literal for {}, got {:?}", input, tokens[0]);
    }
}

#[test]
fn test_keywords() {
    let tokens = setup_lexer("int return void _Generic");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Int,
            TokenKind::Return,
            TokenKind::Void,
            TokenKind::Generic,
            TokenKind::EndOfFile
        ]
    );
}

#[test]
fn test_operators() {
    let tokens = setup_lexer(
        "+ - * / % ++ -- & | ^ ! ~ << >> < > <= >= == != = += -= *= /= %= &= |= ^= <<= >>= && || -> . ? : , ; ... ( ) [ ] { }",
    );
    assert_eq!(
        tokens,
        vec![
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Star,
            TokenKind::Slash,
            TokenKind::Percent,
            TokenKind::Increment,
            TokenKind::Decrement,
            TokenKind::And,
            TokenKind::Or,
            TokenKind::Xor,
            TokenKind::Not,
            TokenKind::Tilde,
            TokenKind::LeftShift,
            TokenKind::RightShift,
            TokenKind::Less,
            TokenKind::Greater,
            TokenKind::LessEqual,
            TokenKind::GreaterEqual,
            TokenKind::Equal,
            TokenKind::NotEqual,
            TokenKind::Assign,
            TokenKind::PlusAssign,
            TokenKind::MinusAssign,
            TokenKind::StarAssign,
            TokenKind::DivAssign,
            TokenKind::ModAssign,
            TokenKind::AndAssign,
            TokenKind::OrAssign,
            TokenKind::XorAssign,
            TokenKind::LeftShiftAssign,
            TokenKind::RightShiftAssign,
            TokenKind::LogicAnd,
            TokenKind::LogicOr,
            TokenKind::Arrow,
            TokenKind::Dot,
            TokenKind::Question,
            TokenKind::Colon,
            TokenKind::Comma,
            TokenKind::Semicolon,
            TokenKind::Ellipsis,
            TokenKind::LeftParen,
            TokenKind::RightParen,
            TokenKind::LeftBracket,
            TokenKind::RightBracket,
            TokenKind::LeftBrace,
            TokenKind::RightBrace,
            TokenKind::EndOfFile,
        ]
    );
}

#[test]
fn test_integer_literals() {
    let cases = [
        (
            "42",
            LitVal::Int {
                value: 42,
                suffix: IntSuffix::None,
                radix: 10,
            },
        ),
        (
            "0x1A",
            LitVal::Int {
                value: 26,
                suffix: IntSuffix::None,
                radix: 16,
            },
        ),
        (
            "077u",
            LitVal::Int {
                value: 63,
                suffix: IntSuffix::U,
                radix: 8,
            },
        ),
        (
            "123llu",
            LitVal::Int {
                value: 123,
                suffix: IntSuffix::ULL,
                radix: 10,
            },
        ),
        (
            "0b1010",
            LitVal::Int {
                value: 10,
                suffix: IntSuffix::None,
                radix: 2,
            },
        ),
        // C23 separators
        (
            "1'234",
            LitVal::Int {
                value: 1234,
                suffix: IntSuffix::None,
                radix: 10,
            },
        ),
        (
            "0xAB'CD",
            LitVal::Int {
                value: 0xABCD,
                suffix: IntSuffix::None,
                radix: 16,
            },
        ),
        (
            "0b1'010",
            LitVal::Int {
                value: 10,
                suffix: IntSuffix::None,
                radix: 2,
            },
        ),
        (
            "0'777",
            LitVal::Int {
                value: 0o777,
                suffix: IntSuffix::None,
                radix: 8,
            },
        ),
    ];
    for (input, expected) in cases {
        assert_literal(input, expected);
    }
}

#[test]
fn test_float_literals() {
    let cases = [
        ("1.23", LitVal::from_f64(1.23, FloatSuffix::None)),
        ("1.0f", LitVal::from_f64(1.0, FloatSuffix::F)),
        ("2.0L", LitVal::from_f64(2.0, FloatSuffix::L)),
        ("1e10", LitVal::from_f64(1e10, FloatSuffix::None)),
        ("0x1p-10", LitVal::from_f64(0.0009765625, FloatSuffix::None)),
        // C23 separators
        ("1'234.5", LitVal::from_f64(1234.5, FloatSuffix::None)),
        ("0x1'A.5p2", LitVal::from_f64(105.25, FloatSuffix::None)),
    ];
    for (input, expected) in cases {
        assert_literal(input, expected);
    }
}

#[test]
fn test_char_literals() {
    let cases = [
        ("'a'", LitVal::Char(97, CharPrefix::None)),
        ("L'b'", LitVal::Char(98, CharPrefix::Wide)),
        (r"'\n'", LitVal::Char(10, CharPrefix::None)),
    ];
    for (input, expected) in cases {
        assert_literal(input, expected);
    }
}

#[test]
fn test_string_literals() {
    let cases = [
        (
            r#""hello""#,
            LitVal::String {
                value: "hello".into(),
                prefix: StrPrefix::None,
            },
        ),
        (
            r#"L"world""#,
            LitVal::String {
                value: "world".into(),
                prefix: StrPrefix::Wide,
            },
        ),
        (
            r#"u8"utf8""#,
            LitVal::String {
                value: "utf8".into(),
                prefix: StrPrefix::Utf8,
            },
        ),
        (
            r#"u"utf16""#,
            LitVal::String {
                value: "utf16".into(),
                prefix: StrPrefix::Utf16,
            },
        ),
    ];
    for (input, expected) in cases {
        assert_literal(input, expected);
    }
}

#[test]
fn test_lexer_display() {
    use crate::parser::lexer::TokenKind::*;

    let kinds = vec![
        Literal(LitRef::from_int(1, IntSuffix::None, 10)),
        Literal(LitRef::from_f64(1.0, FloatSuffix::None)),
        Literal(LitRef::from_char(97, CharPrefix::None)),
        Literal(LitRef::from_string(std::borrow::Cow::Borrowed("test"), StrPrefix::None)),
        Identifier(NameId::new("test")),
        Int,
        Return,
        Plus,
        Equal,
        EndOfFile,
    ];

    for kind in kinds {
        let _ = format!("{:?}", kind);
    }
}

#[test]
fn test_identifier_boundary_cases() {
    let tokens = setup_lexer("l2?");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Identifier(NameId::new("l2")),
            TokenKind::Question,
            TokenKind::EndOfFile
        ]
    );

    let tokens = setup_lexer("l2\\\n?");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Identifier(NameId::new("l2")),
            TokenKind::Question,
            TokenKind::EndOfFile
        ]
    );
}
