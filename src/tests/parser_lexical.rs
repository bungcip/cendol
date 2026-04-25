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

macro_rules! check_tok {
    ($input:expr, $kind:expr) => {
        let tokens = setup_lexer($input);
        // We expect the kind + EndOfFile
        assert!(
            tokens.len() >= 1,
            "Expected at least 1 token for {}, got {:?}",
            $input,
            tokens
        );
        assert_eq!(tokens[0], $kind, "Token mismatch for {}", $input);
    };
}

macro_rules! check_lit {
    ($input:expr, $val:expr) => {
        let tokens = setup_lexer($input);
        assert!(tokens.len() >= 1);
        if let TokenKind::Literal(lit) = &tokens[0] {
            assert_eq!(lit.get_val(), $val, "Literal mismatch for {}", $input);
        } else {
            panic!("Expected Literal for {}, got {:?}", $input, tokens[0]);
        }
    };
}

#[test]
fn test_keywords() {
    check_tok!("int", TokenKind::Int);
    check_tok!("return", TokenKind::Return);
    check_tok!("void", TokenKind::Void);
    check_tok!("_Generic", TokenKind::Generic);
}

#[test]
fn test_operators() {
    // Arithmetic
    check_tok!("+", TokenKind::Plus);
    check_tok!("-", TokenKind::Minus);
    check_tok!("*", TokenKind::Star);
    check_tok!("/", TokenKind::Slash);
    check_tok!("%", TokenKind::Percent);
    check_tok!("++", TokenKind::Increment);
    check_tok!("--", TokenKind::Decrement);

    // Bitwise
    check_tok!("&", TokenKind::And);
    check_tok!("|", TokenKind::Or);
    check_tok!("^", TokenKind::Xor);
    check_tok!("!", TokenKind::Not);
    check_tok!("~", TokenKind::Tilde);
    check_tok!("<<", TokenKind::LeftShift);
    check_tok!(">>", TokenKind::RightShift);

    // Comparison
    check_tok!("<", TokenKind::Less);
    check_tok!(">", TokenKind::Greater);
    check_tok!("<=", TokenKind::LessEqual);
    check_tok!(">=", TokenKind::GreaterEqual);
    check_tok!("==", TokenKind::Equal);
    check_tok!("!=", TokenKind::NotEqual);

    // Assignment
    check_tok!("=", TokenKind::Assign);
    check_tok!("+=", TokenKind::PlusAssign);
    check_tok!("-=", TokenKind::MinusAssign);
    check_tok!("*=", TokenKind::StarAssign);
    check_tok!("/=", TokenKind::DivAssign);
    check_tok!("%=", TokenKind::ModAssign);
    check_tok!("&=", TokenKind::AndAssign);
    check_tok!("|=", TokenKind::OrAssign);
    check_tok!("^=", TokenKind::XorAssign);
    check_tok!("<<=", TokenKind::LeftShiftAssign);
    check_tok!(">>=", TokenKind::RightShiftAssign);

    // Logical
    check_tok!("&&", TokenKind::LogicAnd);
    check_tok!("||", TokenKind::LogicOr);

    // Member access and others
    check_tok!("->", TokenKind::Arrow);
    check_tok!(".", TokenKind::Dot);
    check_tok!("?", TokenKind::Question);
    check_tok!(":", TokenKind::Colon);
    check_tok!(",", TokenKind::Comma);
    check_tok!(";", TokenKind::Semicolon);
    check_tok!("...", TokenKind::Ellipsis);

    // Brackets
    check_tok!("(", TokenKind::LeftParen);
    check_tok!(")", TokenKind::RightParen);
    check_tok!("[", TokenKind::LeftBracket);
    check_tok!("]", TokenKind::RightBracket);
    check_tok!("{", TokenKind::LeftBrace);
    check_tok!("}", TokenKind::RightBrace);
}

#[test]
#[rustfmt::skip]
fn test_integer_literals() {
    check_lit!("42", LitVal::Int { value: 42, suffix: IntSuffix::None, radix: 10 });
    check_lit!("0x1A", LitVal::Int { value: 26, suffix: IntSuffix::None, radix: 16 });
    check_lit!("077u", LitVal::Int { value: 63, suffix: IntSuffix::U, radix: 8 });
    check_lit!("123llu", LitVal::Int { value: 123, suffix: IntSuffix::ULL, radix: 10 });
    check_lit!("0b1010", LitVal::Int { value: 10, suffix: IntSuffix::None, radix: 2 });
    // C23 separators
    check_lit!("1'234", LitVal::Int { value: 1234, suffix: IntSuffix::None, radix: 10 });
    check_lit!("0xAB'CD", LitVal::Int { value: 0xABCD, suffix: IntSuffix::None, radix: 16 });
    check_lit!("0b1'010", LitVal::Int { value: 10, suffix: IntSuffix::None, radix: 2 });
    check_lit!("0'777", LitVal::Int { value: 0o777, suffix: IntSuffix::None, radix: 8 });
}

#[test]
#[rustfmt::skip]
fn test_float_literals() {
    check_lit!("1.23", LitVal::from_f64(1.23, FloatSuffix::None));
    check_lit!("1.0f", LitVal::from_f64(1.0, FloatSuffix::F));
    check_lit!("2.0L", LitVal::from_f64(2.0, FloatSuffix::L));
    check_lit!("1e10", LitVal::from_f64(1e10, FloatSuffix::None));
    check_lit!("0x1p-10", LitVal::from_f64(0.0009765625, FloatSuffix::None));
    // C23 separators
    check_lit!("1'234.5", LitVal::from_f64(1234.5, FloatSuffix::None));
    check_lit!("0x1'A.5p2", LitVal::from_f64(105.25, FloatSuffix::None));
}

#[test]
fn test_char_literals() {
    check_lit!("'a'", LitVal::Char(97, CharPrefix::None));
    check_lit!("L'b'", LitVal::Char(98, CharPrefix::Wide));
    check_lit!(r"'\n'", LitVal::Char(10, CharPrefix::None));
}

#[test]
fn test_string_literals() {
    check_lit!(
        r#""hello""#,
        LitVal::String {
            value: "hello".into(),
            prefix: StrPrefix::None
        }
    );
    check_lit!(
        r#"L"world""#,
        LitVal::String {
            value: "world".into(),
            prefix: StrPrefix::Wide
        }
    );
}

#[test]
fn test_lexer_display() {
    use crate::parser::lexer::TokenKind::*;

    let kinds = vec![
        Literal(LitRef::from_int(1, IntSuffix::None, 10)),
        Literal(LitRef::from_f64(1.0, FloatSuffix::None)),
        Literal(LitRef::from_char(97, CharPrefix::None)),
        Literal(LitRef::from_string("test", StrPrefix::None)),
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
