use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::create_test_pp_lexer;

#[test]
fn test_u8_string_literal() {
    let source = "u8\"hello\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("u8\"hello\"", PPTokenKind::StringLiteral(_)),);
}

#[test]
fn test_u8_string_literal_with_escapes() {
    let source = "u8\"hello\\nworld\\u00E4\"";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(lexer, ("u8\"hello\\nworld\\u00E4\"", PPTokenKind::StringLiteral(_)),);
}

#[test]
fn test_not_u8_literal() {
    let source = "u8+1";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("u8", PPTokenKind::Identifier(_)),
        ("+", PPTokenKind::Plus),
        ("1", PPTokenKind::Number(_)),
    );
}

#[test]
fn test_u8_char_literal_not_supported_in_c11() {
    // C11 doesn't have u8'a', so it should be lexed as Identifier(u8) then CharLiteral('a')
    let source = "u8'a'";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("u8", PPTokenKind::Identifier(_)),
        ("'a'", PPTokenKind::CharLiteral(97, _)),
    );
}
