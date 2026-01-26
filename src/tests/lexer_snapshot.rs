use crate::lexer::TokenKind;
use crate::tests::test_utils;
use crate::driver::artifact::CompilePhase;
use serde::Serialize;

#[derive(Debug, Serialize)]
enum SnapshotTokenKind {
    IntegerConstant(i64),
    FloatConstant(f64),
    CharacterConstant(u8),
    StringLiteral(String),
    Identifier(String),
    Simple(String),
}

impl From<TokenKind> for SnapshotTokenKind {
    fn from(kind: TokenKind) -> Self {
        match kind {
            TokenKind::IntegerConstant(i) => SnapshotTokenKind::IntegerConstant(i),
            TokenKind::FloatConstant(f) => SnapshotTokenKind::FloatConstant(f),
            TokenKind::CharacterConstant(c) => SnapshotTokenKind::CharacterConstant(c),
            TokenKind::StringLiteral(id) => SnapshotTokenKind::StringLiteral(id.as_str().to_string()),
            TokenKind::Identifier(id) => SnapshotTokenKind::Identifier(id.as_str().to_string()),
            // For all other tokens, use their Debug representation
            _ => SnapshotTokenKind::Simple(format!("{:?}", kind)),
        }
    }
}

fn setup_lexer(source: &str) -> Vec<SnapshotTokenKind> {
    let phase = CompilePhase::Lex;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let tokens = artifact.lexed.clone().unwrap();

    tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, TokenKind::EndOfFile))
        .map(|t| SnapshotTokenKind::from(t.kind))
        .collect()
}

#[test]
fn test_keywords() {
    let source = "auto break case char const continue default do double else enum extern float for goto if inline int long register restrict return short signed sizeof static struct switch typedef union unsigned void volatile while _Alignas _Alignof _Atomic _Bool _Complex _Generic _Noreturn _Static_assert _Thread_local __attribute__ __builtin_va_arg";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_operators() {
    let source = "+ - * / % ++ -- ~ ! & | ^ << >> && || < > <= >= == != = += -= *= /= %= &= |= ^= <<= >>= . -> ? : , ; ...";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_punctuators() {
    let source = "[ ] ( ) { }";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_integer_literals() {
    let source = "0 123 0x123 077 1u 1l 1ul 1lu 1ll 1ull 1llu 0x1u 0x1l 0x1ul 0x1lu 0x1ll 0x1ull 0x1llu";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_float_literals() {
    let source = "0. 1. .5 1.5 1.5e10 1.5e-10 1.5f 1.5L 0x1.2p3 0x1.2p-3 0x1p3";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_char_literals() {
    let source = "'a' '\\n' '\\t' '\\'' '\"' '\\?' '\\\\' '\\0' '\\xff' '\\123'";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_string_literals() {
    let source = "\"hello\" \"hello\\nworld\" \"\\\"quoted\\\"\"";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_string_concatenation() {
    let source = "\"hello\" \" \" \"world\"";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_string_concatenation_with_escapes() {
    let source = "\"hello\\n\" \"world\"";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_identifiers() {
    let source = "foo bar _baz foo123";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_mixed() {
    let source = "int main() { return 0; }";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_unknown_tokens() {
    let source = "$ @ `";
    let tokens = setup_lexer(source);
    insta::assert_yaml_snapshot!(tokens);
}
