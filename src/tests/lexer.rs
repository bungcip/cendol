use crate::driver::artifact::CompilePhase;
use crate::lexer::*;
use crate::tests::test_utils;

/// Helper function to test lexing from string to TokenKind
/// This tests the full pipeline: string -> PPToken -> TokenKind
fn setup_lexer(input: &str) -> Vec<TokenKind> {
    setup_lexer_with_eof(input, false)
}

/// Helper function to test lexing from string to TokenKind, optionally including EndOfFile
fn setup_lexer_with_eof(source: &str, include_eof: bool) -> Vec<TokenKind> {
    let phase = CompilePhase::Lex;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let tokens = artifact.lexed.clone().unwrap();

    if include_eof {
        tokens.into_iter().map(|t| t.kind).collect()
    } else {
        tokens
            .into_iter()
            .filter(|t| !matches!(t.kind, TokenKind::EndOfFile))
            .map(|t| t.kind)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c11_keywords() {
        // Test all C11 keywords including C11-specific ones
        let keywords = r#"
            auto break case char const continue default do
            double else enum extern float for goto if
            inline int long register restrict return short
            signed sizeof static struct switch typedef union
            unsigned void volatile while
            _Alignas _Alignof _Atomic _Bool _Complex _Generic
            _Noreturn _Static_assert _Thread_local
            __attribute__ __attribute
            __builtin_va_arg __builtin_va_start __builtin_va_end __builtin_va_copy
        "#;

        let tokens = setup_lexer(keywords);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_operators_and_punctuation() {
        // We separate them with spaces to avoid creating unintended compound tokens (like + and + becoming ++)
        // checking compound tokens is done separately.
        let operators = r#"
            + - * / % & | ^ ! ~ < > <= >= == !=
            << >> = += -= *= /= %= &= |= ^= <<= >>=
            ++ -- -> . ? : , ; ... && ||
            ( ) [ ] { }
        "#;

        let tokens = setup_lexer(operators);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_integer_literals() {
        let inputs = r#"
            42
            0x1A
            077
            1ll 42u 123l 456ul 789lu 1000ull 2000llu
            0x1Au 0xFFll 0x10UL 0x20LU 0x40ULL 0x80LLU
            077u 0123l 0777ul 0123lu 0777ull 0123llu
            1LL 42U 123L 456UL 789LU 1000ULL 2000LLU
        "#;

        let tokens = setup_lexer(inputs);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_float_literals() {
        // FIXME: Some of these cases reveal bugs or missing features in the lexer.
        // - .5 is currently lexed as [Dot, IntegerConstant(5)] instead of FloatConstant(0.5).
        // - 0x1p+1 is lexed as [Unknown, Plus, IntegerConstant(1)] because hex floats with exponent
        //   without a dot are not correctly parsed.
        let inputs = r#"
            1.5
            1.23e-4
            0x1.2p3
            1.
            .5
            1e10
            0x1p+1
        "#;

        let tokens = setup_lexer(inputs);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_char_and_string_literals() {
        let inputs = r#"
            'a'
            '\n'
            "hello"
            "world\n"
        "#;

        let tokens = setup_lexer(inputs);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_identifiers() {
        let inputs = "variable my_var _private var123 a _";
        let tokens = setup_lexer(inputs);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_string_literal_concatenation() {
        // Test adjacent string literal concatenation (C11 6.4.5)
        // Note: The lexer performs concatenation on adjacent string tokens.

        // Basic concatenation: "hello" "world" -> "helloworld"
        let t1 = setup_lexer(r#""hello" "world""#);

        // With whitespace: "hello"   "world" -> "helloworld"
        let t2 = setup_lexer(r#""hello"   "world""#);

        // Multiple: "a" "b" "c" -> "abc"
        let t3 = setup_lexer(r#""a" "b" "c""#);

        // With escapes: "hello\n" "world" -> "hello\nworld"
        let t4 = setup_lexer(r#""hello\n" "world""#);

        // Mixed: "start" " middle " "end" -> "start middle end"
        let t5 = setup_lexer(r#""start" " middle " "end""#);

        insta::assert_yaml_snapshot!(vec![t1, t2, t3, t4, t5]);
    }

    #[test]
    fn test_non_concatenation() {
         // Test that non-adjacent strings are not concatenated
        let tokens = setup_lexer(r#""hello" ; "world""#);
        insta::assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile
        let eof = setup_lexer_with_eof("", true);

        // Unknown character
        let unknown = setup_lexer("@");

        insta::assert_yaml_snapshot!(vec![eof, unknown]);
    }
}
