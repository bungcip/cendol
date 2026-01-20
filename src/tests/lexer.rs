use crate::driver::artifact::CompilePhase;
use crate::lexer::*;
use crate::tests::test_utils;
use insta::assert_yaml_snapshot;

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

fn setup_lexer_snapshot(input: &str) -> Vec<TokenKind> {
    setup_lexer(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c11_keywords() {
        let source = "
            auto break case char const continue default do
            double else enum extern float for goto if
            inline int long register restrict return short
            signed sizeof static struct switch typedef union
            unsigned void volatile while
            _Alignas _Alignof _Atomic _Bool _Complex _Generic
            _Noreturn _Static_assert _Thread_local
        ";
        let tokens = setup_lexer_snapshot(source);
        assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_operators_and_punctuation() {
        let source = "
            + - * / % & | ^ ! ~ < > <= >= == !=
            << >> = += -= *= /= %= &= |= ^=
            <<= >>= ++ -- -> . ? : , ; ...
            ( ) [ ] { } && ||
        ";
        let tokens = setup_lexer_snapshot(source);
        assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_literals() {
        let source = r#"
            42 0x1A 077
            1ll 42u 123l 456ul 789lu 1000ull 2000llu
            0x1Au 0xFFll 0x10UL 0x20LU 0x40ULL 0x80LLU
            077u 0123l 0777ul 0123lu 0777ull 0123llu
            1LL 42U 123L 456UL 789LU 1000ULL 2000LLU
            1.5 1.23e-4 0x1.2p3
            'a' '\n'
            "hello" "world\n"
        "#;
        let tokens = setup_lexer_snapshot(source);
        assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_complex_float_literals() {
        let source = "
            0x1p+1
            0x.8p0
            0XABCp-1
            1.f
            .5
            1e10
            0x1.FFFFp1023
            0x1p-1022
        ";
        let tokens = setup_lexer_snapshot(source);
        assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_identifiers() {
        let source = "variable my_var _private var123 a _";
        let tokens = setup_lexer_snapshot(source);
        assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_string_literal_concatenation() {
        let source = r#"
            "hello" "world"
            "hello"   "world"
            "a" "b" "c"
            "hello\n" "world"
            "start" " middle " "end"
        "#;
        let tokens = setup_lexer_snapshot(source);
        assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_non_adjacent_string_literals() {
         let source = r#""hello" ; "world""#;
         let tokens = setup_lexer_snapshot(source);
         assert_yaml_snapshot!(tokens);
    }

    #[test]
    fn test_special_tokens() {
        // EndOfFile is filtered out by setup_lexer, but we can test setup_lexer_with_eof
        let tokens = setup_lexer_with_eof("", true);
        assert_yaml_snapshot!(tokens, @r###"
        - EndOfFile
        "###);

        // Unknown
        let tokens = setup_lexer("@");
        assert_yaml_snapshot!(tokens, @r###"
        - Unknown
        "###);
    }

    #[test]
    fn test_string_escapes() {
        let source = r#""\n \t \r \b \f \v \a \\ \' \" \? \x41 \101""#; // \x41 = A, \101 = A
        let tokens = setup_lexer_snapshot(source);
        assert_yaml_snapshot!(tokens);
    }
}
