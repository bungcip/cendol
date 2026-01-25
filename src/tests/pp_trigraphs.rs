#[cfg(test)]
mod tests {
    use crate::intern::StringId;
    use crate::pp::pp_lexer::{PPLexer, PPTokenKind};
    use crate::source_manager::SourceId;

    fn create_test_pp_lexer(source: &str) -> PPLexer {
        let source_id = SourceId::new(1);
        let buffer = source.as_bytes().to_vec();
        PPLexer::new(source_id, buffer)
    }

    #[test]
    fn test_all_trigraphs() {
        // ??= #
        // ??( [
        // ??/ \
        // ??) ]
        // ??' ^
        // ??< {
        // ??! |
        // ??> }
        // ??- ~
        let source = "??= ??( ??/ ??/ ??) ??' ??< ??! ??> ??-";

        let mut lexer = create_test_pp_lexer(source);

        // ??= -> #
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Hash);

        // ??( -> [
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::LeftBracket);

        // ??/ -> \ (Unknown token unless it's part of something else)
        // \ is not a valid operator, so it returns Unknown
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Unknown); // First ??/

        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Unknown); // Second ??/

        // ??) -> ]
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::RightBracket);

        // ??' -> ^
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Xor);

        // ??< -> {
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::LeftBrace);

        // ??! -> |
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Or);

        // ??> -> }
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::RightBrace);

        // ??- -> ~
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Tilde);
    }

    #[test]
    fn test_trigraph_line_splice() {
        // ??/ followed by newline should be spliced
        // Remove space to ensure they merge into one identifier
        let source = "abc??/\ndef";
        let mut lexer = create_test_pp_lexer(source);

        // Should lex as "abcdef" (identifier)
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Identifier(StringId::new("abcdef")));
    }

    #[test]
    fn test_trigraph_in_string() {
        // Trigraphs ARE replaced in string literals (Phase 1 vs Phase 3)
        // "??=" should be "#"
        let source = "\"??=\"";
        let mut lexer = create_test_pp_lexer(source);

        let t = lexer.next_token().unwrap();
        // StringLiteral kind stores the raw text INCLUDING quotes
        assert_eq!(t.kind, PPTokenKind::StringLiteral(StringId::new("\"#\"")));
    }

    #[test]
    fn test_escaped_question_mark() {
        // \??= becomes \#
        let source = "\"\\??=\"";
        let mut lexer = create_test_pp_lexer(source);

        let t = lexer.next_token().unwrap();
        // StringLiteral kind stores the raw text INCLUDING quotes
        // Since lex_string_literal doesn't interpret \# as an escape, it keeps the backslash
        assert_eq!(t.kind, PPTokenKind::StringLiteral(StringId::new("\"\\#\"")));
    }

    #[test]
    fn test_no_trigraph() {
        // ??x is not a trigraph
        let source = "??x";
        let mut lexer = create_test_pp_lexer(source);

        // Should be ?, ?, x
        // ? is Question
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Question);

        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Question);

        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Identifier(StringId::new("x")));
    }

    #[test]
    fn test_trigraph_composite_tokens() {
        // ??! is |
        // ??!??! should be || (LogicOr)
        let source = "??!??!";
        let mut lexer = create_test_pp_lexer(source);

        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::LogicOr);

        // ??= is #
        // ??=??= should be ## (HashHash)
        let source = "??=??=";
        let mut lexer = create_test_pp_lexer(source);

        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::HashHash);

        // ??- is ~
        // ??-??- is ~~ (Tilde Tilde) - technically two tokens
        let source = "??-??-";
        let mut lexer = create_test_pp_lexer(source);

        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Tilde);
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Tilde);

        // ??< is {
        // ??<: is {: - which is NOT a digraph.
        // <: is [.
        // But ??< consumes <. So it leaves :.
        let source = "??<:";
        let mut lexer = create_test_pp_lexer(source);

        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::LeftBrace);
        let t = lexer.next_token().unwrap();
        assert_eq!(t.kind, PPTokenKind::Colon);
    }
}
