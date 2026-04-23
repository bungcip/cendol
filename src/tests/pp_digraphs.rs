use crate::pp::PPTokenKind;
use crate::tests::pp_common::create_test_pp_lexer;

#[macro_export]
macro_rules! test_digraph_tokens {
    ($lexer:expr, $( ($input:expr, $expected:pat) ),* $(,)?) => {
        $(
            let token = $lexer.next_token().unwrap();
            match token.kind {
                $expected => {
                    // Digraphs are tokenized as their standard equivalents.
                    // We don't check for literal source text here because get_text_from_buffer
                    // (and hence get_text_with_sm) returns the fixed text for punctuators.
                },
                _ => panic!("Expected {:?}, got {:?}", stringify!($expected), token.kind),
            }
        )*
    };
}

#[test]
fn test_digraphs() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    test_digraph_tokens!(
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
    let source = "%:define FOO 1";
    let mut lexer = create_test_pp_lexer(source);

    let t1 = lexer.next_token().unwrap();
    assert_eq!(t1.kind, PPTokenKind::Hash);
    assert!(t1.flags.contains(crate::pp::PPTokenFlags::STARTS_PP_LINE));

    test_digraph_tokens!(
        lexer,
        ("define", PPTokenKind::Identifier(_)),
        ("FOO", PPTokenKind::Identifier(_)),
        ("1", PPTokenKind::Number),
        ("", PPTokenKind::Eod),
    );
}

#[test]
fn test_digraph_splices() {
    let source = "<\\\n: :\\\n> <\\\n% %\\\n> %\\\n: %\\\n:%\\\n:";
    let mut lexer = create_test_pp_lexer(source);

    test_digraph_tokens!(
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
fn test_not_digraphs() {
    let source = "% : % % : : % : % :";
    let mut lexer = create_test_pp_lexer(source);

    test_digraph_tokens!(
        lexer,
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
        ("%", PPTokenKind::Percent),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
        (":", PPTokenKind::Colon),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
    );
}

#[test]
fn test_percent_colon_percent_not_hash_hash() {
    let source = "%:%";
    let mut lexer = create_test_pp_lexer(source);

    test_digraph_tokens!(
        lexer,
        ("#", PPTokenKind::Hash),
        ("%", PPTokenKind::Percent),
    );
}
