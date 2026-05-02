use crate::pp::PPTokenKind;
use crate::tests::pp_common::setup_pp_snapshot;

// Helper to quickly assert token sequences from a source string.
macro_rules! test_tokens {
    ($source:expr, [$( ($kind:expr, $text:expr) ),* $(,)?]) => {
        let tokens = setup_pp_snapshot($source);
        let expected = vec![ $( ($kind, $text) ),* ];
        assert_eq!(tokens.len(), expected.len(), "Token count mismatch");

        for (i, (tok, (expected_kind, expected_text))) in tokens.iter().zip(expected.iter()).enumerate() {
            assert_eq!(tok.kind, format!("{:?}", expected_kind), "Token kind mismatch at index {}", i);
            assert_eq!(tok.text, *expected_text, "Token text mismatch at index {}", i);
        }
    };
}

#[test]
fn test_digraph_punctuators() {
    let source = "<: :> <% %> %: %:%:";

    test_tokens!(
        source,
        [
            (PPTokenKind::LeftBracket, "["),
            (PPTokenKind::RightBracket, "]"),
            (PPTokenKind::LeftBrace, "{"),
            (PPTokenKind::RightBrace, "}"),
            (PPTokenKind::Hash, "#"),
            (PPTokenKind::HashHash, "##"),
        ]
    );
}

#[test]
fn test_digraph_directives() {
    let source = "
%:define FOO 1
%:if FOO
int x = 42;
%:endif
";
    let tokens = setup_pp_snapshot(source);

    // The directive should be processed normally, so we only see the body tokens
    assert_eq!(tokens.len(), 5);

    // int x = 42 ;
    let texts = vec!["int", "x", "=", "42", ";"];
    for (i, text) in texts.iter().enumerate() {
        assert_eq!(tokens[i].text, *text);
    }
}

#[test]
fn test_digraph_fast_skip() {
    let source = "
%:if 0
  this is skipped;
  int x = %:not_a_directive;
  // %:fake directive in comment
  %:if 1
    nested skipped %:
  %:endif
%:else
  int y = 1;
%:endif
";
    let tokens = setup_pp_snapshot(source);

    // Only "int y = 1;" should be returned
    assert_eq!(tokens.len(), 5);

    let texts = vec!["int", "y", "=", "1", ";"];
    for (i, text) in texts.iter().enumerate() {
        assert_eq!(tokens[i].text, *text);
    }
}
