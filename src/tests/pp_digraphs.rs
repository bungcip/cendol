use crate::intern::StringId;
use crate::pp::{PPConfig, PPTokenKind, Preprocessor};
use crate::source_manager::SourceManager;
use crate::diagnostic::DiagnosticEngine;

fn setup_pp_test_kinds(input: &str) -> Vec<PPTokenKind> {
    let mut source_manager = SourceManager::new();
    let source_id = source_manager.add_buffer(input.as_bytes().to_vec(), "test.c", None);

    let mut diag = DiagnosticEngine::new();
    let config = PPConfig::default();

    let mut pp = Preprocessor::new(&mut source_manager, &mut diag, &config);
    let tokens = pp.process(source_id, &config).expect("Preprocessing failed");

    tokens.into_iter()
        .filter(|t| t.kind != PPTokenKind::Eof && t.kind != PPTokenKind::Eod)
        .map(|t| t.kind)
        .collect()
}

fn setup_pp_test_strings(input: &str) -> Vec<String> {
    let mut source_manager = SourceManager::new();
    let source_id = source_manager.add_buffer(input.as_bytes().to_vec(), "test.c", None);

    let mut diag = DiagnosticEngine::new();
    let config = PPConfig::default();

    let mut pp = Preprocessor::new(&mut source_manager, &mut diag, &config);
    let tokens = pp.process(source_id, &config).expect("Preprocessing failed");

    tokens.into_iter()
        .filter(|t| t.kind != PPTokenKind::Eof && t.kind != PPTokenKind::Eod)
        .map(|t| pp.get_token_text(&t).to_string())
        .collect()
}

#[test]
fn test_digraph_brackets() {
    let input = "int a<:5:>;";
    let tokens = setup_pp_test_kinds(input);

    // int a [ 5 ] ;
    assert_eq!(tokens.len(), 6);
    match &tokens[0] {
        PPTokenKind::Identifier(id) => assert_eq!(id.as_str(), "int"),
        _ => panic!("Expected int"),
    }
    match &tokens[1] {
        PPTokenKind::Identifier(id) => assert_eq!(id.as_str(), "a"),
        _ => panic!("Expected a"),
    }
    assert!(matches!(tokens[2], PPTokenKind::LeftBracket));
    assert!(matches!(tokens[3], PPTokenKind::Number(_)));
    assert!(matches!(tokens[4], PPTokenKind::RightBracket));
    assert!(matches!(tokens[5], PPTokenKind::Semicolon));
}

#[test]
fn test_digraph_braces() {
    let input = "<% int a; %>";
    let tokens = setup_pp_test_kinds(input);

    assert!(matches!(tokens[0], PPTokenKind::LeftBrace));
    // int, a, ;
    assert!(matches!(tokens[4], PPTokenKind::RightBrace));
}

#[test]
fn test_digraph_hash_directive() {
    let input = r#"
%:define FOO 100
FOO
"#;
    let tokens = setup_pp_test_strings(input);
    assert_eq!(tokens, vec!["100"]);
}

#[test]
fn test_digraph_pasting() {
    let input = r#"
#define PASTE(a, b) a %:%: b
PASTE(x, y)
"#;
    let tokens = setup_pp_test_strings(input);
    assert_eq!(tokens, vec!["xy"]);
}

#[test]
fn test_digraph_mixed() {
    let input = r#"
%:define ARR(n) int arr<:n:> = <% 0 %>;
ARR(10)
"#;
    let tokens = setup_pp_test_kinds(input);
    // int arr [ 10 ] = { 0 } ;
    let expected = vec![
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenKind::Identifier(StringId::new("arr")),
        PPTokenKind::LeftBracket,
        PPTokenKind::Number(StringId::new("10")),
        PPTokenKind::RightBracket,
        PPTokenKind::Assign,
        PPTokenKind::LeftBrace,
        PPTokenKind::Number(StringId::new("0")),
        PPTokenKind::RightBrace,
        PPTokenKind::Semicolon,
    ];

    // We can't easily compare whole vector because of StringId and Number content,
    // but we can check types and key values.
    assert_eq!(tokens.len(), expected.len());
    assert!(matches!(tokens[0], PPTokenKind::Identifier(_))); // int
    assert!(matches!(tokens[2], PPTokenKind::LeftBracket));
    assert!(matches!(tokens[4], PPTokenKind::RightBracket));
    assert!(matches!(tokens[6], PPTokenKind::LeftBrace));
    assert!(matches!(tokens[8], PPTokenKind::RightBrace));
}

#[test]
fn test_not_digraphs() {
    // Check that % followed by something else is not a digraph
    let input = "a % b";
    let tokens = setup_pp_test_kinds(input);
    assert!(matches!(tokens[1], PPTokenKind::Percent));

    let input = "a % : b"; // Not a digraph (space)
    let tokens = setup_pp_test_kinds(input);
    assert!(matches!(tokens[1], PPTokenKind::Percent));
    assert!(matches!(tokens[2], PPTokenKind::Colon));

    let input = "< :"; // Not a digraph
    let tokens = setup_pp_test_kinds(input);
    assert!(matches!(tokens[0], PPTokenKind::Less));
    assert!(matches!(tokens[1], PPTokenKind::Colon));
}

#[test]
fn test_expression_hash() {
    // This should NOT be interpreted as a directive because it's not at the start of the line.
    // It should just be lexed as a Hash token (which is technically invalid in C expression, but valid token stream).
    // If our fix is correct, this will NOT error with "InvalidDirective".

    // Test digraph %:
    let input = "int x = %: 0;";
    let tokens = setup_pp_test_kinds(input);

    assert_eq!(tokens.len(), 6);
    assert!(matches!(tokens[3], PPTokenKind::Hash));

    // Test standard #
    let input = "int x = # 0;";
    let tokens = setup_pp_test_kinds(input);

    assert_eq!(tokens.len(), 6);
    assert!(matches!(tokens[3], PPTokenKind::Hash));
}
