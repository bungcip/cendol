use crate::pp::PPTokenKind;
use crate::tests::pp_common::setup_preprocessor_test_with_diagnostics;

fn setup_preprocessor_test(source: &str) -> Vec<crate::pp::PPToken> {
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(source, None).unwrap();
    tokens
}

#[test]
fn test_pp_digraphs_basic() {
    let source = "<: :> <% %>";
    let tokens = setup_preprocessor_test(source);

    assert_eq!(tokens[0].kind, PPTokenKind::LeftBracket);
    assert_eq!(tokens[1].kind, PPTokenKind::RightBracket);
    assert_eq!(tokens[2].kind, PPTokenKind::LeftBrace);
    assert_eq!(tokens[3].kind, PPTokenKind::RightBrace);
}

#[test]
fn test_pp_digraphs_hash() {
    let source = "%: define FOO 1\nFOO";
    let tokens = setup_preprocessor_test(source);

    // FOO should be expanded to 1
    assert_eq!(tokens[0].get_text(), "1");
}

#[test]
fn test_pp_digraphs_hashhash() {
    let source = "#define CONCAT(a, b) a %:%: b\nCONCAT(x, y)";
    let tokens = setup_preprocessor_test(source);

    assert_eq!(tokens[0].get_text(), "xy");
}

#[test]
fn test_pp_digraphs_directive_start() {
    let source = "%:ifdef UNDEFINED\n  skipped\n%:else\n  kept\n%:endif";
    let tokens = setup_preprocessor_test(source);

    assert_eq!(tokens[0].get_text(), "kept");
}

#[test]
fn test_pp_digraphs_in_string() {
    let source = r#""<: :> <% %> %: %:%:""#;
    let tokens = setup_preprocessor_test(source);

    assert_eq!(tokens[0].get_text(), r#""<: :> <% %> %: %:%:""#);
}

#[test]
fn test_pp_digraphs_mix() {
    let source = "<% int a<:1:>; %>";
    let tokens = setup_preprocessor_test(source);

    assert_eq!(tokens[0].kind, PPTokenKind::LeftBrace);
    assert_eq!(tokens[1].get_text(), "int");
    assert_eq!(tokens[2].get_text(), "a");
    assert_eq!(tokens[3].kind, PPTokenKind::LeftBracket);
    assert_eq!(tokens[4].get_text(), "1");
    assert_eq!(tokens[5].kind, PPTokenKind::RightBracket);
    assert_eq!(tokens[6].kind, PPTokenKind::Semicolon);
    assert_eq!(tokens[7].kind, PPTokenKind::RightBrace);
}

#[test]
fn test_pp_digraphs_not_digraphs() {
    let source = "% = < < : >";
    let tokens = setup_preprocessor_test(source);

    assert_eq!(tokens[0].kind, PPTokenKind::Percent);
    assert_eq!(tokens[1].kind, PPTokenKind::Assign);
    assert_eq!(tokens[2].kind, PPTokenKind::Less);
    assert_eq!(tokens[3].kind, PPTokenKind::Less);
    assert_eq!(tokens[4].kind, PPTokenKind::Colon);
    assert_eq!(tokens[5].kind, PPTokenKind::Greater);
}
