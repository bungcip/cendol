use crate::pp::PPTokenKind;
use crate::test_tokens;
use crate::tests::pp_common::{create_test_pp_lexer, setup_pp_snapshot};

#[test]
fn test_all_digraph_tokens() {
    let source = "<: :> <% %> %: %:%:";
    let mut lexer = create_test_pp_lexer(source);

    test_tokens!(
        lexer,
        ("<:", PPTokenKind::LeftBracket),
        (":>", PPTokenKind::RightBracket),
        ("<%", PPTokenKind::LeftBrace),
        ("%>", PPTokenKind::RightBrace),
        ("%:", PPTokenKind::Hash),
        ("%:%:", PPTokenKind::HashHash),
    );
}

#[test]
fn test_digraph_directive() {
    // Digraph %: should work as # for directives
    let source = "%:define FOO 1\nFOO";
    let tokens = setup_pp_snapshot(source);

    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "1");
}

#[test]
fn test_digraph_stringification() {
    let source = "#define STR(x) #x\nSTR(a)";
    let tokens = setup_pp_snapshot(source);
    assert_eq!(tokens[0].text, "\"a\"");

    // With digraph stringification
    let source = "#define STR2(x) %:x\nSTR2(a)";
    let tokens = setup_pp_snapshot(source);
    assert_eq!(tokens[0].text, "\"a\"");
}

#[test]
fn test_digraph_concatenation() {
    let source = "#define CONCAT(a, b) a %:%: b\nCONCAT(x, y)";
    let tokens = setup_pp_snapshot(source);
    assert_eq!(tokens[0].text, "xy");
}

#[test]
fn test_digraph_mixed() {
    let source = "<: %> <% :>";
    let mut lexer = create_test_pp_lexer(source);
    test_tokens!(
        lexer,
        ("<:", PPTokenKind::LeftBracket),
        ("%>", PPTokenKind::RightBrace),
        ("<%", PPTokenKind::LeftBrace),
        (":>", PPTokenKind::RightBracket),
    );
}

#[test]
fn test_digraph_backtrack() {
    let mut lexer = create_test_pp_lexer("%: %");
    test_tokens!(lexer, ("%:", PPTokenKind::Hash), ("%", PPTokenKind::Percent),);

    let mut lexer = create_test_pp_lexer("%: :");
    test_tokens!(lexer, ("%:", PPTokenKind::Hash), (":", PPTokenKind::Colon),);

    let mut lexer = create_test_pp_lexer("%:% :");
    test_tokens!(
        lexer,
        ("%:", PPTokenKind::Hash),
        ("%", PPTokenKind::Percent),
        (":", PPTokenKind::Colon),
    );
}

#[test]
fn test_xor_regression() {
    let mut lexer = create_test_pp_lexer("^ ^=");
    test_tokens!(lexer, ("^", PPTokenKind::Xor), ("^=", PPTokenKind::XorAssign),);

    // Ensure ^: is not a digraph
    let mut lexer = create_test_pp_lexer("^: ^>");
    test_tokens!(
        lexer,
        ("^", PPTokenKind::Xor),
        (":", PPTokenKind::Colon),
        ("^", PPTokenKind::Xor),
        (">", PPTokenKind::Greater),
    );
}
