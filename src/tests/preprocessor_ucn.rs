use crate::tests::pp_common::setup_preprocessor_test_with_diagnostics;
use crate::pp::PPConfig;
use crate::lang_options::LangOptions;

#[test]
fn test_ucn_identifier() {
    let src = r#"
#define \u00E4 10
int x = \u00E4;
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    // Tokens:
    // 1. int (because #define is consumed)
    // 2. x
    // 3. =
    // 4. 10 (expanded)
    // 5. ;

    assert!(tokens.iter().any(|t| t.get_text() == "10"));
}

#[test]
fn test_raw_utf8_identifier() {
    let src = r#"
#define ä 20
int x = ä;
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "20"));
}

#[test]
fn test_mixed_ucn_identifier() {
    let src = r#"
#define a\u00E4b 30
int x = aäb;
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "30"));
}

#[test]
fn test_ucn_string_literal() {
    let src = r#"
char *s = "\u00E4";
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    let s_token = tokens.iter().find(|t| t.get_text().contains(r#"\u00E4"#));
    assert!(s_token.is_some(), "Could not find string literal with \\u00E4");
}

#[test]
fn test_invalid_ucn_in_string() {
    let src = r#"
char *s = "\uD800"; // Surrogate, invalid
"#;
    let (_, diags) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    assert!(diags.iter().any(|d| d.message.contains("Invalid universal character name")), "Expected invalid UCN diagnostic");
}

#[test]
fn test_utf_macros() {
    let src = r#"
#if __STDC_UTF_16__ == 1
int u16 = 1;
#endif
#if __STDC_UTF_32__ == 1
int u32 = 1;
#endif
"#;
    let config = PPConfig {
        lang_options: LangOptions::c11(),
        ..Default::default()
    };
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, Some(config)).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "u16"));
    assert!(tokens.iter().any(|t| t.get_text() == "u32"));
}
