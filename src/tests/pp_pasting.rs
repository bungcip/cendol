use crate::diagnostic::DiagnosticEngine;
use crate::pp::*;
use crate::source_manager::SourceManager;
use serde::Serialize;

#[derive(Serialize)]
struct DebugToken {
    kind: String,
    text: String,
}

impl From<&PPToken> for DebugToken {
    fn from(token: &PPToken) -> Self {
        let kind_str = match &token.kind {
            PPTokenKind::Identifier(_) => "Identifier".to_string(),
            PPTokenKind::StringLiteral(_) => "StringLiteral".to_string(),
            PPTokenKind::Number(_) => "Number".to_string(),
            PPTokenKind::CharLiteral(_, _) => "CharLiteral".to_string(),
            k => format!("{:?}", k),
        };

        DebugToken {
            kind: kind_str,
            text: token.get_text().to_string(),
        }
    }
}

fn setup_pp_snapshot(src: &str) -> Vec<DebugToken> {
    let mut source_manager = SourceManager::new();
    let mut diagnostics = DiagnosticEngine::new();
    let config = PPConfig::default();

    let source_id = source_manager.add_buffer(src.as_bytes().to_vec(), "<test>");
    let mut preprocessor = Preprocessor::new(&mut source_manager, &mut diagnostics, &config);

    let tokens = preprocessor.process(source_id, &config).unwrap();
    let significant_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, PPTokenKind::Eof | PPTokenKind::Eod))
        .collect();

    significant_tokens.iter().map(DebugToken::from).collect()
}

#[test]
fn test_paste_numbers() {
    let src = r#"
#define PASTE(a,b) a ## b
int x = PASTE(1, 2);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "12"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_paste_operators() {
    let src = r#"
#define PASTE(a,b) a ## b
int x = 1;
x PASTE(+, =) 2;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: x
    - kind: PlusAssign
      text: +=
    - kind: Number
      text: "2"
    - kind: Semicolon
      text: ;
    "#);
}
