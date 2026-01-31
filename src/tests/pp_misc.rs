use crate::tests::pp_common::setup_pp_snapshot;

// GNU Extensions
#[test]
fn test_gnu_comma_swallowing() {
    let src = r#"
#define LOG(fmt, ...) printf(fmt, ##__VA_ARGS__)
LOG("foo");
LOG("bar", 1);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: printf
    - kind: LeftParen
      text: (
    - kind: StringLiteral
      text: "\"foo\""
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: printf
    - kind: LeftParen
      text: (
    - kind: StringLiteral
      text: "\"bar\""
    - kind: Comma
      text: ","
    - kind: Number
      text: "1"
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "#);
}

// Regressions
#[test]
fn test_recursive_macro_expansion_regression() {
    let src = r#"
#define CAT2(a, b) a ## b
#define CAT(a, b) CAT2(a, b)
#define AB(x) CAT(x, y)
int res = AB(x);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: res
    - kind: Assign
      text: "="
    - kind: Identifier
      text: xy
    - kind: Semicolon
      text: ;
    "#);
}
