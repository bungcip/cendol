use crate::tests::pp_common::setup_pp_snapshot;

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

#[test]
fn test_paste_va_args() {
    let src = r#"
#define PASTE(...) prefix ## __VA_ARGS__
PASTE(a, b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}
