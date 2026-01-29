use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_stringification_whitespace_handling() {
    let src = r#"
#define STR(x) #x
const char* s1 = STR(a+b);
const char* s2 = STR(a + b);
const char* s3 = STR( f(a, b) );
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: const
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s1
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"a+b\""
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: const
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s2
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"a + b\""
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: const
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s3
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"f(a, b)\""
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_va_args_stringification() {
    let src = r#"
#define STR(...) #__VA_ARGS__
const char* s = STR(a, b, c);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: const
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"a, b, c\""
    - kind: Semicolon
      text: ;
    "#);
}
