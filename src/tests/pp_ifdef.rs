use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_ifdef_defined() {
    let src = r#"
#define FOO
#ifdef FOO
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_ifdef_undefined() {
    let src = r#"
#ifdef FOO
FAIL
#endif
OK
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_ifndef_defined() {
    let src = r#"
#define FOO
#ifndef FOO
FAIL
#endif
OK
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_ifndef_undefined() {
    let src = r#"
#ifndef FOO
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_ifdef_else_defined() {
    let src = r#"
#define FOO
#ifdef FOO
OK
#else
FAIL
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_ifdef_else_undefined() {
    let src = r#"
#ifdef FOO
FAIL
#else
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_nested_ifdef() {
    let src = r#"
#define FOO
#define BAR
#ifdef FOO
  #ifdef BAR
    OK
  #endif
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_nested_ifdef_mixed() {
    let src = r#"
#define FOO
#ifdef FOO
  #ifdef BAR
    FAIL
  #else
    OK
  #endif
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_ifdef_elif_chain() {
    let src = r#"
#ifdef FOO
FAIL
#elif 1
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}
