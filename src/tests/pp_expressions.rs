use crate::tests::pp_common::{setup_multi_file_pp_snapshot, setup_pp_snapshot};

// Preprocessor Expression and Conditional tests
#[test]
fn test_pp_arithmetic_ops() {
    let src = r#"
#if 1 + 2 * 3 == 7
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_pp_logic_ops() {
    let src = r#"
#if 1 && 1
OK
#endif

#if 0 || 0
FAIL
#else
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_pp_defined_operator() {
    let src = r#"
#define DEFINED_VAR 100
#if defined(DEFINED_VAR)
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    ");
}

// Unsigned Arithmetic
#[test]
fn test_pp_unsigned_arithmetic() {
    let src = r#"
#if 0xFFFFFFFFFFFFFFFFU > 0
OK
#endif

#if -1 < 0U
FAIL
#else
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    - kind: Identifier
      text: OK
    ");
}

// __has_include
#[test]
fn test_has_include_builtin() {
    let src = r#"
#if __has_include(<stddef.h>)
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_has_include_with_files() {
    let files = vec![
        ("header.h", "int z = 3;"),
        (
            "main.c",
            r#"
#if __has_include("header.h")
OK
#endif
"#,
        ),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK
    "#);
}

// Conditional Operator
#[test]
fn test_pp_conditional_op() {
    let src = r#"
#if 1 ? 1 : 0
TRUE
#else
FALSE
#endif

#if 0 ? 1 : 0
FALSE
#else
TRUE
#endif

#if (1 ? 2 : 3) == 2
OK
#endif

#if (1 ? -1 : 1U) > 0
UNSIGNED
#else
SIGNED
#endif

#if (1 ? -1 : 0) > 0
UNSIGNED
#else
SIGNED
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: "TRUE"
    - kind: Identifier
      text: "TRUE"
    - kind: Identifier
      text: OK
    - kind: Identifier
      text: UNSIGNED
    - kind: Identifier
      text: SIGNED
    "#);
}
