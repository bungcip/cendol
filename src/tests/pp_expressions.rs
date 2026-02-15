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

// Unary Operators
#[test]
fn test_pp_unary_ops() {
    let src = r#"
/* Unary Plus */
#if +1 == 1
PLUS_OK
#else
PLUS_FAIL
#endif

/* Unary BitNot */
#if ~0 == -1
BITNOT_SIGNED_OK
#else
BITNOT_SIGNED_FAIL
#endif

#if ~0U == 0xFFFFFFFFFFFFFFFFU
BITNOT_UNSIGNED_OK
#else
BITNOT_UNSIGNED_FAIL
#endif

/* Unary LogicNot */
#if !0
LOGICNOT_0_OK
#else
LOGICNOT_0_FAIL
#endif

#if !1
LOGICNOT_1_FAIL
#else
LOGICNOT_1_OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: PLUS_OK
    - kind: Identifier
      text: BITNOT_SIGNED_OK
    - kind: Identifier
      text: BITNOT_UNSIGNED_OK
    - kind: Identifier
      text: LOGICNOT_0_OK
    - kind: Identifier
      text: LOGICNOT_1_OK
    ");
}
