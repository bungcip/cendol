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

#[test]
fn test_pp_eval_binary_coverage() {
    let src = r#"
/* LogicAnd Short-circuit */
#if 0 && (1/0)
FAIL_AND
#else
OK_AND_SHORT
#endif

/* LogicOr Short-circuit */
#if 1 || (1/0)
OK_OR_SHORT
#else
FAIL_OR
#endif

/* BitOr */
#if (1 | 2) == 3
OK_BITOR
#endif

/* BitXor */
#if (3 ^ 1) == 2
OK_BITXOR
#endif

/* BitAnd */
#if (3 & 1) == 1
OK_BITAND
#endif

/* NotEqual */
#if 1 != 2
OK_NE
#endif

/* LessEqual */
#if 1 <= 1
OK_LE
#endif
#if 1 <= 2
OK_LE2
#endif

/* GreaterEqual */
#if 1 >= 1
OK_GE
#endif
#if 2 >= 1
OK_GE2
#endif

/* LShift */
#if (1 << 1) == 2
OK_LSHIFT
#endif

/* RShift Unsigned */
#if (2U >> 1) == 1
OK_RSHIFT_U
#endif

/* RShift Signed (Arithmetic Shift) */
#if (-2 >> 1) == -1
OK_RSHIFT_S
#endif

/* Add */
#if (1 + 2) == 3
OK_ADD
#endif

/* Sub */
#if (3 - 1) == 2
OK_SUB
#endif

/* Mul */
#if (2 * 3) == 6
OK_MUL
#endif

/* Div */
#if (6 / 3) == 2
OK_DIV
#endif

/* Mod */
#if (7 % 3) == 1
OK_MOD
#endif

/* Signed vs Unsigned Comparison */
#if -1 < 0
OK_SIGNED_COMPARE
#else
FAIL_SIGNED_COMPARE
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK_AND_SHORT
    - kind: Identifier
      text: OK_OR_SHORT
    - kind: Identifier
      text: OK_BITOR
    - kind: Identifier
      text: OK_BITXOR
    - kind: Identifier
      text: OK_BITAND
    - kind: Identifier
      text: OK_NE
    - kind: Identifier
      text: OK_LE
    - kind: Identifier
      text: OK_LE2
    - kind: Identifier
      text: OK_GE
    - kind: Identifier
      text: OK_GE2
    - kind: Identifier
      text: OK_LSHIFT
    - kind: Identifier
      text: OK_RSHIFT_U
    - kind: Identifier
      text: OK_RSHIFT_S
    - kind: Identifier
      text: OK_ADD
    - kind: Identifier
      text: OK_SUB
    - kind: Identifier
      text: OK_MUL
    - kind: Identifier
      text: OK_DIV
    - kind: Identifier
      text: OK_MOD
    - kind: Identifier
      text: OK_SIGNED_COMPARE
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

#[test]
fn test_has_include_computed() {
    let src = r#"
#define STD_HEADER <stddef.h>
#define LOCAL_HEADER "stddef.h"
#define INDIRECT_STD STD_HEADER
#define INDIRECT_LOCAL LOCAL_HEADER

#if __has_include(STD_HEADER)
OK_STD
#else
FAIL_STD
#endif

#if __has_include(LOCAL_HEADER)
OK_LOCAL
#else
FAIL_LOCAL
#endif

#if __has_include(INDIRECT_STD)
OK_INDIRECT_STD
#else
FAIL_INDIRECT_STD
#endif

#if __has_include(INDIRECT_LOCAL)
OK_INDIRECT_LOCAL
#else
FAIL_INDIRECT_LOCAL
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK_STD
    - kind: Identifier
      text: OK_LOCAL
    - kind: Identifier
      text: OK_INDIRECT_STD
    - kind: Identifier
      text: OK_INDIRECT_LOCAL
    "#);
}

#[test]
fn test_pp_arithmetic_edge_cases() {
    let src = r#"
/* Division by zero */
#if 1 / 0
FAIL_DIV_ZERO
#else
OK_DIV_ZERO
#endif

/* Modulo by zero */
#if 1 % 0
FAIL_MOD_ZERO
#else
OK_MOD_ZERO
#endif

/* Signed overflow division: INT64_MIN / -1 */
/* -9223372036854775807 - 1 constructs INT64_MIN as signed */
#if ((-9223372036854775807 - 1) / -1) == (-9223372036854775807 - 1)
OK_DIV_OVERFLOW
#else
FAIL_DIV_OVERFLOW
#endif

/* Signed overflow modulo: INT64_MIN % -1 */
#if ((-9223372036854775807 - 1) % -1) == 0
OK_MOD_OVERFLOW
#else
FAIL_MOD_OVERFLOW
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: OK_DIV_ZERO
    - kind: Identifier
      text: OK_MOD_ZERO
    - kind: Identifier
      text: OK_DIV_OVERFLOW
    - kind: Identifier
      text: OK_MOD_OVERFLOW
    "#);
}
