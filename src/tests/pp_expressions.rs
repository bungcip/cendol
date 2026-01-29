use crate::tests::pp_common::{setup_pp_snapshot, setup_pp_snapshot_with_diags};

#[test]
fn test_pp_arithmetic_ops() {
    let src = r#"
#if 1 + 2 * 3 == 7
int add_mul = 1;
#endif

#if (1 + 2) * 3 == 9
int add_mul_grouped = 1;
#endif

#if 10 - 2 == 8
int sub = 1;
#endif

#if 10 / 2 == 5
int div = 1;
#endif

#if 10 % 3 == 1
int rem = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: add_mul
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: add_mul_grouped
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: sub
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: div
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: rem
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_pp_bitwise_ops() {
    let src = r#"
#if (0xF0 & 0x0F) == 0
int bit_and = 1;
#endif

#if (0xF0 | 0x0F) == 0xFF
int bit_or = 1;
#endif

#if (0xF0 ^ 0xFF) == 0x0F
int bit_xor = 1;
#endif

#if ~0 == -1
int bit_not = 1;
#endif

#if (1 << 4) == 16
int lshift = 1;
#endif

#if (16 >> 2) == 4
int rshift = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: bit_and
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: bit_or
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: bit_xor
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: bit_not
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: lshift
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: rshift
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_pp_logic_ops() {
    let src = r#"
#if 1 && 1
int logic_and_true = 1;
#endif

#if 1 && 0
int logic_and_false = 1;
#else
int logic_and_false_else = 1;
#endif

#if 0 || 1
int logic_or_true = 1;
#endif

#if 0 || 0
int logic_or_false = 1;
#else
int logic_or_false_else = 1;
#endif

#if !0
int logic_not_true = 1;
#endif

#if !1
int logic_not_false = 1;
#else
int logic_not_false_else = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: logic_and_true
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: logic_and_false_else
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: logic_or_true
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: logic_or_false_else
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: logic_not_true
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: logic_not_false_else
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_pp_relational_ops() {
    let src = r#"
#if 1 < 2
int less = 1;
#endif

#if 2 <= 2
int less_equal = 1;
#endif

#if 2 > 1
int greater = 1;
#endif

#if 2 >= 2
int greater_equal = 1;
#endif

#if 1 == 1
int equal = 1;
#endif

#if 1 != 2
int not_equal = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: less
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: less_equal
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: greater
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: greater_equal
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: equal
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: not_equal
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_pp_undefined_identifiers() {
    let src = r#"
#if UNDEFINED_VAR == 0
int undefined_is_zero = 1;
#endif

#if UNDEFINED_VAR
int undefined_is_true = 1;
#else
int undefined_is_false = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: undefined_is_zero
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: undefined_is_false
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_pp_defined_operator() {
    let src = r#"
#define DEFINED_VAR 100

#if defined(DEFINED_VAR)
int is_defined = 1;
#endif

#if defined DEFINED_VAR
int is_defined_no_paren = 1;
#endif

#if !defined(UNDEFINED_VAR)
int is_not_defined = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: is_defined
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: is_defined_no_paren
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: is_not_defined
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_pp_division_by_zero() {
    let src = r#"
#if 1 / 0
int div_zero = 1;
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Warning: Invalid conditional expression in preprocessor directive""#);
}

#[test]
fn test_pp_complex_precedence() {
    let src = r#"
// ! binds tighter than &&
#if !0 && 1
int not_binds_tight = 1;
#endif

// && binds tighter than ||
#if 1 || 0 && 0
int and_binds_tighter_than_or = 1;
#endif

// * binds tighter than +
#if 1 + 2 * 3 == 7
int mul_binds_tighter_than_add = 1;
#endif

// == binds tighter than &&
#if 1 == 1 && 2 == 2
int eq_binds_tighter_than_and = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: not_binds_tight
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: and_binds_tighter_than_or
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: mul_binds_tighter_than_add
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: eq_binds_tighter_than_and
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}
