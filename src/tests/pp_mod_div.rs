use crate::tests::pp_common::{setup_pp_snapshot, setup_pp_snapshot_with_diags};

// Test division and modulo operators in preprocessor directives

#[test]
fn test_pp_div_unsigned() {
    let src = r#"
#if 10U / 2U == 5U
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
fn test_pp_div_signed() {
    let src = r#"
#if -10 / 2 == -5
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
fn test_pp_div_signed_overflow() {
    // i64::MIN / -1 should be i64::MIN (due to overflow handling in C/Rust specific behavior in interpreter)
    // -9223372036854775808 / -1
    // We construct -9223372036854775808 as (-9223372036854775807 - 1) because the literal 9223372036854775808 is unsigned.
    let src = r#"
#if ((-9223372036854775807 - 1) / -1) == (-9223372036854775807 - 1)
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
fn test_pp_div_zero() {
    let src = r#"
#if 1 / 0
OK
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    assert!(!diags.is_empty());
    assert!(diags[0].contains("Invalid conditional expression"));
}

#[test]
fn test_pp_mod_unsigned() {
    let src = r#"
#if 10U % 3U == 1U
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
fn test_pp_mod_signed() {
    let src = r#"
#if -10 % 3 == -1
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
fn test_pp_mod_signed_overflow() {
    // i64::MIN % -1 should be 0
    let src = r#"
#if ((-9223372036854775807 - 1) % -1) == 0
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
fn test_pp_mod_zero() {
    let src = r#"
#if 1 % 0
OK
#endif
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    assert!(!diags.is_empty());
    assert!(diags[0].contains("Invalid conditional expression"));
}
