use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_pp_wide_char_arithmetic() {
    let src = r#"
#if L'\u0400' == 0x0400
OK_WIDE
#else
FAIL_WIDE
#endif

#if '\u00FF' == 255
OK_UCN
#else
FAIL_UCN
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK_WIDE
    - kind: Identifier
      text: OK_UCN
    ");
}
