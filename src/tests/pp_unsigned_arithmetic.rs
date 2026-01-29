use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_pp_unsigned_arithmetic() {
    let src = r#"
/* Test 1: High bit set literal (should not be negative in unsigned) */
#if 0xFFFFFFFFFFFFFFFFU > 0
int u64_max_gt_0 = 1;
#else
int u64_max_gt_0 = 0;
#endif

/* Test 2: Signed vs Unsigned comparison */
/* -1 is signed, 0U is unsigned. -1 converts to UINTMAX_MAX. */
/* UINTMAX_MAX < 0 is false. */
#if -1 < 0U
int minus_one_lt_zero_u = 1;
#else
int minus_one_lt_zero_u = 0;
#endif

/* Test 3: Unsigned overflow (wrapping) */
/* UINT64_MAX + 1 == 0 */
#if 0xFFFFFFFFFFFFFFFFU + 1 == 0
int u64_overflow_is_zero = 1;
#else
int u64_overflow_is_zero = 0;
#endif

/* Test 4: Mixed arithmetic */
/* -1 * -1 = 1 (signed) */
/* -1 * -1U ... -1 becomes MAX. MAX * MAX ... */
#if -1 * -1 == 1
int signed_mul = 1;
#endif

/* Test 5: Unsigned suffix parsing */
#if 1u == 1
int u_suffix = 1;
#endif

#if 1U == 1
int U_suffix = 1;
#endif

/* Test 6: Long suffix with unsigned */
#if 1ul == 1
int ul_suffix = 1;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: u64_max_gt_0
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: minus_one_lt_zero_u
    - kind: Assign
      text: "="
    - kind: Number
      text: "0"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: u64_overflow_is_zero
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: signed_mul
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: u_suffix
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: U_suffix
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: ul_suffix
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Semicolon
      text: ;
    "#);
}
