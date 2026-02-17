use crate::tests::pp_common::setup_pp_snapshot;

// This file contains tests specifically targeting uncovered code paths in `expand_tokens`
// in `src/pp/preprocessor.rs`.

#[test]
fn test_expand_tokens_magic_macro_coverage() {
    // This test targets the code path:
    // if let Some(magic) = self.try_expand_magic_macro(&token) {
    //     tokens[i] = magic;
    //     i += 1;
    //     continue;
    // }
    //
    // When `M` is expanded, it produces `__LINE__`.
    // The `expand_object_macro` function then calls `expand_tokens` on the result.
    // Inside `expand_tokens`, it encounters `__LINE__`. `try_expand_magic_macro` returns Some,
    // and the code path is taken.
    let src = r#"
#define M __LINE__
M
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_expand_tokens_pragma_operator_coverage() {
    // This test targets the code path:
    // if self.try_handle_pragma_operator(tokens, i) {
    //     continue;
    // }
    //
    // When `P` is expanded, it produces `_Pragma("once")`.
    // The `expand_object_macro` function then calls `expand_tokens` on the result.
    // Inside `expand_tokens`, it encounters `_Pragma`. `try_handle_pragma_operator` returns true,
    // and the code path is taken (the tokens are consumed/drained).
    let src = r#"
#define P _Pragma("once")
P
"#;
    let tokens = setup_pp_snapshot(src);
    // The _Pragma("once") is handled and removed from the token stream.
    insta::assert_yaml_snapshot!(tokens, @"[]");
}
