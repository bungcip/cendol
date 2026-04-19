use crate::pp::PPConfig;
use crate::tests::pp_common::{
    setup_pp_snapshot, setup_pp_snapshot_with_diags, setup_pp_snapshot_with_diags_and_config,
    setup_preprocessor_test_with_diagnostics,
};
use chrono::{TimeZone, Utc};

// Basic macro tests
#[test]
fn test_simple_macro_definition_and_expansion() {
    let src = r#"
#define TEN OK
TEN
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_parameter_macro_definition_and_expansion() {
    let src = r#"
#define ADD(a,b) ( (a) + (b) )
ADD(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Number
      text: "1"
    - kind: RightParen
      text: )
    - kind: Plus
      text: +
    - kind: LeftParen
      text: (
    - kind: Number
      text: "2"
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    "#);
}

#[test]
fn test_complex_macro_expansion_and_recursion_limit() {
    let src = r#"
#define ID(x) x
#define A ID(ID(ID(1)))
A
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_defer_recursive_expansion() {
    let src = r#"
#define EMPTY()
#define DEFER(id) id EMPTY()
#define EXPAND(...) __VA_ARGS__
#define BAR_I() BAR
#define BAR()  DEFER(BAR_I)()() 1
EXPAND(EXPAND(BAR()))
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: BAR_I
    - kind: LeftParen
      text: (
    - kind: RightParen
      text: )
    - kind: LeftParen
      text: (
    - kind: RightParen
      text: )
    - kind: Number
      text: "1"
    - kind: Number
      text: "1"
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_function_like_macro_not_expanded_when_not_followed_by_paren() {
    let src = r#"
#define x(y) ((y) + 1)
int x = x(0);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Number
      text: "0"
    - kind: RightParen
      text: )
    - kind: Plus
      text: +
    - kind: Number
      text: "1"
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "#);
}

// Stringification (#)
#[test]
fn test_stringification_whitespace_handling() {
    let src = r#"
#define STR(x) #x
STR(a + b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"a + b\""
    "#);
}

#[test]
fn test_va_args_stringification() {
    let src = r#"
#define STR(...) #__VA_ARGS__
STR(a, b, c)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"a, b, c\""
    "#);
}

// Token Pasting (##)
#[test]
fn test_paste_numbers() {
    let src = r#"
#define PASTE(a,b) a ## b
PASTE(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "12"
    "#);
}

#[test]
fn test_paste_va_args() {
    let src = r#"
#define PASTE(...) prefix ## __VA_ARGS__
PASTE(a, b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: prefixa
    - kind: Comma
      text: ","
    - kind: Identifier
      text: b
    "#);
}

// Built-in Macros
#[test]
fn test_redefine_builtin_macro_should_fail() {
    let src = r#"
#define __DATE__ "123"
__DATE__
"#;
    let config = PPConfig {
        current_time: Some(Utc.with_ymd_and_hms(2026, 1, 28, 0, 0, 0).unwrap()),
        ..PPConfig::default()
    };
    let (tokens, diags) = setup_pp_snapshot_with_diags_and_config(src, Some(config));
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: StringLiteral
        text: "\"Jan 28 2026\""
    - - "Warning: Redefinition of built-in macro '__DATE__'"
    "#);
}

#[test]
fn test_file_macro() {
    let src = r#"
__FILE__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"<test>\""
    "#);
}

#[test]
fn test_counter_macro() {
    let src = r#"
__COUNTER__
__COUNTER__
__COUNTER__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "0"
    - kind: Number
      text: "1"
    - kind: Number
      text: "2"
    "#);
}

// Macro Argument Parsing
#[test]
fn test_brace_comma_separation() {
    let src = r#"
#define CNT(x, y) 2
CNT({1, 2})
"#;
    let (tokens, _) = setup_preprocessor_test_with_diagnostics(src, None).unwrap();
    assert!(tokens.iter().any(|t| t.get_text() == "2"));
}

#[test]
fn test_paren_comma_protection() {
    let src = r#"
#define ID(x) x
#if 1
(ID((1, 2)))
OK
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Number
      text: "1"
    - kind: Comma
      text: ","
    - kind: Number
      text: "2"
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    - kind: Identifier
      text: OK
    "#);
}

// GNU Extensions
#[test]
fn test_gnu_named_variadic_macros() {
    let src = r#"
#define M(a, args...) args
M(1, 2, 3, 4)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "2"
    - kind: Comma
      text: ","
    - kind: Number
      text: "3"
    - kind: Comma
      text: ","
    - kind: Number
      text: "4"
    "#);
}

#[test]
fn test_gnu_comma_swallowing() {
    let src = r#"
#define M(a, args...) a, ## args
M(1)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_gnu_comma_swallowing_va_args() {
    let src = r#"
#define LOG(fmt, ...) printf(fmt, ##__VA_ARGS__)
LOG("foo");
LOG("bar", 1);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: printf
    - kind: LeftParen
      text: (
    - kind: StringLiteral
      text: "\"foo\""
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: printf
    - kind: LeftParen
      text: (
    - kind: StringLiteral
      text: "\"bar\""
    - kind: Comma
      text: ","
    - kind: Number
      text: "1"
    - kind: RightParen
      text: )
    - kind: Semicolon
      text: ;
    "#);
}

// Regressions
#[test]
fn test_recursive_macro_expansion_regression() {
    let src = r#"
#define CAT2(a, b) a ## b
#define CAT(a, b) CAT2(a, b)
#define AB(x) CAT(x, y)
int res = AB(x);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: res
    - kind: Assign
      text: "="
    - kind: Identifier
      text: xy
    - kind: Semicolon
      text: ;
    "#);
}

// Magic Macros
#[test]
fn test_magic_macros() {
    let src = r#"
__LINE__
__FILE__
__COUNTER__
__COUNTER__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "2"
    - kind: StringLiteral
      text: "\"<test>\""
    - kind: Number
      text: "0"
    - kind: Number
      text: "1"
    "#);
}

// Placemarkers
#[test]
fn test_placemarker_concatenation() {
    let src = r#"
#define M(a, b) a ## b
M(, 1)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_placemarker_concatenation_with_prefix() {
    let src = r#"
#define M(a, b) X a ## b
M(, 1)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: X
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_placemarker_concatenation_chained() {
    let src = r#"
#define M(a, b, c) a ## b ## c
M(, , C)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: C
    ");
}

// GCC Compatibility
#[test]
fn test_gcc_version_macros() {
    let src = r#"
__GNUC__
__GNUC_MINOR__
__GNUC_PATCHLEVEL__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "4"
    - kind: Number
      text: "2"
    - kind: Number
      text: "1"
    "#);
}

// Regression Tests for TinyExpr Fixes
#[test]
fn test_concat_with_empty_argument() {
    let src = r#"
#define __CONCAT(x,y) x ## y
__CONCAT(a,)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: a
    ");
}

#[test]
fn test_gcc_extension_keywords() {
    let src = r#"
__extension__
__restrict
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"[]");
}

// Macro Redefinition Tests (C11 6.10.3)
#[test]
fn test_identical_macro_redefinition_no_warning() {
    // C11 6.10.3: Identical macro redefinition is allowed without warning.
    // All whitespace separations are considered identical.
    let src = r#"
#define FOO 42
#define FOO 42
FOO
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Number
        text: "42"
    - []
    "#);
}

#[test]
fn test_different_macro_redefinition_warns() {
    // Different macro redefinition should produce a warning
    let src = r#"
#define FOO 42
#define FOO 43
FOO
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Number
        text: "43"
    - - "Error: Macro 'FOO' redefined with different value"
    "#);
}

#[test]
fn test_undef_builtin_macro_should_warn() {
    let src = r#"
#undef __DATE__
"#;
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!(diags, @r#"- "Warning: Undefining built-in macro '__DATE__'""#);
}

// Macro Expansion Coverage
#[test]
fn test_expand_tokens_magic_macro_coverage() {
    // This test targets the code path:
    // if let Some(magic) = self.try_expand_magic_macro(&token) {
    //     tokens[i] = magic;
    //     i += 1;
    //     continue;
    // }
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
    let src = r#"
#define P _Pragma("once")
P
"#;
    let tokens = setup_pp_snapshot(src);
    // The _Pragma("once") is handled and removed from the token stream.
    insta::assert_yaml_snapshot!(tokens, @"[]");
}

#[test]
fn test_identical_builtin_redefinition_no_warning() {
    // Identical redefinition of a built-in macro should not warn.
    let src = r#"
#define __STDC_IEC_559__ 1
__STDC_IEC_559__
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags), @r#"
    - - kind: Number
        text: "1"
    - []
    "#);
}

#[test]
fn test_macro_recursive_pasting() {
    // should not hanging on recursive pasting
    let source = r#"
#define CAT(a,b) a ## b
#define foobar CAT(foo, bar)
foobar
"#;

    let (_, result) = crate::tests::test_utils::run_pipeline(source, crate::driver::artifact::CompilePhase::Preprocess);
    assert!(result.is_ok());
}

// Regression test for macro expansion chain bug
// foo(X)(Y)(Z) should expand to "1 2 1 bar", not "1 2 foo(Z)"
// The bug was that is_recursive_expansion walked the entire include stack,
// blocking expansion of a macro just because it appeared somewhere in the
// expansion history, even when the current token is a fresh invocation.
#[test]
fn test_type_builtins() {
    let src = r#"
__SIZE_TYPE__
__PTRDIFF_TYPE__
__WCHAR_TYPE__
__WINT_TYPE__
__INTMAX_TYPE__
__UINTMAX_TYPE__
__SIZE_MAX__
__PTRDIFF_MAX__
__INTMAX_MAX__
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: unsigned
    - kind: Identifier
      text: long
    - kind: Identifier
      text: long
    - kind: Identifier
      text: int
    - kind: Identifier
      text: unsigned
    - kind: Identifier
      text: int
    - kind: Identifier
      text: long
    - kind: Identifier
      text: long
    - kind: Identifier
      text: unsigned
    - kind: Identifier
      text: long
    - kind: Identifier
      text: long
    - kind: Number
      text: 18446744073709551615UL
    - kind: Number
      text: 9223372036854775807L
    - kind: Number
      text: 9223372036854775807LL
    ");
}

#[test]
fn test_stddef_stdint_integration() {
    let src = r#"
#include <stddef.h>
#include <stdint.h>
size_t s;
ptrdiff_t p;
intmax_t i;
uintmax_t u;
"#;
    // We just want to make sure it preprocesses without errors
    let (_, diags) = setup_pp_snapshot_with_diags(src);
    assert!(diags.is_empty(), "Expected no diagnostics, got: {:?}", diags);
}

#[test]
fn test_macro_expansion_chain_not_blocked() {
    let src = r#"
#define foo(X) 1 bar
#define bar(X) 2 foo
foo(X)(Y)(Z)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    - kind: Number
      text: "2"
    - kind: Number
      text: "1"
    - kind: Identifier
      text: bar
    "#);
}

// Regression test for nested macro expansion with self-referential macros
// f(f(z)) should expand to "z[0]", not "z[0][0][0]"
// The bug was that when z expands to z[0] during argument prescan,
// the resulting z token in z[0] was being re-expanded during rescan
// because the hide-set (recursive expansion check) was not properly
// handling tokens that came from macro expansions.
#[test]
fn test_nested_macro_expansion_self_referential() {
    let src = r#"
#define f(a) a
#define z z[0]
f(f(z))
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: z
    - kind: LeftBracket
      text: "["
    - kind: Number
      text: "0"
    - kind: RightBracket
      text: "]"
    "#);
}

#[test]
fn test_deferred_macro_expansion() {
    let src = r#"
#define EMPTY
#define DEFER(x) x EMPTY
#define EXPAND() 42

DEFER(EXPAND)()
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: Identifier
      text: EXPAND
    - kind: LeftParen
      text: (
    - kind: RightParen
      text: )
    ");
}

#[test]
fn test_empty_macro_arg() {
    let src = r#"
#define M(x) x
int y = M();
"#;
    let Ok((_, diags)) = setup_preprocessor_test_with_diagnostics(src, None) else {
        panic!("PP Error");
    };
    assert!(diags.is_empty(), "Expected no diagnostics, got: {:?}", diags);
}

#[test]
fn test_recursive_expansion_issue() {
    let src = r#"
#define SELF SELF
int x = SELF;

#define A B
#define B A
int y = A;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Identifier
      text: SELF
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: int
    - kind: Identifier
      text: y
    - kind: Assign
      text: "="
    - kind: Identifier
      text: A
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_indirect_recursion_prosser() {
    let src = r#"
#define A(x) x B
#define B(y) y A
int x = A(1)(2)(3);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: int
    - kind: Identifier
      text: x
    - kind: Assign
      text: "="
    - kind: Number
      text: "1"
    - kind: Number
      text: "2"
    - kind: Number
      text: "3"
    - kind: Identifier
      text: B
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_stringification_escaping_literal() {
    let src = r#"
#define STR(x) #x
char *s1 = STR(  a    b  );
char *s2 = STR("quote");
char *s3 = STR(  a  \n  b  );
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s1
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"a b\""
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s2
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"\\\"quote\\\"\""
    - kind: Semicolon
      text: ;
    - kind: Identifier
      text: char
    - kind: Star
      text: "*"
    - kind: Identifier
      text: s3
    - kind: Assign
      text: "="
    - kind: StringLiteral
      text: "\"a \\n b\""
    - kind: Semicolon
      text: ;
    "#);
}

#[test]
fn test_deferred_expansion_nested_expand() {
    // Regression test for EXPAND(EXPAND(A())) where A() expands to A_I () 1
    let src = r#"
#define EXPAND(...) __VA_ARGS__
#define A_I() A
#define A() A_I () 1
EXPAND(EXPAND(A()))
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: A
    - kind: Number
      text: "1"
    "#);
}

#[test]
fn test_variadic_macro_rescan_bug() {
    // Regression test for variadic macro calls generated during rescan
    let src = r#"
#define EXPAND(...) __VA_ARGS__
#define F(x, ...) x __VA_ARGS__
EXPAND(F(1, 2, 3))
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    - kind: Number
      text: "2"
    - kind: Comma
      text: ","
    - kind: Number
      text: "3"
    "#);
}

#[test]
fn test_va_opt_basic() {
    let src = r#"
#define M(a, ...) a __VA_OPT__(+) __VA_ARGS__
M(1)
M(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    - kind: Number
      text: "1"
    - kind: Plus
      text: +
    - kind: Number
      text: "2"
    "#);
}

#[test]
fn test_va_opt_stringification() {
    let src = r#"
#define FOO BAR
#define M2(x,y,...) #__VA_OPT__(y##x __VA_ARGS__)
M2(a,b,FOO)
M2(a,b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"ba BAR\""
    - kind: StringLiteral
      text: "\"\""
    "#);
}

#[test]
fn test_va_opt_empty() {
    let src = r#"
#define M1(a, ...) a __VA_OPT__(,) __VA_ARGS__
M1(1)
M1(1, 2, 3)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    - kind: Number
      text: "1"
    - kind: Comma
      text: ","
    - kind: Number
      text: "2"
    - kind: Comma
      text: ","
    - kind: Number
      text: "3"
    "#);
}

// Regression test: `,##__VA_ARGS__` should only swallow comma when
// no variadic arguments are provided.  An explicit empty arg preserves it.
#[test]
fn test_gnu_comma_elision_with_empty_variadic_arg() {
    let src = r#"
#define M(x,y,...) x y ,##__VA_ARGS__
M(a,b,)
M(a,b)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Identifier
      text: a
    - kind: Identifier
      text: b
    - kind: Comma
      text: ","
    - kind: Identifier
      text: a
    - kind: Identifier
      text: b
    "#);
}

#[test]
fn test_int_constant_macros() {
    let src = r#"
__INT8_C(1)
__INT16_C(1)
__INT32_C(1)
__INT64_C(1)
__UINT8_C(1)
__UINT16_C(1)
__UINT32_C(1)
__UINT64_C(1)
__INTMAX_C(1)
__UINTMAX_C(1)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: Number
      text: "1"
    - kind: Number
      text: "1"
    - kind: Number
      text: "1"
    - kind: Number
      text: 1L
    - kind: Number
      text: "1"
    - kind: Number
      text: "1"
    - kind: Number
      text: 1U
    - kind: Number
      text: 1UL
    - kind: Number
      text: 1LL
    - kind: Number
      text: 1ULL
    "#);
}

#[test]
fn test_stdint_h_constant_macros() {
    let src = r#"
#include <stdint.h>
INT64_C(123)
UINT64_C(456)
"#;
    let tokens = setup_pp_snapshot(src);
    // Find the tokens we're interested in (they should be at the end)
    let last_tokens: Vec<_> = tokens.iter().rev().take(2).rev().collect();
    insta::assert_yaml_snapshot!(last_tokens, @"
    - kind: Number
      text: 123L
    - kind: Number
      text: 456UL
    ");
}

#[test]
fn test_nested_macro_expansion_in_args() {
    let src = r#"
#define CAST(t, e) ((t)(e))
#define CAST_U(o) CAST(unsigned, o)

CAST(unsigned, CAST_U(i))
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens, @"
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Identifier
      text: unsigned
    - kind: RightParen
      text: )
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: LeftParen
      text: (
    - kind: Identifier
      text: unsigned
    - kind: RightParen
      text: )
    - kind: LeftParen
      text: (
    - kind: Identifier
      text: i
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    - kind: RightParen
      text: )
    ");
}

#[test]
fn test_macro_invalid_parameters_and_edge_cases() {
    let src = r#"
#define FOO(a, 1) bar
#define BAR(a, a) bar
#define QUX(a ; b) bar
#define HASH1(a) #
HASH1(1)
#define HASH2(a) # 1
HASH2(1)
#define HASH3(a) # +
HASH3(1)
#define BAD_PARAM(1) bar
#define BAD_PARAM2(a, 1) bar
"#;
    let _ = crate::tests::pp_common::setup_preprocessor_test_with_diagnostics(src, None);

    let gnu_ellip_err = r#"
#define QUX2(args... b) bar
"#;
    let _ = crate::tests::pp_common::setup_preprocessor_test_with_diagnostics(gnu_ellip_err, None);

    let c99_ellip_err = r#"
#define BAZ2(..., b) bar
"#;
    let _ = crate::tests::pp_common::setup_preprocessor_test_with_diagnostics(c99_ellip_err, None);

    let src_stringify = r#"
#define STRINGIFY(...) #__VA_ARGS__
STRINGIFY(1)
"#;
    let tokens = crate::tests::pp_common::setup_pp_snapshot(src_stringify);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"1\""
    "#);
}
