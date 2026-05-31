use crate::pp::PPConfig;
use crate::tests::pp_common::{
    assert_pp, preprocess_to_str, setup_pp_snapshot, setup_pp_snapshot_with_diags,
    setup_pp_snapshot_with_diags_and_config, setup_pp_with_sm_and_diagnostics,
};
use chrono::{TimeZone, Utc};

// Basic macro tests
#[test]
fn test_simple_macro_definition_and_expansion() {
    assert_pp("#define TEN OK\nTEN", "OK");
}

#[test]
fn test_parameter_macro_definition_and_expansion() {
    assert_pp(
        "#define ADD(a,b) ( (a) + (b) )\nADD(1, 2)",
        "( (1) + ( 2) )",
    );
}

#[test]
fn test_complex_macro_expansion_and_recursion_limit() {
    assert_pp(
        "#define ID(x) x\n#define A ID(ID(ID(1)))\nA",
        "1",
    );
}

#[test]
fn test_defer_recursive_expansion() {
    assert_pp(
        r#"#define EMPTY()
#define DEFER(id) id EMPTY()
#define EXPAND(...) __VA_ARGS__
#define BAR_I() BAR
#define BAR()  DEFER(BAR_I)()() 1
EXPAND(EXPAND(BAR()))"#,
        "BAR_I()() 1 1 1",
    );
}

#[test]
fn test_function_like_macro_not_expanded_when_not_followed_by_paren() {
    assert_pp(
        "#define x(y) ((y) + 1)\nint x = x(0);",
        "int x = ((0) + 1);",
    );
}

// Stringification (#)
#[test]
fn test_stringification_whitespace_handling() {
    assert_pp(
        "#define STR(x) #x\nSTR(a + b)",
        r#""a + b""#,
    );
}

#[test]
fn test_va_args_stringification() {
    assert_pp(
        "#define STR(...) #__VA_ARGS__\nSTR(a, b, c)",
        r#""a, b, c""#,
    );
}

// Token Pasting (##)
#[test]
fn test_paste_numbers() {
    assert_pp(
        "#define PASTE(a,b) a ## b\nPASTE(1, 2)",
        "12",
    );
}

#[test]
fn test_paste_va_args() {
    assert_pp(
        "#define PASTE(...) prefix ## __VA_ARGS__\nPASTE(a, b)",
        "prefixa\n, b",
    );
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
    assert_pp("__FILE__", r#""<test>""#);
}

#[test]
fn test_counter_macro() {
    assert_pp(
        "__COUNTER__\n__COUNTER__\n__COUNTER__",
        "0\n1\n2",
    );
}

// Macro Argument Parsing
#[test]
fn test_brace_comma_separation() {
    let src = r#"
#define CNT(x, y) 2
CNT({1, 2})
"#;
    let (tokens, _, _) = setup_pp_with_sm_and_diagnostics(src, None).unwrap();
    assert!(tokens.iter().any(|t| t.text == "2"));
}

#[test]
fn test_paren_comma_protection() {
    assert_pp(
        "#define ID(x) x\n#if 1\n(ID((1, 2)))\nOK\n#endif",
        "((1, 2))\nOK",
    );
}

// GNU Extensions
#[test]
fn test_gnu_named_variadic_macros() {
    assert_pp(
        "#define M(a, args...) args\nM(1, 2, 3, 4)",
        "2, 3, 4",
    );
}

#[test]
fn test_gnu_comma_swallowing() {
    assert_pp(
        "#define M(a, args...) a, ## args\nM(1)",
        "1",
    );
}

#[test]
fn test_gnu_comma_swallowing_va_args() {
    assert_pp(
        "#define LOG(fmt, ...) printf(fmt, ##__VA_ARGS__)\nLOG(\"foo\");\nLOG(\"bar\", 1);",
        "printf(\"foo\");\nprintf(\"bar\",1\n);",
    );
}

// Regressions
#[test]
fn test_recursive_macro_expansion_regression() {
    assert_pp(
        "#define CAT2(a, b) a ## b\n#define CAT(a, b) CAT2(a, b)\n#define AB(x) CAT(x, y)\nint res = AB(x);",
        "int res = xy;",
    );
}

// Magic Macros
#[test]
fn test_magic_macros() {
    assert_pp(
        "__LINE__\n__FILE__\n__COUNTER__\n__COUNTER__",
        "1\n\"<test>\"\n0\n1",
    );
}

// Placemarkers
#[test]
fn test_placemarker_concatenation() {
    assert_pp("#define M(a, b) a ## b\nM(, 1)", "1");
}

#[test]
fn test_placemarker_concatenation_with_prefix() {
    assert_pp("#define M(a, b) X a ## b\nM(, 1)", "X 1");
}

#[test]
fn test_placemarker_concatenation_chained() {
    assert_pp("#define M(a, b, c) a ## b ## c\nM(, , C)", "C");
}

// GCC Compatibility
#[test]
fn test_gcc_version_macros() {
    assert_pp(
        "__GNUC__\n__GNUC_MINOR__\n__GNUC_PATCHLEVEL__",
        "4\n2\n1",
    );
}

// Regression Tests for TinyExpr Fixes
#[test]
fn test_concat_with_empty_argument() {
    assert_pp("#define __CONCAT(x,y) x ## y\n__CONCAT(a,)", "a");
}

#[test]
fn test_gcc_extension_keywords() {
    assert_pp("__extension__\n__restrict", "");
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
    assert_pp("#define M __LINE__\nM", "1");
}

#[test]
fn test_expand_tokens_pragma_operator_coverage() {
    // This test targets the code path:
    // if self.try_handle_pragma_operator(tokens, i) {
    //     continue;
    // }
    // The _Pragma("once") is handled and removed from the token stream.
    assert_pp("#define P _Pragma(\"once\")\nP", "");
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
    assert_pp(
        r#"__SIZE_TYPE__
__PTRDIFF_TYPE__
__WCHAR_TYPE__
__WINT_TYPE__
__INTMAX_TYPE__
__UINTMAX_TYPE__
__SIZE_MAX__
__PTRDIFF_MAX__
__INTMAX_MAX__"#,
        "unsigned long\nlong\nint\nunsigned int\nlong long\nunsigned long long 18446744073709551615UL 9223372036854775807L 9223372036854775807LL",
    );
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
    assert_pp(
        "#define foo(X) 1 bar\n#define bar(X) 2 foo\nfoo(X)(Y)(Z)",
        "1 2 1 bar",
    );
}

// Regression test for nested macro expansion with self-referential macros
// f(f(z)) should expand to "z[0]", not "z[0][0][0]"
// The bug was that when z expands to z[0] during argument prescan,
// the resulting z token in z[0] was being re-expanded during rescan
// because the hide-set (recursive expansion check) was not properly
// handling tokens that came from macro expansions.
#[test]
fn test_nested_macro_expansion_self_referential() {
    assert_pp(
        "#define f(a) a\n#define z z[0]\nf(f(z))",
        "z[0]",
    );
}

#[test]
fn test_deferred_macro_expansion() {
    assert_pp(
        "#define EMPTY\n#define DEFER(x) x EMPTY\n#define EXPAND() 42\n\nDEFER(EXPAND)()",
        "EXPAND()",
    );
}

#[test]
fn test_empty_macro_arg() {
    let src = r#"
#define M(x) x
int y = M();
"#;
    let Ok((_, _, diags)) = setup_pp_with_sm_and_diagnostics(src, None) else {
        panic!("PP Error");
    };
    assert!(diags.is_empty(), "Expected no diagnostics, got: {:?}", diags);
}

#[test]
fn test_recursive_expansion_issue() {
    assert_pp(
        "#define SELF SELF\nint x = SELF;\n\n#define A B\n#define B A\nint y = A;",
        "int x = SELF;\nint y = A;",
    );
}

#[test]
fn test_indirect_recursion_prosser() {
    assert_pp(
        "#define A(x) x B\n#define B(y) y A\nint x = A(1)(2)(3);",
        "int x = 1 2 3 B;",
    );
}

#[test]
fn test_stringification_escaping_literal() {
    let output = preprocess_to_str(
        r#"#define STR(x) #x
char *s1 = STR(  a    b  );
char *s2 = STR("quote");
char *s3 = STR(  a  \n  b  );"#,
    );
    let trimmed = output.trim().replace("\n\n", "\n");
    assert!(trimmed.contains(r#""a b""#), "s1 should stringify with normalized whitespace: {}", trimmed);
    assert!(trimmed.contains(r#""\"quote\"""#), "s2 should escape quotes: {}", trimmed);
    assert!(trimmed.contains(r#""a \n b""#), "s3 should preserve backslash-n: {}", trimmed);
}

#[test]
fn test_deferred_expansion_nested_expand() {
    // Regression test for EXPAND(EXPAND(A())) where A() expands to A_I () 1
    assert_pp(
        "#define EXPAND(...) __VA_ARGS__\n#define A_I() A\n#define A() A_I () 1\nEXPAND(EXPAND(A()))",
        "A 1",
    );
}

#[test]
fn test_variadic_macro_rescan_bug() {
    // Regression test for variadic macro calls generated during rescan
    assert_pp(
        "#define EXPAND(...) __VA_ARGS__\n#define F(x, ...) x __VA_ARGS__\nEXPAND(F(1, 2, 3))",
        "1 2, 3",
    );
}

#[test]
fn test_va_opt_basic() {
    assert_pp(
        "#define M(a, ...) a __VA_OPT__(+) __VA_ARGS__\nM(1)\nM(1, 2)",
        "1\n1+ 2",
    );
}

#[test]
fn test_va_opt_stringification() {
    assert_pp(
        "#define FOO BAR\n#define M2(x,y,...) #__VA_OPT__(y##x __VA_ARGS__)\nM2(a,b,FOO)\nM2(a,b)",
        "\"ba BAR\" \"\"",
    );
}

#[test]
fn test_va_opt_empty() {
    assert_pp(
        "#define M1(a, ...) a __VA_OPT__(,) __VA_ARGS__\nM1(1)\nM1(1, 2, 3)",
        "1\n1, 2, 3",
    );
}

// Regression test: `,##__VA_ARGS__` should only swallow comma when
// no variadic arguments are provided.  An explicit empty arg preserves it.
#[test]
fn test_gnu_comma_elision_with_empty_variadic_arg() {
    assert_pp(
        "#define M(x,y,...) x y ,##__VA_ARGS__\nM(a,b,)\nM(a,b)",
        "a b ,\na b",
    );
}

#[test]
fn test_int_constant_macros() {
    assert_pp(
        "__INT8_C(1)\n__INT16_C(1)\n__INT32_C(1)\n__INT64_C(1)\n__UINT8_C(1)\n__UINT16_C(1)\n__UINT32_C(1)\n__UINT64_C(1)\n__INTMAX_C(1)\n__UINTMAX_C(1)",
        "1\n1\n1\n1L\n1\n1\n1U\n1UL\n1LL\n1ULL",
    );
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
    assert_pp(
        "#define CAST(t, e) ((t)(e))\n#define CAST_U(o) CAST(unsigned, o)\n\nCAST(unsigned, CAST_U(i))",
        "((unsigned)( ((unsigned)( i))))",
    );
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
    let _ = setup_pp_with_sm_and_diagnostics(src, None);

    let gnu_ellip_err = r#"
#define QUX2(args... b) bar
"#;
    let _ = setup_pp_with_sm_and_diagnostics(gnu_ellip_err, None);

    let c99_ellip_err = r#"
#define BAZ2(..., b) bar
"#;
    let _ = setup_pp_with_sm_and_diagnostics(c99_ellip_err, None);

    let src_stringify = r#"
#define STRINGIFY(...) #__VA_ARGS__
STRINGIFY(1)
"#;
    let tokens = setup_pp_snapshot(src_stringify);
    insta::assert_yaml_snapshot!(tokens, @r#"
    - kind: StringLiteral
      text: "\"1\""
    "#);
}

#[test]
fn test_define_with_trailing_comment() {
    assert_pp("#define FOO 1 // comment\nFOO", "1");
}

#[test]
fn test_directive_in_macro_args() {
    let output = preprocess_to_str(
        r#"#define BUILD_ARRAY(x, y, z) { x, y, z }
#define USE_FEATURE_B 1

int my_array[] = BUILD_ARRAY(
    10,
#if USE_FEATURE_B
    20,
#else
    99,
#endif
    30
);"#,
    );
    let trimmed = output.trim().replace("\n\n", "\n");
    // The output preserves original spacing; just check the key tokens are present
    assert!(trimmed.contains("int my_array[]"), "should have declaration: {}", trimmed);
    assert!(trimmed.contains("10,"), "should have first arg: {}", trimmed);
    assert!(trimmed.contains("20,"), "should have conditional arg: {}", trimmed);
    assert!(trimmed.contains("30"), "should have third arg: {}", trimmed);
    assert!(!trimmed.contains("99"), "should NOT have else branch: {}", trimmed);
}

#[test]
fn test_counter_macro_pasting_no_prescan() {
    assert_pp(
        "#define STRINGIFY(x) #x\n#define PASTE(x, y) x ## y\n#define EVAL(x) x\n\nSTRINGIFY(__COUNTER__)\nPASTE(x, __COUNTER__)\nEVAL(__COUNTER__)",
        "\"__COUNTER__\"\nx__COUNTER__\n0",
    );
}
