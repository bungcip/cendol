use crate::tests::pp_common::{assert_pp, setup_multi_file_pp_snapshot, check_diag};


#[test]
fn test_ifdef_ifndef_elif() {
    // 1. Basic ifdef / ifndef
    assert_pp("#define FOO\n#ifdef FOO\nOK\n#endif", "OK");
    assert_pp("#ifdef FOO\nFAIL\n#endif\nOK", "OK");
    assert_pp("#define FOO\n#ifndef FOO\nFAIL\n#endif\nOK", "OK");
    assert_pp("#ifndef FOO\nOK\n#endif", "OK");

    // 2. Else
    assert_pp("#define FOO\n#ifdef FOO\nOK\n#else\nFAIL\n#endif", "OK");
    assert_pp("#ifdef FOO\nFAIL\n#else\nOK\n#endif", "OK");

    // 3. Elif basic
    assert_pp("#if 0\nFAIL\n#elif 1\nOK\n#endif", "OK");
    assert_pp("#if 0\nFAIL\n#elif 0\nFAIL\n#else\nOK\n#endif", "OK");
    assert_pp("#if 1\nOK\n#elif 1\nFAIL\n#endif", "OK");

    // 4. Elifdef / Elifndef
    assert_pp("#define FOO\n#if 0\nFAIL\n#elifdef FOO\nOK\n#endif", "OK");
    assert_pp("#if 0\nFAIL\n#elifdef FOO\nFAIL2\n#else\nOK\n#endif", "OK");
    assert_pp("#define FOO\n#if 0\nFAIL\n#elifndef FOO\nFAIL2\n#else\nOK\n#endif", "OK");
    assert_pp("#if 0\nFAIL\n#elifndef FOO\nOK\n#endif", "OK");

    // 5. Nested
    assert_pp("#define FOO\n#define BAR\n #ifdef FOO\n #ifdef BAR\n OK\n #endif\n#endif", "OK");
    assert_pp("#define FOO\n#ifdef FOO\n #ifdef BAR\n FAIL\n #else\n OK\n #endif\n#endif", "OK");
    assert_pp("#if 0\n #if 1\n FAIL\n #elif 1\n FAIL\n #else\n FAIL\n #endif\n#endif\nOK", "OK");
    assert_pp("#if 1\n #if 0\n FAIL\n #elif 1\n OK\n #endif\n#endif", "OK");

    // 6. Chains and multiple elifs
    assert_pp("#ifdef FOO\nFAIL\n#elif 1\nOK\n#endif", "OK");
    assert_pp("#if 0\nFAIL_1\n#elif 0\nFAIL_2\n#elif 1\nOK\n#elif 1\nFAIL_3\n#else\nFAIL_4\n#endif", "OK");
}

#[test]
fn test_skipping_rules() {
    // skipped text is completely ignored
    assert_pp("#if 0\nignored text here\n#endif\nOK", "OK");
    // nested skipped ifs expression is not evaluated (no division by zero error)
    assert_pp("#if 0\n#if 1\nFAIL\n#elif 1/0\nFAIL\n#endif\n#endif\nOK", "OK");
    // nested skipped ifs
    assert_pp("#if 0\n#if 1\n#else\n#endif\n#endif\nOK", "OK");
}

#[test]
fn test_logical_operators() {
    assert_pp("#if 1 && 1\nOK\n#else\nFAIL\n#endif", "OK");
    assert_pp("#if 1 && 0\nFAIL\n#else\nOK\n#endif", "OK");
    assert_pp("#if 0 || 1\nOK\n#else\nFAIL\n#endif", "OK");
    assert_pp("#if 0 || 0\nFAIL\n#else\nOK\n#endif", "OK");
    assert_pp("#if !0\nOK\n#else\nFAIL\n#endif", "OK");
    assert_pp("#if !1\nFAIL\n#else\nOK\n#endif", "OK");
    assert_pp("#if (1 && 0) || (!0 && 1)\nOK\n#else\nFAIL\n#endif", "OK");
}

#[test]
fn test_constant_expressions() {
    // defined operator
    assert_pp("#define FOO\n#if defined(FOO)\nOK\n#endif", "OK");
    assert_pp("#if defined FOO\nFAIL\n#else\nOK\n#endif", "OK");
    // comparisons
    assert_pp("#if 5 > 3\nOK\n#endif", "OK");
    assert_pp("#if 2 == 2\nOK\n#endif", "OK");
    assert_pp("#if 1 != 2\nOK\n#endif", "OK");
    // arithmetic
    assert_pp("#if 2 + 3 == 5\nOK\n#endif", "OK");
    assert_pp("#if 10 - 4 * 2 == 2\nOK\n#endif", "OK");
    // nested parentheses
    assert_pp("#if (2 + 3) * 4 == 20\nOK\n#endif", "OK");
    // macro expansion
    assert_pp("#define VAL 5\n#if VAL == 5\nOK\n#endif", "OK");
    // hex/octal
    assert_pp("#if 0x10 == 16\nOK\n#endif", "OK");
    assert_pp("#if 010 == 8\nOK\n#endif", "OK");
    // char literal
    assert_pp("#if 'a' == 97\nOK\n#endif", "OK");
    // negative numbers
    assert_pp("#if -5 + 5 == 0\nOK\n#endif", "OK");
    // conditional operator (?:)
    assert_pp("#if 1 ? 1 : 0\nTRUE\n#else\nFALSE\n#endif", "TRUE");
    assert_pp("#if 0 ? 1 : 0\nFALSE\n#else\nTRUE\n#endif", "TRUE");
    assert_pp("#if (1 ? 2 : 3) == 2\nOK\n#endif", "OK");
    assert_pp("#if (1 ? -1 : 1U) > 0\nUNSIGNED\n#else\nSIGNED\n#endif", "UNSIGNED");
    assert_pp("#if (1 ? -1 : 0) > 0\nUNSIGNED\n#else\nSIGNED\n#endif", "SIGNED");
}

#[test]
fn test_pp_binary_operators_coverage() {
    // LogicAnd Short-circuit (division by zero inside short-circuited RHS does not trigger)
    assert_pp("#if 0 && (1/0)\nFAIL\n#else\nOK\n#endif", "OK");
    // LogicOr Short-circuit
    assert_pp("#if 1 || (1/0)\nOK\n#else\nFAIL\n#endif", "OK");
    // Bitwise operators
    assert_pp("#if (1 | 2) == 3\nOK\n#endif", "OK");
    assert_pp("#if (3 ^ 1) == 2\nOK\n#endif", "OK");
    assert_pp("#if (3 & 1) == 1\nOK\n#endif", "OK");
    // Relational and shifts
    assert_pp("#if 1 <= 1\nOK\n#endif", "OK");
    assert_pp("#if 1 <= 2\nOK\n#endif", "OK");
    assert_pp("#if 1 >= 1\nOK\n#endif", "OK");
    assert_pp("#if 2 >= 1\nOK\n#endif", "OK");
    assert_pp("#if (1 << 1) == 2\nOK\n#endif", "OK");
    assert_pp("#if (2U >> 1) == 1\nOK\n#endif", "OK");
    assert_pp("#if (-2 >> 1) == -1\nOK\n#endif", "OK");
    // Mul, div, mod
    assert_pp("#if 10U / 2U == 5U\nOK\n#endif", "OK");
    assert_pp("#if -10 / 2 == -5\nOK\n#endif", "OK");
    assert_pp("#if 10U % 3U == 1U\nOK\n#endif", "OK");
    assert_pp("#if -10 % 3 == -1\nOK\n#endif", "OK");
    // Signed vs unsigned comparison
    assert_pp("#if -1 < 0\nOK\n#else\nFAIL\n#endif", "OK");
}

#[test]
fn test_pp_unary_operators_coverage() {
    assert_pp("#if +1 == 1\nPLUS_OK\n#endif", "PLUS_OK");
    assert_pp("#if ~0 == -1\nBITNOT_SIGNED_OK\n#endif", "BITNOT_SIGNED_OK");
    assert_pp("#if ~0U == 0xFFFFFFFFFFFFFFFFU\nBITNOT_UNSIGNED_OK\n#endif", "BITNOT_UNSIGNED_OK");
    assert_pp("#if !0\nLOGICNOT_0_OK\n#endif", "LOGICNOT_0_OK");
    assert_pp("#if !1\nLOGICNOT_1_FAIL\n#else\nLOGICNOT_1_OK\n#endif", "LOGICNOT_1_OK");
}

#[test]
fn test_has_include_builtin() {
    assert_pp("#if __has_include(<stddef.h>)\nOK\n#endif", "OK");

    let files = vec![
        ("header.h", "int z = 3;"),
        ("main.c", "#if __has_include(\"header.h\")\nOK\n#endif"),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "OK");
}

#[test]
fn test_has_include_next_builtin() {
    let files = vec![
        ("header.h", "int z = 3;"),
        ("main.c", "#if __has_include_next(\"header.h\")\nOK\n#else\nMISSING\n#endif"),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].text, "OK");
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
#endif
#if __has_include(LOCAL_HEADER)
OK_LOCAL
#endif
#if __has_include(INDIRECT_STD)
OK_INDIRECT_STD
#endif
#if __has_include(INDIRECT_LOCAL)
OK_INDIRECT_LOCAL
#endif
"#;
    assert_pp(src, "OK_STD\nOK_LOCAL\nOK_INDIRECT_STD\nOK_INDIRECT_LOCAL");
}

#[test]
fn test_pp_arithmetic_overflow() {
    let src = r#"
#if ((-9223372036854775807 - 1) / -1) == (-9223372036854775807 - 1)
OK_DIV_OVERFLOW
#endif
#if ((-9223372036854775807 - 1) % -1) == 0
OK_MOD_OVERFLOW
#endif
"#;
    assert_pp(src, "OK_DIV_OVERFLOW\nOK_MOD_OVERFLOW");
}

#[test]
fn test_pp_conditional_diagnostics() {
    check_diag("#if 0\n#else\n#elif 1\n#endif", "ElifAfterElse");
    check_diag("#elif 1", "ElifWithoutIf");
    check_diag("#elifdef FOO\nFAIL", "ElifWithoutIf");
    check_diag("#elifndef FOO\nFAIL", "ElifWithoutIf");
    check_diag("#if 1 / 0\nOK\n#endif", "DivisionByZero");
    check_diag("#if 1 % 0\nOK\n#endif", "RemainderByZero");
    check_diag("#if 1 + (2 * 3\n#endif", "InvalidConditionalExpression");
    check_diag("#if\n#endif", "InvalidConditionalExpression");
    check_diag("#if defined(FOO\n#endif", "InvalidConditionalExpression");
    check_diag("#if defined(5)\n#endif", "InvalidConditionalExpression");
}
