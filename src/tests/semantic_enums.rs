use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::{find_enum_constant, setup_lowering};
use crate::tests::test_utils::{run_fail_with_message, run_pass, run_pass_with_diagnostic};

#[test]
fn test_enum_constant_expression_basic() {
    let source = r#"
    enum E {
        A = 1 + 2,
        B = 10,
        C = 5 * 2
    };
    "#;

    let (_, _, symbol_table) = setup_lowering(source);

    assert_eq!(find_enum_constant(&symbol_table, "A"), 3, "Enum A should be 3");
    assert_eq!(find_enum_constant(&symbol_table, "B"), 10, "Enum B should be 10");
    assert_eq!(find_enum_constant(&symbol_table, "C"), 10, "Enum C should be 10");
}

#[test]
fn test_enum_constant_expression_reference() {
    let source = r#"
    enum E {
        A = 10,
        B = A + 5
    };
    "#;

    let (_, _, symbol_table) = setup_lowering(source);

    // This is expected to fail or be incorrect with current implementation
    assert_eq!(find_enum_constant(&symbol_table, "B"), 15, "Enum B should be 15");
}

#[test]
fn test_enum_int_negative() {
    // Enum fits in signed int (min < 0, but within i32 range)
    let code = r#"
        enum E { A = -1 };
        int main() {
            _Static_assert(_Generic((enum E)0, int: 1, default: 0), "expected int");
            return 0;
        }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_enum_unsigned_long_long() {
    // Enum > u32 max. Should be unsigned long long.
    // 4294967296 is 2^32.
    let code = r#"
        enum E { A = 4294967296 };
        int main() {
            // Depending on platform, this might be unsigned long or unsigned long long.
            // On 64-bit Linux, long is 64-bit, so it might fit there too.
            // But my implementation logic:
            // if min >= 0:
            //   if max <= u32_max: uint
            //   else: ulonglong (hardcoded fallback)
            _Static_assert(_Generic((enum E)0, unsigned long long: 1, default: 0), "expected unsigned long long");
            return 0;
        }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_enum_long_long_too_small() {
    // Enum < i32 min. Should be long long.
    // -2147483649
    let code = r#"
        enum E { A = -2147483649 };
        int main() {
            // Implementation logic:
            // min < 0 -> not uint.
            // min < int_min -> not int.
            // Fallback: long long.
            _Static_assert(_Generic((enum E)0, long long: 1, default: 0), "expected long long");
            return 0;
        }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_enum_long_long_mixed_range() {
    // Enum has negative value AND positive value > i32 max.
    // Cannot be int (too big). Cannot be uint (negative).
    // Should be long long.
    let code = r#"
        enum E { A = -1, B = 2147483648 };
        int main() {
            _Static_assert(_Generic((enum E)0, long long: 1, default: 0), "expected long long");
            return 0;
        }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn warns_on_large_enum_constant() {
    let source = "enum T { A = 4294967296LL };";
    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "enumerator value 4294967296 for 'A' is not representable as 'int'",
        1,
        10,
    );
}

#[test]
fn accepts_boundary_enum_constants() {
    let source = "
        enum T {
            MAX_INT = 2147483647,
            MIN_INT = -2147483648
        };
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn warns_on_overflow_next_value() {
    let source = "enum T { A = 2147483647, B };";
    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "enumerator value 2147483648 for 'B' is not representable as 'int'",
        1,
        26,
    );
}

#[test]
fn warns_on_underflow_large_negative() {
    let source = "enum T { A = -2147483649LL };";
    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "enumerator value -2147483649 for 'A' is not representable as 'int'",
        1,
        10,
    );
}

#[test]
fn warns_on_extreme_i64_values() {
    let source = "enum T { A = 9223372036854775807LL };";
    run_pass_with_diagnostic(
        source,
        CompilePhase::Mir,
        "enumerator value 9223372036854775807 for 'A' is not representable as 'int'",
        1,
        10,
    );
}

#[test]
fn test_enum_redefinition_enumerator() {
    run_fail_with_message(
        r#"
        enum E {
            A,
            B,
            A
        };
        "#,
        "redefinition",
    );
}

#[test]
fn test_enumerator_outside_enum() {
    run_fail_with_message(
        r#"
        enum E { A, B };
        int main() {
            int x = C;
        }
        "#,
        "Undeclared",
    );
}

#[test]
fn test_enum_init_with_other_enum() {
    let source = r#"
enum A { A1 = 10 };
enum B { B1 = A1 };

int main() {
    return 0;
}
"#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_enum_init_with_other_enum_indirect() {
    let source = r#"
enum tree_code {
  SOME_CODE = 148,
  LAST_AND_UNUSED_TREE_CODE
};
enum c_tree_code {
  C_DUMMY_TREE_CODE = LAST_AND_UNUSED_TREE_CODE,
  STMT_EXPR,
  LAST_C_TREE_CODE
};
enum cplus_tree_code {
  CP_DUMMY_TREE_CODE = LAST_C_TREE_CODE,
  AMBIG_CONV,
  LAST_CPLUS_TREE_CODE
};

int main() {
    return 0;
}
"#;
    run_pass(source, CompilePhase::Mir);
}

// Regression tests for enum underlying type selection and _Generic matching.
// These cover the cases from BUGS.txt (lines 274-333).
#[test]
fn test_enum_generic_underlying_type_e0() {
    // e0: values all fit in int, underlying type = int
    let code = r#"
        enum e0 { e0_i32max = 0x7FFFFFFF };
        _Static_assert(_Generic(e0_i32max, int:1, default:0), "e0_i32max should be int");
        _Static_assert(_Generic((enum e0)0, int:1, default:0), "enum e0 should be int");
        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_enum_generic_underlying_type_e1() {
    // e1: has a value exceeding int max (0x7FFFFFFF + 1 = 0x80000000) -> unsigned int
    let code = r#"
        enum e1 { e1_i32max = 0x7FFFFFFF, e1_i32max_plus1 };
        _Static_assert(_Generic(e1_i32max, unsigned int:1, default:0), "e1_i32max should be unsigned int");
        _Static_assert(_Generic((enum e1)0, unsigned int:1, default:0), "enum e1 should be unsigned int");
        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}

#[test]
fn test_enum_generic_underlying_type_e5() {
    // e5: has u32 max and a negative value -> long long
    let code = r#"
        enum e5 { e5_u32max = 0xFFFFFFFF, e5_neg = -1 };
        _Static_assert(_Generic(e5_u32max, long long:1, default:0), "e5_u32max should be long long");
        _Static_assert(_Generic((enum e5)0, long long:1, default:0), "enum e5 should be long long");
        int main() { return 0; }
    "#;
    run_pass(code, CompilePhase::Mir);
}
