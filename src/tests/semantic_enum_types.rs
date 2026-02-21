use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

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
