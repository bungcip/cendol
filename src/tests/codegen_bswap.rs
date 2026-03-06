use super::codegen_common::run_c_code_exit_status;

#[test]
fn test_bswap16() {
    let code = r#"
        unsigned short test_bswap16(unsigned short x) {
            return __builtin_bswap16(x);
        }

        int main() {
            if (test_bswap16(0x1234) != 0x3412) return 1;
            if (test_bswap16(0x0000) != 0x0000) return 2;
            if (test_bswap16(0xFFFF) != 0xFFFF) return 3;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_bswap32() {
    let code = r#"
        unsigned int test_bswap32(unsigned int x) {
            return __builtin_bswap32(x);
        }

        int main() {
            if (test_bswap32(0x12345678) != 0x78563412) return 1;
            if (test_bswap32(0x00000000) != 0x00000000) return 2;
            if (test_bswap32(0xFFFFFFFF) != 0xFFFFFFFF) return 3;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_bswap64() {
    let code = r#"
        unsigned long long test_bswap64(unsigned long long x) {
            return __builtin_bswap64(x);
        }

        int main() {
            if (test_bswap64(0x123456789ABCDEF0ULL) != 0xF0DEBC9A78563412ULL) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_bswap_nested() {
    let code = r#"
        int main() {
            unsigned int x = 0x12345678;
            if (__builtin_bswap32(__builtin_bswap32(x)) != x) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_bswap_types() {
    let code = r#"
        int main() {
            // Test with different integer types (should promote/cast correctly)
            unsigned short s = 0x1234;
            if (__builtin_bswap16(s) != 0x3412) return 1;

            unsigned int i = 0x12345678;
            if (__builtin_bswap32(i) != 0x78563412) return 2;

            unsigned char c = 0x12;
            // __builtin_bswap16 expects uint16_t, 'unsigned char' should promote to 'int' then cast to 'uint16_t'
            // 0x0012 -> 0x1200
            if (__builtin_bswap16(c) != 0x1200) return 3;

            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_bswap_side_effects() {
    let code = r#"
        unsigned int global = 0;
        unsigned int get_val() {
            global++;
            return 0x12345678;
        }
        int main() {
            unsigned int res = __builtin_bswap32(get_val());
            if (res != 0x78563412) return 1;
            if (global != 1) return 2;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}
