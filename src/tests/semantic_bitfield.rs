use super::codegen_common::run_c_code_with_output;
use crate::tests::test_utils::run_pipeline_to_mir;

#[test]
fn test_nameless_bitfield_init_repro_output() {
    let code = r#"
        int printf(const char *format, ...);
        struct S {
            int f0;
            unsigned : 1;
            int f1;
            int f2;
        } g = {1, 2, 3};

        int main() {
            printf("%d %d %d", g.f0, g.f1, g.f2);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "1 2 3");
}

#[test]
fn test_complex_bitfield_init_shift() {
    // This mirrors the reported issue where a nameless bit-field caused a shift
    let code = r#"
        int printf(const char *format, ...);
        struct {
          int f0;
          int f1;
          int f2;
          int f3;
          unsigned : 0;
          int f4;
          unsigned f5;
          unsigned short f6;
          long long f7;
        } g = {0, 1, 2, 3, 4, 5, 6, 7};

        int main() {
            // If the nameless bit-field :0 is correctly skipped:
            // 0 -> f0
            // 1 -> f1
            // 2 -> f2
            // 3 -> f3
            // (skip :0)
            // 4 -> f4
            // 5 -> f5
            // 6 -> f6
            // 7 -> f7
            printf("%d %d %d %d %d %u %hu %lld", g.f0, g.f1, g.f2, g.f3, g.f4, g.f5, g.f6, g.f7);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(code);
    assert_eq!(output.trim(), "0 1 2 3 4 5 6 7");
}

#[test]
fn test_bitfield_promotion() {
    let src = r#"
        #define IS_INT(x) _Generic((x), int: 1, default: 0)

        int main() {
            struct { unsigned b : 3; } s = {0};
            
            // Unsigned bit-field of width 3 should be promoted to 'int' since it can
            // represent all values of the bit-field (0-7).
            _Static_assert(IS_INT(~s.b), "~s.b should be promoted to int");
            _Static_assert(IS_INT(~({s.b;})), "~({s.b;}) should be promoted to int");
            _Static_assert(IS_INT(~(s.b)), "~(s.b) should be promoted to int");
            _Static_assert(IS_INT(~({(s.b);})), "~({(s.b);}) should be promoted to int");

            return 0;
        }
    "#;
    run_pipeline_to_mir(src);
}

#[test]
fn test_bitfield_promotion_unsigned() {
    let src = r#"
        #define IS_UINT(x) _Generic((x), unsigned int: 1, default: 0)

        int main() {
            // 32-bit unsigned bit-field cannot fit in (32-bit) signed int.
            struct { unsigned b : 32; } s = {0};
            
            _Static_assert(IS_UINT(~s.b), "~s.b (32-bit) should be promoted to unsigned int");
            
            return 0;
        }
    "#;
    run_pipeline_to_mir(src);
}

#[test]
fn test_struct_bitfield_parsing_and_layout() {
    let source = r#"
        #include <stdint.h>

        // Test parser fix: comma in bitfield width doesn't consume it
        struct S2 {
            int :1, a, :1, b;
        };

        // Test packing of unnamed bitfields
        struct S4 {
            unsigned a : 1;
            unsigned : 1;
            unsigned b : 1;
        };

        // Test signed bitfield sign extension
        struct S5 {
            int i : 2;
        };

        int main() {
            // S2 parsing and initialization
            struct S2 s2 = {1, 2}; // S2.a = 1, S2.b = 2 (unnamed bitfields skipped)
            if (s2.a != 1) return 1;
            if (s2.b != 2) return 2;

            // S4 packing: should be 4 bytes
            if (sizeof(struct S4) != 4) return 3;

            // S5 sign extension
            struct S5 s5;
            s5.i = -1;
            if (s5.i != -1) return 4;

            s5.i = 1;
            if (s5.i != 1) return 5;

            return 0;
        }
    "#;
    assert_eq!(crate::tests::codegen_common::run_c_code_exit_status(source), 0);
}

#[test]
fn test_bitfield_assignment_truncation() {
    let source = r#"
        struct S {
            int i : 2;
            unsigned j : 2;
        } s;
        int main() {
            int x = s.i = -5; // -5 is ...11111011, last 2 bits are 11 -> -1 (signed)
            int y = s.j = 5;  // 5 is ...00000101, last 2 bits are 01 -> 1
            if (x != -1) return 1;
            if (y != 1) return 2;
            if (s.i != -1) return 3;
            if (s.j != 1) return 4;
            return 0;
        }
    "#;
    assert_eq!(crate::tests::codegen_common::run_c_code_exit_status(source), 0);
}

#[test]
fn test_anonymous_bitfield_alignment() {
    let source = r#"
        struct S {
            char a;
            int : 0; // force alignment to next int
            char b;
        };
        int main() {
            // offset of b should be 4 if int is 4-byte aligned
            struct S s;
            char *p1 = &s.a;
            char *p2 = &s.b;
            if (p2 - p1 < 4) return 1;
            return 0;
        }
    "#;
    assert_eq!(crate::tests::codegen_common::run_c_code_exit_status(source), 0);
}

#[test]
fn test_unnamed_bitfield_init_excess_elements() {
    // Unnamed bitfields should be skipped during initialization.
    // {1,2,3,4} should initialize a=1, b=2 and warn about excess elements 3,4.
    let source = r#"
        int main(void) {
            struct {int :1, a, :1, b;} s = {1,2,3,4};
            if (s.a != 1) return 1;
            if (s.b != 2) return 2;
            return 0;
        }
    "#;
    crate::tests::test_utils::run_pass_with_diagnostic_message(source, crate::driver::artifact::CompilePhase::Mir, "excess elements");
}

#[test]
fn test_unnamed_bitfield_init_exact_elements() {
    // Unnamed bitfields should be skipped during initialization.
    // {1,2} should initialize a=1, b=2 with no warnings.
    let source = r#"
        int main(void) {
            struct {int :1, a, :1, b;} s = {1, 2};
            if (s.a != 1) return 1;
            if (s.b != 2) return 2;
            return 0;
        }
    "#;
    assert_eq!(crate::tests::codegen_common::run_c_code_exit_status(source), 0);
}
