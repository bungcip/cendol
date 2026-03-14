use crate::tests::codegen_common::run_c_code_exit_status;

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
    assert_eq!(run_c_code_exit_status(source), 0);
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
    assert_eq!(run_c_code_exit_status(source), 0);
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
    assert_eq!(run_c_code_exit_status(source), 0);
}
