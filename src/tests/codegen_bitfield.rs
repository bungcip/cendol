use crate::tests::codegen_common::run_c_code_exit_status;

// Test for enum bit-field with all non-negative values.
// This tests that enums with all positive values are correctly zero-extended
// (instead of sign-extended) when stored in bit-fields.
#[test]
fn test_enum_bitfield_all_positive() {
    let source = r#"
        enum tree_code {
          SOME_CODE = 148,
          LAST_AND_UNUSED_TREE_CODE
        };
        struct tree_common {
          enum tree_code code : 8;
        };
        int main() {
            struct tree_common t;
            t.code = SOME_CODE;
            // If sign-extended, 148 (0x94) would become -108
            // If zero-extended, it stays 148
            if (t.code != 148) return 1;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

// Test for enum bit-field with negative values (should be signed)
#[test]
fn test_enum_bitfield_with_negative() {
    let source = r#"
        enum sign_test {
          NEG_VALUE = -1,
          POS_VALUE = 1
        };
        struct test {
          enum sign_test val : 8;
        };
        int main() {
            struct test t;
            t.val = NEG_VALUE;
            // Should be sign-extended to -1
            if (t.val != -1) return 1;
            t.val = POS_VALUE;
            if (t.val != 1) return 2;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_bitfield_global_init() {
    let source = r#"
        struct {
            unsigned f1 : 1;
            unsigned f2 : 1;
        } g = {0, 1};
        int main() {
            return g.f2;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_bitfield_local_init() {
    let source = r#"
        int main() {
            struct {
                unsigned f1 : 1;
                unsigned f2 : 1;
            } s = {0, 1};
            return s.f2;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_bitfield_assignment() {
    let source = r#"
        struct {
            unsigned f1 : 1;
            unsigned f2 : 1;
        } g;
        int main() {
            g.f1 = 1;
            g.f2 = 0;
            if (g.f1 != 1) return 1;
            if (g.f2 != 0) return 2;
            g.f1 = 0;
            g.f2 = 1;
            if (g.f1 != 0) return 3;
            if (g.f2 != 1) return 4;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_bitfield_packing_overlap() {
    let source = r#"
        struct {
            unsigned f1 : 1;
            unsigned f2 : 7;
            unsigned f3 : 8;
        } s = {1, 0x7F, 0xAA};
        int main() {
            if (s.f1 != 1) return 1;
            if (s.f2 != 127) return 2;
            if (s.f3 != 170) return 3;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_bitfield_mixed_types() {
    let source = r#"
        struct {
            char c;
            unsigned f1 : 1;
            unsigned f2 : 1;
            int i;
        } s = {'A', 1, 0, 12345};
        int main() {
            if (s.c != 'A') return 1;
            if (s.f1 != 1) return 2;
            if (s.f2 != 0) return 3;
            if (s.i != 12345) return 4;
            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
