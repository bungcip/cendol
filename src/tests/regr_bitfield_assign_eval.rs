use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_bitfield_assign_eval() {
    let source = r#"
        struct S {
            unsigned int a : 1;
        };

        int main() {
            struct S s;
            int res = (s.a = 2);
            if (res != 0) return 1;
            
            s.a = 1;
            res = (s.a = 2);
            if (res != 0) return 2;

            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_bitfield_compound_assign_eval() {
    let source = r#"
        struct S {
            unsigned int a : 1;
        };

        int main() {
            struct S s;
            s.a = 1;
            int res = (s.a += 1); // 1 + 1 = 2, truncated to 1 bit is 0
            if (res != 0) return 1;

            s.a = 0;
            res = (s.a += 1); // 0 + 1 = 1, truncated to 1 bit is 1
            if (res != 1) return 2;

            return 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
