use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_store_truncation_overflow_regression() {
    let source = r#"
typedef unsigned char u8;

int main() {
    // Layout: field at 0. padding/sentinel at 1..7.
    // If we increment field, and it stores 4 bytes, it will overwrite 1,2,3.

    struct {
        u8 val;
        u8 pad[7];
    } s;

    // Initialize
    s.val = 10;
    for(int i=0; i<7; i++) s.pad[i] = 0xAA;

    // Increment (s.val++ -> Assign(s.val, Add(s.val, 1)))
    // If store size is not truncated to u8, it writes 4 bytes.
    s.val++;

    if (s.val != 11) return 1;

    for(int i=0; i<3; i++) {
        if (s.pad[i] != 0xAA) {
            return 2;
        }
    }

    return 0;
}
"#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0, "Memory corruption detected in store truncation");
}
