use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_func_ptr_global_comparison() {
    let source = r#"
typedef char *(*readline_t)(const char *);

void* get_ptr() {
    return (void*)0x1234;
}

readline_t l_readline_static = 0;

int main() {
    l_readline_static = (readline_t)((void*)get_ptr());

    // Check if comparison works correctly
    if (l_readline_static != 0) {
        return 0; // Success
    }
    return 1; // Failure
}
"#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0, "Function pointer global comparison failed");
}
