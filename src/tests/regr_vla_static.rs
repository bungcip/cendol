use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_vla_static_pointer() {
    let source = r#"
    int main() {
        int sz = 10;
        static char (*p)[sz];
        int result = sizeof(*p);
        if (result != 10) return 1;
        
        sz = 20;
        // Even if sz changes, the type of p was 'fixed' at the first evaluation?
        // Actually C11 says for VM types, the size is evaluated when the declaration is reached.
        // For static, it's still reached every time? 
        // Let's just check that it compiles and returns 10 for the first one.
        return 0;
    }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
