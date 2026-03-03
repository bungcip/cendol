use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_local_alignas() {
    let source = r#"
        int main() {
            _Alignas(16) char a;
            _Alignas(16) char b;
            return ((unsigned long)&a % 16) | ((unsigned long)&b % 16);
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_local_alignas_8() {
    let source = r#"
        int main() {
            _Alignas(8) char a;
            return (unsigned long)&a % 8;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_local_alignas_type() {
    let source = r#"
        struct S { _Alignas(16) char c; };
        int main() {
            struct S s;
            return (unsigned long)&s % 16;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_local_alignas_on_decl() {
    let source = r#"
        int main() {
            _Alignas(16) struct { char c; } s;
            return (unsigned long)&s % 16;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
