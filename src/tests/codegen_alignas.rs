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

#[test]
fn test_local_alignas_large() {
    let source = r#"
        int main() {
            _Alignas(1024) char a;
            return (unsigned long)&a % 1024;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_vla_alignas_large() {
    let source = r#"
        int main(int argc, char** argv) {
            _Alignas(2048) char vla[argc];
            return (unsigned long)&vla % 2048;
        }
    "#;
    // argc is at least 1 when running tests normally, but let's be sure.
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_vla_alignas_large_argc() {
    let source = r#"
        int main(int argc, char** argv) {
            int n = argc + 5;
            _Alignas(1024) int vla[n];
            for (int i = 0; i < n; i++) vla[i] = i;
            int res = (unsigned long)&vla % 1024;
            for (int i = 0; i < n; i++) res |= (vla[i] != i);
            return res;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
