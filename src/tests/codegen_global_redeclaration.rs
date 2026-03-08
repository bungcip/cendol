use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_global_extern_then_definition() {
    let code = r#"
        extern int x;
        int x = 42;
        int main() {
            if (x == 42) return 0;
            return 1;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_global_extern_then_tentative() {
    let code = r#"
        extern int x;
        int x;
        int main() {
            if (x == 0) return 0;
            return 1;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_global_tentative_then_extern() {
    let code = r#"
        int x;
        extern int x;
        int main() {
            x = 10;
            if (x == 10) return 0;
            return 1;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_global_static_then_extern() {
    let code = r#"
        static int x = 5;
        extern int x;
        int main() {
            if (x == 5) return 0;
            return 1;
        }
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}

#[test]
fn test_global_extern_then_static() {
    let code = r#"
        static int x;
        int main() {
            extern int x;
            x = 7;
            if (x == 7) return 0;
            return 1;
        }
        static int x = 7;
    "#;
    assert_eq!(run_c_code_exit_status(code), 0);
}
