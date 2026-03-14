use crate::tests::codegen_common::run_c_code_exit_status;

#[test]
fn test_vla_sizeof_parameters() {
    let source = r#"
    int fn(int sz, char (*arr)[sz]) {
        return sizeof *arr;
    }

    int main() {
        int sz = 10;
        char a[sz];
        if (fn(sz, &a) != 10) return 1;
        
        sz = 20;
        char b[sz];
        if (fn(sz, &b) != 20) return 1;
        
        return 0;
    }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_vla_scoping_advanced() {
    let source = r#"
    int f(int n, int m, int a[n][m]) {
        return sizeof a[0];
    }

    int main() {
        int m = 5;
        int n = 3;
        int a[3][5];
        if (f(n, m, a) != 5 * sizeof(int)) return 1;
        return 0;
    }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}
