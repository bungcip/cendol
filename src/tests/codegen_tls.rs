use crate::tests::codegen_common::{run_c_code_exit_status, setup_cranelift};

#[test]
fn test_thread_local_codegen() {
    let source = r#"
        _Thread_local int tls_var = 42;
        int main() {
            return tls_var;
        }
    "#;
    let clif_ir = setup_cranelift(source);
    insta::assert_snapshot!(clif_ir, @"
    ; Function: main
    function u0:0() -> i32 system_v {
        gv0 = symbol colocated tls userextname0

    block0:
        v0 = tls_value.i64 gv0
        v1 = load.i32 v0
        return v1
    }
    ");
}

#[test]
fn test_thread_local_runtime() {
    let source = r#"
        _Thread_local int tls_var = 42;
        int main() {
            tls_var += 10;
            return tls_var;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 52);
}
