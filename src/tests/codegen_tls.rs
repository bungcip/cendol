use crate::tests::semantic_common::setup_mir;

#[test]
fn test_thread_local_storage_mir() {
    let source = r#"
        _Thread_local int tls_var = 42;
        int main() {
            return tls_var;
        }
    "#;
    let mir_dump = setup_mir(source);

    // Check if tls_var is declared as a TLS global in MIR
    insta::assert_snapshot!(mir_dump, @"
    type %t0 = i32

    global @tls_var: i32 (tls) = const 42

    fn main() -> i32
    {

      bb1:
        return @tls_var
    }
    ");
}

#[test]
fn test_thread_local_extern_mir() {
    let source = r#"
        extern _Thread_local int tls_extern;
        int main() {
            return tls_extern;
        }
    "#;
    let mir_dump = setup_mir(source);
    insta::assert_snapshot!(mir_dump, @"
    type %t0 = i32

    global @tls_extern: i32 (tls)

    fn main() -> i32
    {

      bb1:
        return @tls_extern
    }
    ");
}
