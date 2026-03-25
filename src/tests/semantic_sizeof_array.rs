use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_sizeof_array_deref_in_enum() {
    run_pass(
        r#"
        int main() {
            const char in[] = "hello";
            enum { in_sz = sizeof in / sizeof *in };
            return in_sz;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_sizeof_array_deref_global() {
    run_pass(
        r#"
        const char g_in[] = "world";
        enum { g_in_sz = sizeof g_in / sizeof *g_in };
        int main() {
            return g_in_sz;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_sizeof_multi_dim_array_deref() {
    run_pass(
        r#"
        int main() {
            int a[2][3];
            enum { 
                rows = sizeof a / sizeof *a,
                cols = sizeof *a / sizeof **a 
            };
            return rows + cols;
        }
        "#,
        CompilePhase::Mir,
    );
}
