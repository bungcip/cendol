use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_typeof_unqual_type() {
    let source = r#"
        int main() {
            const int a = 1;
            typeof_unqual(const int) b = a;
            b = 2; // Should be allowed, b is int not const int

            const int * const p1 = &a;
            typeof_unqual(const int * const) p2 = p1;
            p2 = (int *)0; // Allowed, p2 should be const int *
            // *p2 = 3; // Should NOT be allowed as it points to const int
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_typeof_unqual_expr() {
    let source = r#"
        int main() {
            const int a = 1;
            typeof_unqual(a) b = a;
            b = 2; // Allowed

            const int * const p1 = &a;
            typeof_unqual(p1) p2 = p1;
            p2 = (int *)0; // Allowed
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_typeof_unqual_assignment_fail() {
    let source = r#"
        int main() {
            const int a = 1;
            typeof_unqual(const int) b = a;
            b = 2;

            const int c = 1;
            typeof(c) d = c;
            d = 2; // Should fail, d is const int
        }
    "#;
    run_fail_with_message(source, "read-only");
}

#[test]
fn test_typeof_unqual_complex_pointer() {
    let source = r#"
        int main() {
            int * const volatile p1 = 0;
            typeof_unqual(p1) p2 = 0;
            p2 = (int *)1; // Should be allowed, p2 is int *
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_typeof_unqual_vla() {
    let source = r#"
        void foo(int n) {
            const int a[n];
            typeof_unqual(a) b; // b should be int[n]
            // We can't easily check for non-constness of VLA elements in MIR
            // but at least it should pass semantic analysis.
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}
