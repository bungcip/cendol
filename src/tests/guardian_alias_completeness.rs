use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_association_typeof_incomplete_rejected() {
    run_fail_with_message(
        r#"
        struct S;
        extern struct S s;
        int main() {
            return _Generic(0, typeof(s): 1, default: 2);
        }
        "#,
        "generic association specifies incomplete type",
    );
}

#[test]
fn test_generic_association_typeof_vla_rejected() {
    run_fail_with_message(
        r#"
        void f(int n) {
            int vla[n];
            _Generic(0, typeof(vla): 1, default: 2);
        }
        "#,
        "generic association specifies variably modified type",
    );
}

#[test]
fn test_generic_association_typeof_complete_accepted() {
    run_pass(
        r#"
        struct S { int x; };
        extern struct S s;
        int main() {
            return _Generic(0, typeof(s): 1, default: 2);
        }
        "#,
        CompilePhase::Mir,
    );
}
