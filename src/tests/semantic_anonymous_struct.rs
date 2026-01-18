use super::semantic_common::{run_fail, run_pass};
use crate::driver::artifact::CompilePhase;

#[test]
fn test_anonymous_struct_member_access() {
    run_pass(
        r#"
        struct outer {
            int a;
            struct {
                int b;
                int c;
            };
            int d;
        };

        int main() {
            struct outer s;
            s.a = 1;
            s.b = 2;
            s.c = 3;
            s.d = 4;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_anonymous_struct_name_conflict() {
    run_fail(
        r#"
        struct outer {
            int a;
            struct {
                int b;
                int c;
            };
            int b;
        };
    "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_anonymous_struct_initialization() {
    run_pass(
        r#"
        struct outer {
            int a;
            struct {
                int b;
                int c;
            };
            int d;
        };

        int main() {
            struct outer s = {1, 2, 3, 4};
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_anonymous_union_name_conflict() {
    run_fail(
        r#"
        struct outer {
            int a;
            union {
                int b;
                float c;
            };
            int c;
        };
    "#,
        CompilePhase::SemanticLowering,
    );
}

#[test]
fn test_anonymous_union_member_access() {
    run_pass(
        r#"
        struct outer {
            int a;
            union {
                int b;
                float c;
            };
            int d;
        };

        int main() {
            struct outer s;
            s.a = 1;
            s.b = 2;
            s.c = 3.0f;
            s.d = 4;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}
