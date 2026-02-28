use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_typeof_comma_expr_compile() {
    run_pass(
        "
        void foo(void) {
            const int x = 0;
            __typeof__(((void) 0, x)) y = 5;
        }
        ",
        CompilePhase::Mir,
    );
}

#[test]
fn test_typeof_type_compile() {
    run_pass(
        "
        void foo(void) {
            __typeof__(int) y = 5;
        }
        ",
        CompilePhase::Mir,
    );
}

#[test]
fn test_typeof_function() {
    run_pass(
        "
        int bar(void);
        void foo(void) {
            __typeof__(bar()) y = 5;
        }
        ",
        CompilePhase::Mir,
    );
}

#[test]
fn test_typeof_struct_member() {
    run_pass(
        "
        struct S { float f; };
        void foo(struct S* s) {
            __typeof__(s->f) y = 5.0f;
        }
        ",
        CompilePhase::Mir,
    );
}
