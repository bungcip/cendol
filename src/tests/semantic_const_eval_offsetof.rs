use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail, run_pass};

#[test]
fn test_builtin_offsetof_in_const_eval_coverage() {
    let source = "
    struct S {
        int a;
        struct {
            int b;
            int c;
        };
    };
    int arr[__builtin_offsetof(struct S, c)];
    ";
    run_pass(source, CompilePhase::Mir);

    let source2 = "
    struct S { int a; };
    int arr[__builtin_offsetof(struct S, xyz)];
    ";
    run_fail(source2, CompilePhase::Mir);

    let source3 = "
    int x;
    int arr[__builtin_offsetof(int, x)];
    ";
    run_fail(source3, CompilePhase::Mir);

    let source4 = "
    struct S { int a[10]; };
    int arr[__builtin_offsetof(struct S, a[2])];
    ";
    run_pass(source4, CompilePhase::Mir);

    let source5 = "
    struct S { int a; };
    int arr[__builtin_offsetof(struct S, a[2])];
    ";
    run_fail(source5, CompilePhase::Mir);

    let source6 = "
    struct S { int a[10]; };
    int var;
    int arr[__builtin_offsetof(struct S, a[var])];
    ";
    run_fail(source6, CompilePhase::Mir);

    let source7 = "
    struct S { int a; };
    int arr[__builtin_offsetof(struct S, a + 1)];
    ";
    run_fail(source7, CompilePhase::Mir);

    let source8 = "
    int x;
    int arr[__builtin_offsetof(struct S, x)];
    ";
    run_fail(source8, CompilePhase::Mir);

    let source9 = "
    struct S { int a; };
    int arr[__builtin_offsetof(struct S, 123)];
    ";
    run_fail(source9, CompilePhase::Mir);

    let source10 = "
    int arr[__builtin_offsetof(struct DOES_NOT_EXIST, a)];
    ";
    run_fail(source10, CompilePhase::Mir);
}
