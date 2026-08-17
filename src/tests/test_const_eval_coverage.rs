use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::*;

#[test]
fn test_const_eval_coverage() {
    let source = "
    void f() {
        int arr1[__builtin_choose_expr(1, 10, 20)];
        int arr2[__builtin_choose_expr(0, 10, 20)];
        int arr3[__builtin_types_compatible_p(int, int) ? 1 : 2];
        struct S { int a; };
        int arr4[sizeof((struct S){0}.a)];
        int arr5[sizeof(__builtin_choose_expr(1, 10, 20))];
        int arr6[sizeof(__builtin_offsetof(struct S, a))];
        int arr7[sizeof((int *)0)];
        int arr8[sizeof(+(int *)0)];
        int arr9[sizeof((struct S){0})];
        int arr10[sizeof((struct S *)0)];
        int arr11[sizeof(1 ? (struct S *)0 : (struct S *)0)];
        int arr12[sizeof(1 ? (int *)0 : (int *)0)];
        int arr13[sizeof(1 ? (void *)0 : (int *)0)];
        int arr14[sizeof(1 ? (int *)0 : (void *)0)];
        int arr15[sizeof(1 ? (void *)0 : (void *)0)];

        int a = 1;
        int arr23[sizeof(1 ? a : a)];

        int arr26[sizeof(_Generic(1, int: 1, float: 2))];
        int arr27[sizeof(_Generic(1, float: 2, default: 3))];

        int arr28[sizeof(\"abc\")];
        int arr29[sizeof(u8\"abc\")];
        int arr30[sizeof(u\"abc\")];
        int arr31[sizeof(U\"abc\")];
        int arr32[sizeof(L\"abc\")];
    }

    struct SomeStruct { int member; };
    struct S {
        struct SomeStruct s;
    };

    void g() {
        int arr33[sizeof((struct S){0}.s.member)];
        int arr34[sizeof(((struct S*)0)->s.member)];
        int arr35[sizeof(*((struct S*)0))];
        int arr36[sizeof( (int[2]){1, 2}[0] )];
        int arr37[sizeof( !1.0 )];
        int arr38[sizeof( +1.0 )];
        int arr39[sizeof( -1.0 )];
        int arr40[sizeof( 1.0 + 2.0 )];
        int arr41[sizeof( (int)1.0 )];
    }
    ";
    run_pass(source, CompilePhase::SemanticLowering);
}
