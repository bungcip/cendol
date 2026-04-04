use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pipeline;

#[test]
fn test_const_eval_member_access_in_array_size() {
    let src = r#"
        struct S {
            int x[10];
            char y;
        };
        struct T {
            struct S s;
            struct S *p;
        };

        int main() {
            struct S mys;
            struct T myt;
            // The size of these arrays forces constant evaluation of sizeof(member)
            // But sizeof doesn't evaluate the expression, it just asks for its type.
            // Let's force an integer constant expression that requires inferring type.
            // Oh wait, sizeof is not evaluated this way?
            // "without relying on semantic_info. Used during lowering when semantic_info isn't available yet"
            // Wait, how about pointer arithmetic in sizeof?
            // sizeof(mys.x[0] + 1) -> + needs to infer type of mys.x[0] -> IndexAccess(MemberAccess).
            int arr1[sizeof(mys.y + 1)];
            int arr2[sizeof(myt.s.x[0] + 1)];
            int arr3[sizeof(myt.p->x[0] + 1)];
            return 0;
        }
    "#;
    let (_, result) = run_pipeline(src, CompilePhase::Mir);
    assert!(result.is_ok());
}
