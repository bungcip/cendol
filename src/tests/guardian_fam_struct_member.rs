use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_struct_can_contain_fam_struct() {
    // C11 allows structs to contain structs with flexible array members (FAM).
    // It's a GNU extension if they're not at the end, but the compiler should just emit a warning
    // and successfully compile the code.
    run_pass(
        r#"
        struct Inner {
            int count;
            char flex[];
        };

        struct Outer {
            void* ptr;
            struct Inner inner;
        };

        struct Outer2 {
            struct Inner inner;
            void* ptr;
        };

        int main() {
            return 0;
        }
        "#,
        CompilePhase::SemanticLowering,
    );
}
