use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_bitfield_builder_coverage() {
    // This test ensures that the ParsedDeclarator::BitField variant is correctly
    // handled by build_parsed_declarator, even though the bit width expression
    // is not used for type construction (it's handled in struct member parsing).
    run_pass(
        r#"
        struct S {
            int x : 3;
            unsigned int y : 5;
        };
        int main() {
            struct S s;
            s.x = 1;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_abstract_declarator_builder_coverage() {
    // This test ensures that the ParsedDeclarator::Abstract variant is correctly
    // handled by build_parsed_declarator.
    // Abstract declarators appear in type names (casts, sizeof, alignof).
    run_pass(
        r#"
        int main() {
            // sizeof(type-name) uses abstract declarators
            int sz1 = sizeof(int *);           // Abstract pointer
            int sz2 = sizeof(int [5]);         // Abstract array
            int sz3 = sizeof(int (*)(void));   // Abstract function pointer

            // Casts also use abstract declarators
            int x = (int)3.14;

            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
