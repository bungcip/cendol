use super::semantic_common::setup_mir;

#[test]
fn test_struct_copy_init() {
    let source = r#"
        struct Wrap {
            void *func;
        };
        int global;
        void inc_global (void) { global++; }
        struct Wrap global_wrap[] = {
            ((struct Wrap) {inc_global}),
            inc_global,
        };
        int main() { return 0; }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}
