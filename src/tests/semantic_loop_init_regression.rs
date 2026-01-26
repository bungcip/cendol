use super::semantic_common::setup_mir;

#[test]
fn test_for_loop_init_assignment() {
    let source = r#"
        int main() {
            int i;
            for (i = 0; i < 10; i++) {
                // empty body
            }
            return 0;
        }
    "#;

    let mir_dump = setup_mir(source);
    insta::assert_snapshot!(mir_dump);
}
