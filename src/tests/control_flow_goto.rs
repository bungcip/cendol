use super::semantic_common::setup_mir;

#[test]
fn test_goto_into_block_skips_init() {
    let source = r#"
        int printf(const char *, ...);
        void henry() {
           int a;
           goto inner;
           {
              int b;
        inner:
              b = 1234;
              printf("b = %d\n", b);
           }
           printf("done\n");
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir);
}
