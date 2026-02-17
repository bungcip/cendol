use super::semantic_common::setup_mir;

#[test]
fn test_case_range_coverage() {
    let source = r#"
        int foo(int x) {
            switch (x) {
                case 1 ... 5:
                    return 10;
                case 10 ... 20:
                    return 20;
                default:
                    return 0;
            }
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r###"
    type %t0 = i32

    fn foo(%param0: i32) -> i32
    {

      bb1:
        br bb3

      bb2:
        unreachable

      bb3:
        return const 0

      bb4:
        br bb3
    }
    "###);
}
