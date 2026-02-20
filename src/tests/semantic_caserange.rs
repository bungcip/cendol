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
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = bool

    fn foo(%param0: i32) -> i32
    {
      locals {
        %2: bool
        %3: bool
        %4: bool
        %5: bool
        %6: bool
        %7: bool
      }

      bb1:
        %2 = %param0 >= const 1
        %3 = %param0 <= const 5
        %4 = %2 & %3
        cond_br %4, bb3, bb6

      bb2:
        unreachable

      bb3:
        return const 10

      bb4:
        return const 20

      bb5:
        return const 0

      bb6:
        %5 = %param0 >= const 10
        %6 = %param0 <= const 20
        %7 = %5 & %6
        cond_br %7, bb4, bb7

      bb7:
        br bb5

      bb8:
        br bb3
    }
    ");
}
