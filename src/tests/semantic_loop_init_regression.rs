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
    insta::assert_snapshot!(mir_dump, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %i: i32
        %2: i32
      }

      bb1:
        %i = const 0
        br bb2

      bb2:
        %2 = %i < cast<i32>(const 10)
        cond_br %2, bb3, bb5

      bb3:
        br bb4

      bb4:
        %i = %i + const 1
        br bb2

      bb5:
        return const 0
    }
    ");
}
