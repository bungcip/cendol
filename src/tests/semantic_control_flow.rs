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
    insta::assert_snapshot!(mir, @r#"
    type %t0 = void
    type %t1 = i32
    type %t2 = i8
    type %t3 = ptr<%t2>
    type %t4 = fn(%t3, ...) -> %t1
    type %t5 = [8]%t2
    type %t6 = [8]%t2
    type %t7 = [6]%t2
    type %t8 = [6]%t2

    global @.L.str0: [8]i8 = const "b = %d\n"
    global @.L.str1: [6]i8 = const "done\n"

    fn henry() -> void
    {
      locals {
        %a: i32
        %b: i32
      }

      bb1:
        br bb2

      bb2:
        %b = const 1234
        call printf(cast<ptr<i8>>(const @.L.str0), %b)
        call printf(cast<ptr<i8>>(const @.L.str1))
        return
    }

    extern fn printf(%param0: ptr<i8>, ...) -> i32
    "#);
}

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
    insta::assert_snapshot!(mir_dump, @"
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
