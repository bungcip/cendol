use crate::tests::semantic_common::setup_mir;

#[test]
fn test_comma_operator_crash() {
    let src = r#"
        void test(char *p, char *q) {
            p++, q++;
        }

        int main() {
            return 0;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = void
    type %t2 = i8
    type %t3 = ptr<%t2>

    fn main() -> i32
    {

      bb2:
        return const 0
    }

    fn test(%param0: ptr<i8>, %param1: ptr<i8>) -> void
    {
      locals {
        %3: ptr<i8>
        %4: ptr<i8>
        %5: ptr<i8>
        %6: ptr<i8>
      }

      bb1:
        %3 = %param0
        %4 = ptradd(%param0, const 1)
        %param0 = %4
        %5 = %param1
        %6 = ptradd(%param1, const 1)
        %param1 = %6
        return
    }
    ");
}

#[test]
fn test_comma_operator_types() {
    let src = r#"
        void test() {
            int x = 0;
            char *p = 0;
            // (void)x, p  -> type should be char*
            char *q = (x++, p);
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i32
    type %t2 = i8
    type %t3 = ptr<%t2>
    type %t4 = ptr<%t0>

    fn test() -> void
    {
      locals {
        %x: i32
        %p: ptr<i8>
        %q: ptr<i8>
        %4: i32
        %5: i32
      }

      bb1:
        %x = const 0
        %p = cast<ptr<i8>>(const 0)
        %4 = %x
        %5 = %x + const 1
        %x = %5
        %q = %p
        return
    }
    ");
}

#[test]
fn test_comma_operator_loop() {
    let src = r#"
        void loop(char *s, char *f) {
            for (; *f; f++, s++)
                ;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = i8
    type %t2 = ptr<%t1>
    type %t3 = i32

    fn loop(%param0: ptr<i8>, %param1: ptr<i8>) -> void
    {
      locals {
        %3: ptr<i8>
        %4: ptr<i8>
        %5: ptr<i8>
        %6: ptr<i8>
      }

      bb1:
        br bb2

      bb2:
        cond_br deref(%param1), bb3, bb5

      bb3:
        br bb4

      bb4:
        %3 = %param1
        %4 = ptradd(%param1, const 1)
        %param1 = %4
        %5 = %param0
        %6 = ptradd(%param0, const 1)
        %param0 = %6
        br bb2

      bb5:
        return
    }
    ");
}
