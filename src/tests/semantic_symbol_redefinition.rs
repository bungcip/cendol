use super::semantic_common::setup_mir;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function_redefinition_with_prototype() {
        let source = r#"
            int x;
            int x = 3;
            int x;

            int main();

            void *
            foo()
            {
                return &main;
            }

            int
            main()
            {
                if (x != 3)
                    return 0;

                x = 0;
                return x;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = void
        type %t2 = ptr<%t1>
        type %t3 = fn() -> %t0
        type %t4 = ptr<%t3>

        global @x: i32 = const 3

        fn main() -> i32
        {
          locals {
            %1: i32
          }

          bb2:
            %1 = @x != cast<i32>(const 3)
            cond_br %1, bb3, bb4

          bb3:
            return const 0

          bb4:
            br bb5

          bb5:
            @x = const 0
            return @x
        }

        fn foo() -> ptr<void>
        {

          bb1:
            return cast<ptr<void>>(const main)
        }
        ");
    }
}
