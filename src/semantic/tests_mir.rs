use crate::driver::{cli::CompileConfig, compiler::CompilerDriver};

#[cfg(test)]
mod tests {
    use super::*;

    /// helper function to setup compiler driver with given source code
    fn setup_mir(source: &str) -> String {
        // Use string-based MIR dump with no header for cleaner testing
        let mut config = CompileConfig::from_source_code(source.to_string());
        config.dump_mir = false; // Don't dump to file

        let mut driver = CompilerDriver::from_config(config);
        driver.get_mir_dump_string(false).expect("Failed to get MIR dump")
    }

    #[test]
    fn test_if_else_statement() {
        let source = r#"
            int main() {
                int a = 1;
                int b = 2;
                if (a > b) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %a: i32
            %b: i32
            %3: i32
          }

          bb1:
            %a = const 1
            %b = const 2
            %3 = %a > %b
            cond_br %3, bb2, bb3

          bb2:
            return const 1

          bb3:
            return const 2
        }
        ");
    }

    #[test]
    fn test_simple_variable_return() {
        let source = r#"
            int main() {
                int result = 99;
                return result;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
            %result: i32
          }

          bb1:
            %result = const 99
            return %result
        }
        ");
    }

    #[test]
    fn test_global_variable() {
        let source = r#"
            int result = 99;
            int main() {
                return result;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        global @result: i32 = const 99

        fn main() -> i32
        {
          locals {
          }

          bb1:
            return @result
        }
        ");
    }

    #[test]
    fn test_consecutive_labels() {
        let source = r#"
            int main() {
                goto end;
                label1:
                label2:
                label3:
                    return 1;
                end:
                    return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32

        fn main() -> i32
        {
          locals {
          }

          bb1:
            br bb3

          bb2:
            return const 1

          bb3:
            return const 0
        }
        ");
    }

    #[test]
    fn test_struct_type_regression() {
        let source = r#"
            struct { int a; int b; int c; } s = {1, 2, 3};
            int main() {
                if (s.a != 1) return 1;
                return 0;
            }
        "#;

        let mir_dump = setup_mir(source);
        // We want to ensure %t0 is i32 and %t1 is struct using %t0
        // and NOT that %t0 is struct using %t0
        insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = struct anon_struct { a: %t0, b: %t0, c: %t0 }

        global @s: %t1 = const struct_literal { 0: const 1, 1: const 2, 2: const 3 }

        fn main() -> i32
        {
          locals {
            %1: i32
          }

          bb1:
            %1 = @s.field_0 != const 1
            cond_br %1, bb2, bb2

          bb2:
            return const 0
        }
        ");
    }
}
