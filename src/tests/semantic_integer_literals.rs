use super::semantic_common::setup_mir;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_long_long_literal_suffix() {
        let source = r#"
            int main() {
                long long a = -2147483648LL;
                long long b = 2147483648LL;
                // Test constant without suffix that fits in unsigned int but not signed int (C11 rules)
                // This is the problematic case for non-suffix literals too
                long long c = 2147483648;
                return 0;
            }
        "#;
        let mir = setup_mir(source);
        insta::assert_snapshot!(mir, @r"
        type %t0 = i32
        type %t1 = i64

        fn main() -> i32
        {
          locals {
            %a: i64
            %b: i64
            %c: i64
          }

          bb1:
            %a = const -2147483648
            %b = const 2147483648
            %c = const 2147483648
            return const 0
        }
        ");
    }
}
