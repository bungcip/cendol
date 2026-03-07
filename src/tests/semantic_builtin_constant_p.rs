use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtin_constant_p() {
    run_pass(
        r#"
            int main() {
                int x = 5;
                const int y = 10;

                _Static_assert(__builtin_constant_p(10) == 1, "10 is constant");
                _Static_assert(__builtin_constant_p(x) == 0, "x is not constant");
                _Static_assert(__builtin_constant_p(y) == 0, "y is not constant in C");
                _Static_assert(__builtin_constant_p(10 + 20) == 1, "10+20 is constant");

                int arr[__builtin_constant_p(10) ? 10 : -1]; // Valid array size if true
                return 0;
            }
        "#,
        CompilePhase::Mir,
    );
}
