use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_types_compatible_unresolved_typeof() {
    run_pass(
        "
        int main() {
            int a = 1;
            int x = __builtin_types_compatible_p(typeof(({ a; })), typeof(1));
            return x;
        }
        ",
        CompilePhase::Mir,
    );
}

#[test]
fn test_negative_array_size_with_builtin_types_compatible() {
    crate::tests::test_utils::run_fail_with_message(
        r#"
        #define Py_BUILD_ASSERT_EXPR(cond) (sizeof(char [1 - 2*!(cond)]) - 1)
        #define Py_ARRAY_LENGTH(array) \
            (sizeof(array) / sizeof((array)[0]) + \
             Py_BUILD_ASSERT_EXPR(!__builtin_types_compatible_p(__typeof__(array), __typeof__(&(array)[0]))))

        int main() {
            int *arr;
            return Py_ARRAY_LENGTH(arr);
        }
        "#,
        "size of array is negative",
    );
}
