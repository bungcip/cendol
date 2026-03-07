use crate::tests::codegen_common::run_c_code_with_output;

#[test]
fn test_struct_init_in_array_regression() {
    let source = r#"
    int printf(const char *fmt, ...);
    struct Inner {
      long i;
    };
    struct Outer {
      struct Inner b;
      int j;
    };
    int main(void) {
        struct Inner v = {3};
        struct Outer s[] = {v, 6, 7};

        printf("%ld %d %ld %d", s[0].b.i, s[0].j, s[1].b.i, s[1].j);
        return 0;
    }
    "#;

    let output = run_c_code_with_output(source);
    assert_eq!(output, "3 6 7 0");
}
