use crate::tests::codegen_common::run_c_code_with_output;

#[test]
fn test_struct_brace_elision_init() {
    let source = r#"
    int printf(const char *fmt, ...);
    typedef unsigned char u8;

    struct S {
        u8 c[2];
    };

    struct U {
        struct S s;
        u8 y;
    };

    struct U u = {4, 5, 6};

    int main()
    {
      // We check if brace elision correctly filled u.s.c[0] and u.s.c[1],
      // and stopped so that u.y got 6.
      if (u.s.c[0] == 4 && u.s.c[1] == 5 && u.y == 6) {
          printf("OK");
          return 0;
      }
      printf("FAIL: c[0]=%d, c[1]=%d, y=%d\n", u.s.c[0], u.s.c[1], u.y);
      return 1;
    }
    "#;

    let output = run_c_code_with_output(source);
    assert_eq!(output, "OK");
}
