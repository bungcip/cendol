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

#[test]
fn test_nested_struct_string_brace_elision_init() {
    let source = r#"
    int printf(const char *fmt, ...);
    typedef unsigned char u8;

    struct T {
      u8 s[16];
      u8 a;
    };

    struct U {
      u8 a[5];
      u8 b;
      struct T t;
    };

    int main()
    {
      struct U lu = { {1,2,3,4,5}, 6, "huhu", 43 };
      if (lu.t.s[0] == 'h' && lu.t.s[1] == 'u' && lu.t.s[2] == 'h' && lu.t.s[3] == 'u' && lu.t.s[4] == 0 && lu.t.a == 43) {
          printf("OK");
          return 0;
      }
      printf("FAIL: s[0]=%d, s[1]=%d, s[2]=%d, s[3]=%d, s[4]=%d, t.a=%d\n", 
          lu.t.s[0], lu.t.s[1], lu.t.s[2], lu.t.s[3], lu.t.s[4], lu.t.a);
      return 1;
    }
    "#;

    let output = run_c_code_with_output(source);
    assert_eq!(output, "OK");
}

#[test]
fn test_anonymous_struct_designator_init() {
    let source = r#"
        typedef unsigned char u8;
        int printf(const char *, ...);
        union UV {
            struct { u8 a, b; };
            u8 c[4];
        };
        int main() {
            union UV guv = {{6, 5}};
            union UV guv2 = {{.b = 7, .a = 8}};
            union UV guv3 = {.b = 8, .a = 7};
            printf("guv: %d %d, guv2: %d %d, guv3: %d %d\n", guv.a, guv.b, guv2.a, guv2.b, guv3.a, guv3.b);
            if (guv.a != 6 || guv.b != 5) return 1;
            if (guv2.a != 8 || guv2.b != 7) return 2;
            if (guv3.a != 7 || guv3.b != 8) return 3;
            printf("OK\n");
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output, "guv: 6 5, guv2: 8 7, guv3: 7 8\nOK\n");
}
